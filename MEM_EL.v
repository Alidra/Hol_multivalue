Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_EL_term_abbrevs.
Require Import LT_SUC_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1097080_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89994_spec.
Lemma lem1160418 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1160419 {A : Type'} : term1 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1160420 {A : Type'} (h : A) : term2 A h.
Proof. exact (@lem1160419 A h). Qed.
Lemma lem1160421 {A : Type'} (h : A) : (term2 A h) = (term3 A h).
Proof. exact (eq_refl (term2 A h)). Qed.
Lemma lem1160422 {A : Type'} (h : A) : term3 A h.
Proof. exact (EQ_MP (@lem1160421 A h) (@lem1160420 A h)). Qed.
Lemma lem1160423 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem1160422 A h t). Qed.
Lemma lem1160424 {A : Type'} (h : A) (t : list A) : (term4 A h t) = ((term5 A h t) = (term6 A t)).
Proof. exact (eq_refl (term4 A h t)). Qed.
Lemma lem1160427 (m : nat) : term7 m.
Proof. exact (@lem1160418 m). Qed.
Lemma lem1160428 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1160433 {A : Type'} (P : type1143 A) : term9 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1160434 {_27264 : Type'} (P : type1143 _27264) : term9 _27264 P.
Proof. exact (@lem1160433 _27264 P). Qed.
Lemma lem1160435 {_27264 : Type'} : term10 _27264.
Proof. exact (@lem1160434 _27264 (term11 _27264)). Qed.
Lemma lem1160436 {_27264 : Type'} : (term12 _27264) = (term13 _27264).
Proof. exact (eq_refl (term12 _27264)). Qed.
Lemma lem1160437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1160438 {_27264 : Type'} : (term14 _27264) = (term15 _27264).
Proof. exact (MK_COMB (@lem1160437) (@lem1160436 _27264)). Qed.
Lemma lem1160439 {_27264 : Type'} (t : list _27264) : (term16 _27264 t) = (term17 _27264 t).
Proof. exact (eq_refl (term16 _27264 t)). Qed.
Lemma lem1160440 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160441 {_27264 : Type'} (t : list _27264) : (term18 _27264 t) = (term19 _27264 t).
Proof. exact (MK_COMB (@lem1160440) (@lem1160439 _27264 t)). Qed.
Lemma lem1160442 {_27264 : Type'} (h : _27264) (t : list _27264) : (term20 _27264 h t) = (term21 _27264 h t).
Proof. exact (eq_refl (term20 _27264 h t)). Qed.
Lemma lem1160443 {_27264 : Type'} (h : _27264) (t : list _27264) : (term22 _27264 h t) = (term23 _27264 h t).
Proof. exact (MK_COMB (@lem1160441 _27264 t) (@lem1160442 _27264 h t)). Qed.
Lemma lem1160444 {_27264 : Type'} (h : _27264) : (term24 _27264 h) = (term25 _27264 h).
Proof. exact (fun_ext (fun t : list _27264 => @lem1160443 _27264 h t)). Qed.
Lemma lem1160445 {_27264 : Type'} : (@all (list _27264)) = (@all (list _27264)).
Proof. exact (eq_refl (@all (list _27264))). Qed.
Lemma lem1160446 {_27264 : Type'} (h : _27264) : (term26 _27264 h) = (term27 _27264 h).
Proof. exact (MK_COMB (@lem1160445 _27264) (@lem1160444 _27264 h)). Qed.
Lemma lem1160447 {_27264 : Type'} : (term28 _27264) = (term29 _27264).
Proof. exact (fun_ext (fun h : _27264 => @lem1160446 _27264 h)). Qed.
Lemma lem1160448 {_27264 : Type'} : (@all _27264) = (@all _27264).
Proof. exact (eq_refl (@all _27264)). Qed.
Lemma lem1160449 {_27264 : Type'} : (term30 _27264) = (term31 _27264).
Proof. exact (MK_COMB (@lem1160448 _27264) (@lem1160447 _27264)). Qed.
Lemma lem1160450 {_27264 : Type'} : (term32 _27264) = (term33 _27264).
Proof. exact (MK_COMB (@lem1160438 _27264) (@lem1160449 _27264)). Qed.
Lemma lem1160451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160452 {_27264 : Type'} : (term34 _27264) = (term35 _27264).
Proof. exact (MK_COMB (@lem1160451) (@lem1160450 _27264)). Qed.
Lemma lem1160453 {_27264 : Type'} (l : list _27264) : (term16 _27264 l) = (term17 _27264 l).
Proof. exact (eq_refl (term16 _27264 l)). Qed.
Lemma lem1160454 {_27264 : Type'} : (term36 _27264) = (term11 _27264).
Proof. exact (fun_ext (fun l : list _27264 => @lem1160453 _27264 l)). Qed.
Lemma lem1160455 {_27264 : Type'} : (@all (list _27264)) = (@all (list _27264)).
Proof. exact (eq_refl (@all (list _27264))). Qed.
Lemma lem1160456 {_27264 : Type'} : (term37 _27264) = (term38 _27264).
Proof. exact (MK_COMB (@lem1160455 _27264) (@lem1160454 _27264)). Qed.
Lemma lem1160457 {_27264 : Type'} : (term10 _27264) = (term39 _27264).
Proof. exact (MK_COMB (@lem1160452 _27264) (@lem1160456 _27264)). Qed.
Lemma lem1160458 {_27264 : Type'} : term39 _27264.
Proof. exact (EQ_MP (@lem1160457 _27264) (@lem1160435 _27264)). Qed.
Lemma lem1160459 {_27264 : Type'} (t : list _27264) (h1 : term17 _27264 t) : term17 _27264 t.
Proof. exact (h1). Qed.
Lemma lem1160467 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1160468 {_27264 : Type'} : (@List.length _27264 (@nil _27264)) = (NUMERAL 0).
Proof. exact (@lem1160467 _27264). Qed.
Lemma lem1160469 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem1160470 {_27264 : Type'} (n : nat) : (term40 _27264 n) = (term8 n).
Proof. exact (MK_COMB (@lem1160469 n) (@lem1160468 _27264)). Qed.
Lemma lem1160472 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem1160428 m) (@lem1160427 m)). Qed.
Lemma lem1160473 (n : nat) : (term8 n) = False.
Proof. exact (@lem1160472 n). Qed.
Lemma lem1160474 {_27264 : Type'} (n : nat) : (term40 _27264 n) = False.
Proof. exact (TRANS (@lem1160470 _27264 n) (@lem1160473 n)). Qed.
Lemma lem1160475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160476 {_27264 : Type'} (n : nat) : (term41 _27264 n) = (imp False).
Proof. exact (MK_COMB (@lem1160475) (@lem1160474 _27264 n)). Qed.
Lemma lem1160478 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1160479 {_27264 : Type'} (x : _27264) : (@List.In _27264 x (@nil _27264)) = False.
Proof. exact (@lem1160478 _27264 x). Qed.
Lemma lem1160480 {_27264 : Type'} (n : nat) : (term42 _27264 n) = False.
Proof. exact (@lem1160479 _27264 (@EL _27264 n (@nil _27264))). Qed.
Lemma lem1160481 {_27264 : Type'} (n : nat) : (term43 _27264 n) = (False -> False).
Proof. exact (MK_COMB (@lem1160476 _27264 n) (@lem1160480 _27264 n)). Qed.
Lemma lem1160483 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1160484 : (False -> False) = True.
Proof. exact (@lem1160483 False). Qed.
Lemma lem1160485 {_27264 : Type'} (n : nat) : (term43 _27264 n) = True.
Proof. exact (TRANS (@lem1160481 _27264 n) (@lem1160484)). Qed.
Lemma lem1160486 {_27264 : Type'} : (term44 _27264) = term45.
Proof. exact (fun_ext (fun n : nat => @lem1160485 _27264 n)). Qed.
Lemma lem1160487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1160488 {_27264 : Type'} : (term13 _27264) = term46.
Proof. exact (MK_COMB (@lem1160487) (@lem1160486 _27264)). Qed.
Lemma lem1160490 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1160491 (t : Prop) : (term48 t) = t.
Proof. exact (@lem1160490 nat t). Qed.
Lemma lem1160492 : term46 = True.
Proof. exact (@lem1160491 True). Qed.
Lemma lem1160493 {_27264 : Type'} : (term13 _27264) = True.
Proof. exact (TRANS (@lem1160488 _27264) (@lem1160492)). Qed.
Lemma lem1160494 {_27264 : Type'} : True = (term13 _27264).
Proof. exact (SYM (@lem1160493 _27264)). Qed.
Lemma lem1160495 {_27264 : Type'} : term13 _27264.
Proof. exact (EQ_MP (@lem1160494 _27264) (@lem0)). Qed.
Lemma lem1160503 {A : Type'} (h : A) (t : list A) : (term5 A h t) = (term6 A t).
Proof. exact (EQ_MP (@lem1160424 A h t) (@lem1160423 A h t)). Qed.
Lemma lem1160504 {_27264 : Type'} (h : _27264) (t : list _27264) : (term5 _27264 h t) = (term6 _27264 t).
Proof. exact (@lem1160503 _27264 h t). Qed.
Lemma lem1160505 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem1160506 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term49 _27264 n h t) = (term50 _27264 n t).
Proof. exact (MK_COMB (@lem1160505 n) (@lem1160504 _27264 h t)). Qed.
Lemma lem1160507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160508 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term51 _27264 n h t) = (term52 _27264 n t).
Proof. exact (MK_COMB (@lem1160507) (@lem1160506 _27264 h n t)). Qed.
Lemma lem1160510 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term53 _25376 x h t) = (term54 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1160511 {_27264 : Type'} (h : _27264) (x : _27264) (t : list _27264) : (term53 _27264 x h t) = (term54 _27264 h x t).
Proof. exact (@lem1160510 _27264 h x t). Qed.
Lemma lem1160512 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term55 _27264 n h t) = (term56 _27264 n h t).
Proof. exact (@lem1160511 _27264 h (term57 _27264 n h t) t). Qed.
Lemma lem1160517 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term58 _27264 n h t) = (term59 _27264 n h t).
Proof. exact (MK_COMB (@lem1160508 _27264 h n t) (@lem1160512 _27264 n h t)). Qed.
Lemma lem1160520 {_27264 : Type'} (h : _27264) (t : list _27264) : (term60 _27264 h t) = (term61 _27264 h t).
Proof. exact (fun_ext (fun n : nat => @lem1160517 _27264 n h t)). Qed.
Lemma lem1160521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1160522 {_27264 : Type'} (h : _27264) (t : list _27264) : (term21 _27264 h t) = (term62 _27264 h t).
Proof. exact (MK_COMB (@lem1160521) (@lem1160520 _27264 h t)). Qed.
Lemma lem1160527 {_27264 : Type'} (h : _27264) (t : list _27264) : (term62 _27264 h t) = (term21 _27264 h t).
Proof. exact (SYM (@lem1160522 _27264 h t)). Qed.
Lemma lem1160529 (P : nat -> Prop) : term63 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1160530 {_27264 : Type'} (h : _27264) (t : list _27264) : term64 _27264 h t.
Proof. exact (@lem1160529 (term61 _27264 h t)). Qed.
Lemma lem1160531 {_27264 : Type'} (h : _27264) (t : list _27264) : (term65 _27264 h t) = (term66 _27264 h t).
Proof. exact (eq_refl (term65 _27264 h t)). Qed.
Lemma lem1160532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1160533 {_27264 : Type'} (h : _27264) (t : list _27264) : (term67 _27264 h t) = (term68 _27264 h t).
Proof. exact (MK_COMB (@lem1160532) (@lem1160531 _27264 h t)). Qed.
Lemma lem1160534 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term69 _27264 h t n) = (term59 _27264 n h t).
Proof. exact (eq_refl (term69 _27264 h t n)). Qed.
Lemma lem1160535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160536 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term70 _27264 h t n) = (term71 _27264 n h t).
Proof. exact (MK_COMB (@lem1160535) (@lem1160534 _27264 n h t)). Qed.
Lemma lem1160537 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term72 _27264 h t n) = (term73 _27264 n h t).
Proof. exact (eq_refl (term72 _27264 h t n)). Qed.
Lemma lem1160538 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term74 _27264 h t n) = (term75 _27264 n h t).
Proof. exact (MK_COMB (@lem1160536 _27264 n h t) (@lem1160537 _27264 n h t)). Qed.
Lemma lem1160539 {_27264 : Type'} (h : _27264) (t : list _27264) : (term76 _27264 h t) = (term77 _27264 h t).
Proof. exact (fun_ext (fun n : nat => @lem1160538 _27264 n h t)). Qed.
Lemma lem1160540 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1160541 {_27264 : Type'} (h : _27264) (t : list _27264) : (term78 _27264 h t) = (term79 _27264 h t).
Proof. exact (MK_COMB (@lem1160540) (@lem1160539 _27264 h t)). Qed.
Lemma lem1160542 {_27264 : Type'} (h : _27264) (t : list _27264) : (term80 _27264 h t) = (term81 _27264 h t).
Proof. exact (MK_COMB (@lem1160533 _27264 h t) (@lem1160541 _27264 h t)). Qed.
Lemma lem1160543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160544 {_27264 : Type'} (h : _27264) (t : list _27264) : (term82 _27264 h t) = (term83 _27264 h t).
Proof. exact (MK_COMB (@lem1160543) (@lem1160542 _27264 h t)). Qed.
Lemma lem1160545 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term69 _27264 h t n) = (term59 _27264 n h t).
Proof. exact (eq_refl (term69 _27264 h t n)). Qed.
Lemma lem1160546 {_27264 : Type'} (h : _27264) (t : list _27264) : (term84 _27264 h t) = (term61 _27264 h t).
Proof. exact (fun_ext (fun n : nat => @lem1160545 _27264 n h t)). Qed.
Lemma lem1160547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1160548 {_27264 : Type'} (h : _27264) (t : list _27264) : (term85 _27264 h t) = (term62 _27264 h t).
Proof. exact (MK_COMB (@lem1160547) (@lem1160546 _27264 h t)). Qed.
Lemma lem1160549 {_27264 : Type'} (h : _27264) (t : list _27264) : (term64 _27264 h t) = (term86 _27264 h t).
Proof. exact (MK_COMB (@lem1160544 _27264 h t) (@lem1160548 _27264 h t)). Qed.
Lemma lem1160550 {_27264 : Type'} (h : _27264) (t : list _27264) : term86 _27264 h t.
Proof. exact (EQ_MP (@lem1160549 _27264 h t) (@lem1160530 _27264 h t)). Qed.
Lemma lem1160575 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term87 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1160576 (p : Prop) (q : Prop) (p' : Prop) : term88 p q p'.
Proof. exact (fun q' : Prop => @lem1160575 p q p' q'). Qed.
Lemma lem1160577 (p : Prop) (q : Prop) : term89 p q.
Proof. exact (fun p' : Prop => @lem1160576 p q p'). Qed.
Lemma lem1160578 {_27264 : Type'} (h : _27264) (t : list _27264) : term90 _27264 h t.
Proof. exact (@lem1160577 (term91 _27264 t) (term92 _27264 h t)). Qed.
Lemma lem1160579 {_27264 : Type'} (h : _27264) (t : list _27264) (p' : Prop) : term93 _27264 h t p'.
Proof. exact (@lem1160578 _27264 h t p'). Qed.
Lemma lem1160580 {_27264 : Type'} (h : _27264) (t : list _27264) (p' : Prop) : (term93 _27264 h t p') = (term94 _27264 h t p').
Proof. exact (eq_refl (term93 _27264 h t p')). Qed.
Lemma lem1160581 {_27264 : Type'} (h : _27264) (t : list _27264) (p' : Prop) : term94 _27264 h t p'.
Proof. exact (EQ_MP (@lem1160580 _27264 h t p') (@lem1160579 _27264 h t p')). Qed.
Lemma lem1160582 {_27264 : Type'} (h : _27264) (t : list _27264) (p' : Prop) (q' : Prop) : term95 _27264 h t p' q'.
Proof. exact (@lem1160581 _27264 h t p' q'). Qed.
Lemma lem1160583 {_27264 : Type'} (h : _27264) (t : list _27264) (p' : Prop) (q' : Prop) : (term95 _27264 h t p' q') = (term96 _27264 h t p' q').
Proof. exact (eq_refl (term95 _27264 h t p' q')). Qed.
Lemma lem1160584 {_27264 : Type'} (h : _27264) (t : list _27264) (p' : Prop) (q' : Prop) : term96 _27264 h t p' q'.
Proof. exact (EQ_MP (@lem1160583 _27264 h t p' q') (@lem1160582 _27264 h t p' q')). Qed.
Lemma lem1160585 {_27264 : Type'} (t : list _27264) : (term91 _27264 t) = (term91 _27264 t).
Proof. exact (eq_refl (term91 _27264 t)). Qed.
Lemma lem1160586 {_27264 : Type'} (h : _27264) (t : list _27264) (q' : Prop) : term97 _27264 h t q'.
Proof. exact (@lem1160584 _27264 h t (term91 _27264 t) q'). Qed.
Lemma lem1160587 {_27264 : Type'} (h : _27264) (t : list _27264) (q' : Prop) : term98 _27264 h t q'.
Proof. exact (@lem1160586 _27264 h t q' (@lem1160585 _27264 t)). Qed.
Lemma lem1160596 {_25569 : Type'} (l : list _25569) : (term99 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1160597 {_27264 : Type'} (l : list _27264) : (term99 _27264 l) = (@hd _27264 l).
Proof. exact (@lem1160596 _27264 l). Qed.
Lemma lem1160598 {_27264 : Type'} (h : _27264) (t : list _27264) : (term100 _27264 h t) = (term101 _27264 h t).
Proof. exact (@lem1160597 _27264 (@cons _27264 h t)). Qed.
Lemma lem1160600 {A : Type'} (t : list A) (h : A) : (term101 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1160601 {_27264 : Type'} (t : list _27264) (h : _27264) : (term101 _27264 h t) = h.
Proof. exact (@lem1160600 _27264 t h). Qed.
Lemma lem1160602 {_27264 : Type'} (t : list _27264) (h : _27264) : (term100 _27264 h t) = h.
Proof. exact (TRANS (@lem1160598 _27264 h t) (@lem1160601 _27264 t h)). Qed.
Lemma lem1160603 {_27264 : Type'} : (@eq _27264) = (@eq _27264).
Proof. exact (eq_refl (@eq _27264)). Qed.
Lemma lem1160604 {_27264 : Type'} (t : list _27264) (h : _27264) : (term102 _27264 h t) = (@eq _27264 h).
Proof. exact (MK_COMB (@lem1160603 _27264) (@lem1160602 _27264 t h)). Qed.
Lemma lem1160605 {_27264 : Type'} (h : _27264) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1160606 {_27264 : Type'} (t : list _27264) (h : _27264) : ((term100 _27264 h t) = h) = (h = h).
Proof. exact (MK_COMB (@lem1160604 _27264 t h) (@lem1160605 _27264 h)). Qed.
Lemma lem1160608 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1160609 {_27264 : Type'} (x : _27264) : (x = x) = True.
Proof. exact (@lem1160608 _27264 x). Qed.
Lemma lem1160610 {_27264 : Type'} (h : _27264) : (h = h) = True.
Proof. exact (@lem1160609 _27264 h). Qed.
Lemma lem1160611 {_27264 : Type'} (t : list _27264) (h : _27264) : ((term100 _27264 h t) = h) = True.
Proof. exact (TRANS (@lem1160606 _27264 t h) (@lem1160610 _27264 h)). Qed.
Lemma lem1160612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1160613 {_27264 : Type'} (t : list _27264) (h : _27264) : (term103 _27264 t h) = (or True).
Proof. exact (MK_COMB (@lem1160612) (@lem1160611 _27264 t h)). Qed.
Lemma lem1160615 {_25569 : Type'} (l : list _25569) : (term99 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1160616 {_27264 : Type'} (l : list _27264) : (term99 _27264 l) = (@hd _27264 l).
Proof. exact (@lem1160615 _27264 l). Qed.
Lemma lem1160617 {_27264 : Type'} (h : _27264) (t : list _27264) : (term100 _27264 h t) = (term101 _27264 h t).
Proof. exact (@lem1160616 _27264 (@cons _27264 h t)). Qed.
Lemma lem1160619 {A : Type'} (t : list A) (h : A) : (term101 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1160620 {_27264 : Type'} (t : list _27264) (h : _27264) : (term101 _27264 h t) = h.
Proof. exact (@lem1160619 _27264 t h). Qed.
Lemma lem1160621 {_27264 : Type'} (t : list _27264) (h : _27264) : (term100 _27264 h t) = h.
Proof. exact (TRANS (@lem1160617 _27264 h t) (@lem1160620 _27264 t h)). Qed.
Lemma lem1160622 {_27264 : Type'} : (@List.In _27264) = (@List.In _27264).
Proof. exact (eq_refl (@List.In _27264)). Qed.
Lemma lem1160623 {_27264 : Type'} (t : list _27264) (h : _27264) : (term104 _27264 h t) = (@List.In _27264 h).
Proof. exact (MK_COMB (@lem1160622 _27264) (@lem1160621 _27264 t h)). Qed.
Lemma lem1160624 {_27264 : Type'} (t : list _27264) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1160625 {_27264 : Type'} (h : _27264) (t : list _27264) : (term105 _27264 h t) = (@List.In _27264 h t).
Proof. exact (MK_COMB (@lem1160623 _27264 t h) (@lem1160624 _27264 t)). Qed.
Lemma lem1160626 {_27264 : Type'} (h : _27264) (t : list _27264) : (term92 _27264 h t) = (term106 _27264 h t).
Proof. exact (MK_COMB (@lem1160613 _27264 t h) (@lem1160625 _27264 h t)). Qed.
Lemma lem1160628 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1160629 {_27264 : Type'} (h : _27264) (t : list _27264) : (term106 _27264 h t) = True.
Proof. exact (@lem1160628 (@List.In _27264 h t)). Qed.
Lemma lem1160630 {_27264 : Type'} (h : _27264) (t : list _27264) : (term92 _27264 h t) = True.
Proof. exact (TRANS (@lem1160626 _27264 h t) (@lem1160629 _27264 h t)). Qed.
Lemma lem1160631 {_27264 : Type'} (h : _27264) (t : list _27264) : term107 _27264 h t.
Proof. exact (fun h0 : term91 _27264 t => @lem1160630 _27264 h t). Qed.
Lemma lem1160632 {_27264 : Type'} (h : _27264) (t : list _27264) : term108 _27264 h t.
Proof. exact (@lem1160587 _27264 h t True). Qed.
Lemma lem1160633 {_27264 : Type'} (h : _27264) (t : list _27264) : (term66 _27264 h t) = (term109 _27264 t).
Proof. exact (@lem1160632 _27264 h t (@lem1160631 _27264 h t)). Qed.
Lemma lem1160635 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1160636 {_27264 : Type'} (t : list _27264) : (term109 _27264 t) = True.
Proof. exact (@lem1160635 (term91 _27264 t)). Qed.
Lemma lem1160637 {_27264 : Type'} (h : _27264) (t : list _27264) : (term66 _27264 h t) = True.
Proof. exact (TRANS (@lem1160633 _27264 h t) (@lem1160636 _27264 t)). Qed.
Lemma lem1160638 {_27264 : Type'} (h : _27264) (t : list _27264) : True = (term66 _27264 h t).
Proof. exact (SYM (@lem1160637 _27264 h t)). Qed.
Lemma lem1160639 {_27264 : Type'} (h : _27264) (t : list _27264) : term66 _27264 h t.
Proof. exact (EQ_MP (@lem1160638 _27264 h t) (@lem0)). Qed.
Lemma lem1160640 (m : nat) : term110 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem1160641 (m : nat) : (term110 m) = (term111 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem1160642 (m : nat) : term111 m.
Proof. exact (EQ_MP (@lem1160641 m) (@lem1160640 m)). Qed.
Lemma lem1160643 (m : nat) (n : nat) : term112 m n.
Proof. exact (@lem1160642 m n). Qed.
Lemma lem1160644 (m : nat) (n : nat) : (term112 m n) = ((term113 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term112 m n)). Qed.
Lemma lem1160648 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term17 _27264 t) : term114 _27264 t n.
Proof. exact (@lem1160459 _27264 t h1 n). Qed.
Lemma lem1160649 {_27264 : Type'} (n : nat) (t : list _27264) : (term114 _27264 t n) = (term115 _27264 n t).
Proof. exact (eq_refl (term114 _27264 t n)). Qed.
Lemma lem1160650 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term17 _27264 t) : term115 _27264 n t.
Proof. exact (EQ_MP (@lem1160649 _27264 n t) (@lem1160648 _27264 n t h1)). Qed.
Lemma lem1160651 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term116 _27264 n t) : term116 _27264 n t.
Proof. exact (h1). Qed.
Lemma lem1160652 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term17 _27264 t) (h2 : term116 _27264 n t) : term117 _27264 n t.
Proof. exact (@lem1160650 _27264 n t h1 (@lem1160651 _27264 n t h2)). Qed.
Lemma lem1160653 {_27264 : Type'} (n : nat) (t : list _27264) : (term117 _27264 n t) = ((term117 _27264 n t) = True).
Proof. exact (@lem7 (term117 _27264 n t)). Qed.
Lemma lem1160654 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term17 _27264 t) (h2 : term116 _27264 n t) : (term117 _27264 n t) = True.
Proof. exact (EQ_MP (@lem1160653 _27264 n t) (@lem1160652 _27264 n t h1 h2)). Qed.
Lemma lem1160672 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term87 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1160673 (p : Prop) (q : Prop) (p' : Prop) : term88 p q p'.
Proof. exact (fun q' : Prop => @lem1160672 p q p' q'). Qed.
Lemma lem1160674 (p : Prop) (q : Prop) : term89 p q.
Proof. exact (fun p' : Prop => @lem1160673 p q p'). Qed.
Lemma lem1160675 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : term118 _27264 n h t.
Proof. exact (@lem1160674 (term119 _27264 n t) (term120 _27264 n h t)). Qed.
Lemma lem1160676 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (p' : Prop) : term121 _27264 n h t p'.
Proof. exact (@lem1160675 _27264 n h t p'). Qed.
Lemma lem1160677 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (p' : Prop) : (term121 _27264 n h t p') = (term122 _27264 n h t p').
Proof. exact (eq_refl (term121 _27264 n h t p')). Qed.
Lemma lem1160678 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (p' : Prop) : term122 _27264 n h t p'.
Proof. exact (EQ_MP (@lem1160677 _27264 n h t p') (@lem1160676 _27264 n h t p')). Qed.
Lemma lem1160679 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (p' : Prop) (q' : Prop) : term123 _27264 n h t p' q'.
Proof. exact (@lem1160678 _27264 n h t p' q'). Qed.
Lemma lem1160680 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (p' : Prop) (q' : Prop) : (term123 _27264 n h t p' q') = (term124 _27264 n h t p' q').
Proof. exact (eq_refl (term123 _27264 n h t p' q')). Qed.
Lemma lem1160681 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (p' : Prop) (q' : Prop) : term124 _27264 n h t p' q'.
Proof. exact (EQ_MP (@lem1160680 _27264 n h t p' q') (@lem1160679 _27264 n h t p' q')). Qed.
Lemma lem1160683 (m : nat) (n : nat) : (term113 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1160644 m n) (@lem1160643 m n)). Qed.
Lemma lem1160684 {_27264 : Type'} (n : nat) (t : list _27264) : (term119 _27264 n t) = (term116 _27264 n t).
Proof. exact (@lem1160683 n (@List.length _27264 t)). Qed.
Lemma lem1160685 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) (q' : Prop) : term125 _27264 h n t q'.
Proof. exact (@lem1160681 _27264 n h t (term116 _27264 n t) q'). Qed.
Lemma lem1160686 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) (q' : Prop) : term126 _27264 h n t q'.
Proof. exact (@lem1160685 _27264 h n t q' (@lem1160684 _27264 n t)). Qed.
Lemma lem1160687 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term116 _27264 n t) : term116 _27264 n t.
Proof. exact (h1). Qed.
Lemma lem1160688 {_27264 : Type'} (n : nat) (t : list _27264) : (term116 _27264 n t) = ((term116 _27264 n t) = True).
Proof. exact (@lem7 (term116 _27264 n t)). Qed.
Lemma lem1160695 {_25569 : Type'} (n : nat) (l : list _25569) : (term127 _25569 n l) = (term128 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1160696 {_27264 : Type'} (n : nat) (l : list _27264) : (term127 _27264 n l) = (term128 _27264 n l).
Proof. exact (@lem1160695 _27264 n l). Qed.
Lemma lem1160697 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term129 _27264 n h t) = (term130 _27264 n h t).
Proof. exact (@lem1160696 _27264 n (@cons _27264 h t)). Qed.
Lemma lem1160699 {A : Type'} (h : A) (t : list A) : (term131 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1160700 {_27264 : Type'} (h : _27264) (t : list _27264) : (term131 _27264 h t) = t.
Proof. exact (@lem1160699 _27264 h t). Qed.
Lemma lem1160701 {_27264 : Type'} (n : nat) : (@EL _27264 n) = (@EL _27264 n).
Proof. exact (eq_refl (@EL _27264 n)). Qed.
Lemma lem1160702 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term130 _27264 n h t) = (@EL _27264 n t).
Proof. exact (MK_COMB (@lem1160701 _27264 n) (@lem1160700 _27264 h t)). Qed.
Lemma lem1160703 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term129 _27264 n h t) = (@EL _27264 n t).
Proof. exact (TRANS (@lem1160697 _27264 n h t) (@lem1160702 _27264 h n t)). Qed.
Lemma lem1160704 {_27264 : Type'} : (@eq _27264) = (@eq _27264).
Proof. exact (eq_refl (@eq _27264)). Qed.
Lemma lem1160705 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term132 _27264 n h t) = (term133 _27264 n t).
Proof. exact (MK_COMB (@lem1160704 _27264) (@lem1160703 _27264 h n t)). Qed.
Lemma lem1160706 {_27264 : Type'} (h : _27264) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1160707 {_27264 : Type'} (n : nat) (t : list _27264) (h : _27264) : ((term129 _27264 n h t) = h) = ((@EL _27264 n t) = h).
Proof. exact (MK_COMB (@lem1160705 _27264 h n t) (@lem1160706 _27264 h)). Qed.
Lemma lem1160710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1160711 {_27264 : Type'} (n : nat) (t : list _27264) (h : _27264) : (term134 _27264 n t h) = (term135 _27264 n t h).
Proof. exact (MK_COMB (@lem1160710) (@lem1160707 _27264 n t h)). Qed.
Lemma lem1160715 {_25569 : Type'} (n : nat) (l : list _25569) : (term127 _25569 n l) = (term128 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1160716 {_27264 : Type'} (n : nat) (l : list _27264) : (term127 _27264 n l) = (term128 _27264 n l).
Proof. exact (@lem1160715 _27264 n l). Qed.
Lemma lem1160717 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) : (term129 _27264 n h t) = (term130 _27264 n h t).
Proof. exact (@lem1160716 _27264 n (@cons _27264 h t)). Qed.
Lemma lem1160719 {A : Type'} (h : A) (t : list A) : (term131 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1160720 {_27264 : Type'} (h : _27264) (t : list _27264) : (term131 _27264 h t) = t.
Proof. exact (@lem1160719 _27264 h t). Qed.
Lemma lem1160721 {_27264 : Type'} (n : nat) : (@EL _27264 n) = (@EL _27264 n).
Proof. exact (eq_refl (@EL _27264 n)). Qed.
Lemma lem1160722 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term130 _27264 n h t) = (@EL _27264 n t).
Proof. exact (MK_COMB (@lem1160721 _27264 n) (@lem1160720 _27264 h t)). Qed.
Lemma lem1160723 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term129 _27264 n h t) = (@EL _27264 n t).
Proof. exact (TRANS (@lem1160717 _27264 n h t) (@lem1160722 _27264 h n t)). Qed.
Lemma lem1160724 {_27264 : Type'} : (@List.In _27264) = (@List.In _27264).
Proof. exact (eq_refl (@List.In _27264)). Qed.
Lemma lem1160725 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term136 _27264 n h t) = (term137 _27264 n t).
Proof. exact (MK_COMB (@lem1160724 _27264) (@lem1160723 _27264 h n t)). Qed.
Lemma lem1160726 {_27264 : Type'} (t : list _27264) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1160727 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : (term138 _27264 n h t) = (term117 _27264 n t).
Proof. exact (MK_COMB (@lem1160725 _27264 h n t) (@lem1160726 _27264 t)). Qed.
Lemma lem1160729 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term17 _27264 t) : term139 _27264 n t.
Proof. exact (fun h0 : term116 _27264 n t => @lem1160654 _27264 n t h1 h0). Qed.
Lemma lem1160731 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term116 _27264 n t) : (term116 _27264 n t) = True.
Proof. exact (EQ_MP (@lem1160688 _27264 n t) (@lem1160687 _27264 n t h1)). Qed.
Lemma lem1160732 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term116 _27264 n t) : True = (term116 _27264 n t).
Proof. exact (SYM (@lem1160731 _27264 n t h1)). Qed.
Lemma lem1160733 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term116 _27264 n t) : term116 _27264 n t.
Proof. exact (EQ_MP (@lem1160732 _27264 n t h1) (@lem0)). Qed.
Lemma lem1160734 {_27264 : Type'} (n : nat) (t : list _27264) (h1 : term17 _27264 t) (h2 : term116 _27264 n t) : (term117 _27264 n t) = True.
Proof. exact (@lem1160729 _27264 n t h1 (@lem1160733 _27264 n t h2)). Qed.
Lemma lem1160735 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) (h1 : term17 _27264 t) (h2 : term116 _27264 n t) : (term138 _27264 n h t) = True.
Proof. exact (TRANS (@lem1160727 _27264 h n t) (@lem1160734 _27264 n t h1 h2)). Qed.
Lemma lem1160736 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) (h1 : term17 _27264 t) (h2 : term116 _27264 n t) : (term120 _27264 n h t) = (term140 _27264 n t h).
Proof. exact (MK_COMB (@lem1160711 _27264 n t h) (@lem1160735 _27264 h n t h1 h2)). Qed.
Lemma lem1160738 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1160739 {_27264 : Type'} (n : nat) (t : list _27264) (h : _27264) : (term140 _27264 n t h) = True.
Proof. exact (@lem1160738 ((@EL _27264 n t) = h)). Qed.
Lemma lem1160740 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) (h1 : term17 _27264 t) (h2 : term116 _27264 n t) : (term120 _27264 n h t) = True.
Proof. exact (TRANS (@lem1160736 _27264 h n t h1 h2) (@lem1160739 _27264 n t h)). Qed.
Lemma lem1160741 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : term141 _27264 n h t.
Proof. exact (fun h0 : term116 _27264 n t => @lem1160740 _27264 h n t h1 h0). Qed.
Lemma lem1160742 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) : term142 _27264 h n t.
Proof. exact (@lem1160686 _27264 h n t True). Qed.
Lemma lem1160743 {_27264 : Type'} (h : _27264) (n : nat) (t : list _27264) (h1 : term17 _27264 t) : (term73 _27264 n h t) = (term143 _27264 n t).
Proof. exact (@lem1160742 _27264 h n t (@lem1160741 _27264 n h t h1)). Qed.
Lemma lem1160745 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1160746 {_27264 : Type'} (n : nat) (t : list _27264) : (term143 _27264 n t) = True.
Proof. exact (@lem1160745 (term116 _27264 n t)). Qed.
Lemma lem1160747 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : (term73 _27264 n h t) = True.
Proof. exact (TRANS (@lem1160743 _27264 h n t h1) (@lem1160746 _27264 n t)). Qed.
Lemma lem1160748 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : True = (term73 _27264 n h t).
Proof. exact (SYM (@lem1160747 _27264 n h t h1)). Qed.
Lemma lem1160749 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : term73 _27264 n h t.
Proof. exact (EQ_MP (@lem1160748 _27264 n h t h1) (@lem0)). Qed.
Lemma lem1160750 {_27264 : Type'} (n : nat) (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : term75 _27264 n h t.
Proof. exact (fun h0 : term59 _27264 n h t => @lem1160749 _27264 n h t h1). Qed.
Lemma lem1160755 {_27264 : Type'} (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : term79 _27264 h t.
Proof. exact (fun n : nat => @lem1160750 _27264 n h t h1). Qed.
Lemma lem1160756 {_27264 : Type'} (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : term81 _27264 h t.
Proof. exact (conj (@lem1160639 _27264 h t) (@lem1160755 _27264 h t h1)). Qed.
Lemma lem1160757 {_27264 : Type'} (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : term62 _27264 h t.
Proof. exact (@lem1160550 _27264 h t (@lem1160756 _27264 h t h1)). Qed.
Lemma lem1160758 {_27264 : Type'} (h : _27264) (t : list _27264) (h1 : term17 _27264 t) : term21 _27264 h t.
Proof. exact (EQ_MP (@lem1160527 _27264 h t) (@lem1160757 _27264 h t h1)). Qed.
Lemma lem1160759 {_27264 : Type'} (h : _27264) (t : list _27264) : term23 _27264 h t.
Proof. exact (fun h0 : term17 _27264 t => @lem1160758 _27264 h t h0). Qed.
Lemma lem1160764 {_27264 : Type'} (h : _27264) : term27 _27264 h.
Proof. exact (fun t : list _27264 => @lem1160759 _27264 h t). Qed.
Lemma lem1160769 {_27264 : Type'} : term31 _27264.
Proof. exact (fun h : _27264 => @lem1160764 _27264 h). Qed.
Lemma lem1160770 {_27264 : Type'} : term33 _27264.
Proof. exact (conj (@lem1160495 _27264) (@lem1160769 _27264)). Qed.
Lemma lem1160771 {_27264 : Type'} : term38 _27264.
Proof. exact (@lem1160458 _27264 (@lem1160770 _27264)). Qed.
