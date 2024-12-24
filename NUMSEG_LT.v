Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_LT_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1857_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
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
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem5479398 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5479399 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5479400 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5479399 A x) (@lem5479398 A x)). Qed.
Lemma lem5479401 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5479427 {_83095 : Type'} : term3 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5479428 {_83095 : Type'} (p : _83095 -> Prop) : term4 _83095 p.
Proof. exact (@lem5479427 _83095 p). Qed.
Lemma lem5479429 {_83095 : Type'} (p : _83095 -> Prop) : (term4 _83095 p) = (term5 _83095 p).
Proof. exact (eq_refl (term4 _83095 p)). Qed.
Lemma lem5479430 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (EQ_MP (@lem5479429 _83095 p) (@lem5479428 _83095 p)). Qed.
Lemma lem5479431 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term6 _83095 p x.
Proof. exact (@lem5479430 _83095 p x). Qed.
Lemma lem5479432 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term6 _83095 p x) = ((term7 _83095 x p) = (p x)).
Proof. exact (eq_refl (term6 _83095 p x)). Qed.
Lemma lem5479441 (m : nat) : term8 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5479442 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem5479443 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem5479442 m) (@lem5479441 m)). Qed.
Lemma lem5479444 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem5479443 m n). Qed.
Lemma lem5479445 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem5479446 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem5479445 m n) (@lem5479444 m n)). Qed.
Lemma lem5479447 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (@lem5479446 m n p). Qed.
Lemma lem5479448 (m : nat) (p : nat) (n : nat) : (term12 m n p) = ((term13 p m n) = (term14 m p n)).
Proof. exact (eq_refl (term12 m n p)). Qed.
Lemma lem5479450 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5479451 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (eq_refl (term15 A s)). Qed.
Lemma lem5479452 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem5479451 A s) (@lem5479450 A s)). Qed.
Lemma lem5479453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term17 A s t.
Proof. exact (@lem5479452 A s t). Qed.
Lemma lem5479454 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = ((s = t) = (term18 A s t)).
Proof. exact (eq_refl (term17 A s t)). Qed.
Lemma lem5479456 (_474 : nat -> Prop) (_475 : Prop) (_476 : type993) (_477 : nat -> Prop) : (term19 _476 _475 _474 _477) = (term20 _474 _475 _476 _477).
Proof. exact (@lem13473 (nat -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5479457 (_474 : nat -> Prop) (_475 : Prop) (n : nat) (_477 : nat -> Prop) : (term21 n _475 _474 _477) = (term22 _474 _475 n _477).
Proof. exact (@lem5479456 _474 _475 (term23 n) _477). Qed.
Lemma lem5479458 (n : nat) : (term24 n) = (term25 n).
Proof. exact (@lem5479457 (@EMPTY nat) (n = (NUMERAL 0)) n (term26 n)). Qed.
Lemma lem5479459 (n : nat) : (term27 n) = ((term28 n) = (term26 n)).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem5479460 (n : nat) : (term29 n) = (term29 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem5479461 (n : nat) : (term30 n) = (term31 n).
Proof. exact (MK_COMB (@lem5479460 n) (@lem5479459 n)). Qed.
Lemma lem5479462 (n : nat) : (term32 n) = ((term28 n) = (@EMPTY nat)).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem5479463 (n : nat) : (term33 n) = (term33 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem5479464 (n : nat) : (term34 n) = (term35 n).
Proof. exact (MK_COMB (@lem5479463 n) (@lem5479462 n)). Qed.
Lemma lem5479465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5479466 (n : nat) : (term36 n) = (term37 n).
Proof. exact (MK_COMB (@lem5479465) (@lem5479464 n)). Qed.
Lemma lem5479467 (n : nat) : (term25 n) = (term38 n).
Proof. exact (MK_COMB (@lem5479466 n) (@lem5479461 n)). Qed.
Lemma lem5479468 (n : nat) : (term24 n) = ((term28 n) = (term39 n)).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem5479469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5479470 (n : nat) : (term40 n) = (term41 n).
Proof. exact (MK_COMB (@lem5479469) (@lem5479468 n)). Qed.
Lemma lem5479471 (n : nat) : ((term24 n) = (term25 n)) = (((term28 n) = (term39 n)) = (term38 n)).
Proof. exact (MK_COMB (@lem5479470 n) (@lem5479467 n)). Qed.
Lemma lem5479472 (n : nat) : ((term28 n) = (term39 n)) = (term38 n).
Proof. exact (EQ_MP (@lem5479471 n) (@lem5479458 n)). Qed.
Lemma lem5479473 (n : nat) : (term38 n) = ((term28 n) = (term39 n)).
Proof. exact (SYM (@lem5479472 n)). Qed.
Lemma lem5479474 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem5479491 (n : nat) (h1 : term42 n) : term42 n.
Proof. exact (h1). Qed.
Lemma lem5479511 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem5479454 A s t) (@lem5479453 A s t)). Qed.
Lemma lem5479512 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term43 s t).
Proof. exact (@lem5479511 nat s t). Qed.
Lemma lem5479513 (n : nat) : ((term28 n) = (@EMPTY nat)) = (term44 n).
Proof. exact (@lem5479512 (term28 n) (@EMPTY nat)). Qed.
Lemma lem5479523 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5479432 _83095 p x) (@lem5479431 _83095 p x)). Qed.
Lemma lem5479524 (p : nat -> Prop) (x : nat) : (term45 x p) = (p x).
Proof. exact (@lem5479523 nat p x). Qed.
Lemma lem5479525 (n : nat) (x : nat) : (term46 x n) = (term47 n x).
Proof. exact (@lem5479524 (term48 n) x). Qed.
Lemma lem5479526 (x : nat) (n : nat) : (term47 n x) = (Peano.lt x n).
Proof. exact (eq_refl (term47 n x)). Qed.
Lemma lem5479527 (GEN_PVAR_232 : nat) : (@SETSPEC nat GEN_PVAR_232) = (@SETSPEC nat GEN_PVAR_232).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_232)). Qed.
Lemma lem5479528 (GEN_PVAR_232 : nat) (x : nat) (n : nat) : (term49 GEN_PVAR_232 n x) = (term50 GEN_PVAR_232 x n).
Proof. exact (MK_COMB (@lem5479527 GEN_PVAR_232) (@lem5479526 x n)). Qed.
Lemma lem5479529 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5479530 (GEN_PVAR_232 : nat) (n : nat) (x : nat) : (term51 GEN_PVAR_232 n x) = (term52 GEN_PVAR_232 n x).
Proof. exact (MK_COMB (@lem5479528 GEN_PVAR_232 x n) (@lem5479529 x)). Qed.
Lemma lem5479531 (GEN_PVAR_232 : nat) (n : nat) : (term53 GEN_PVAR_232 n) = (term54 GEN_PVAR_232 n).
Proof. exact (fun_ext (fun x : nat => @lem5479530 GEN_PVAR_232 n x)). Qed.
Lemma lem5479532 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5479533 (GEN_PVAR_232 : nat) (n : nat) : (term55 GEN_PVAR_232 n) = (term56 GEN_PVAR_232 n).
Proof. exact (MK_COMB (@lem5479532) (@lem5479531 GEN_PVAR_232 n)). Qed.
Lemma lem5479534 (n : nat) : (term57 n) = (term58 n).
Proof. exact (fun_ext (fun GEN_PVAR_232 : nat => @lem5479533 GEN_PVAR_232 n)). Qed.
Lemma lem5479535 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5479536 (n : nat) : (term59 n) = (term28 n).
Proof. exact (MK_COMB (@lem5479535) (@lem5479534 n)). Qed.
Lemma lem5479537 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5479538 (x : nat) (n : nat) : (term46 x n) = (term60 x n).
Proof. exact (MK_COMB (@lem5479537 x) (@lem5479536 n)). Qed.
Lemma lem5479539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5479540 (x : nat) (n : nat) : (term61 x n) = (term62 x n).
Proof. exact (MK_COMB (@lem5479539) (@lem5479538 x n)). Qed.
Lemma lem5479541 (x : nat) (n : nat) : (term47 n x) = (Peano.lt x n).
Proof. exact (eq_refl (term47 n x)). Qed.
Lemma lem5479542 (x : nat) (n : nat) : ((term46 x n) = (term47 n x)) = ((term60 x n) = (Peano.lt x n)).
Proof. exact (MK_COMB (@lem5479540 x n) (@lem5479541 x n)). Qed.
Lemma lem5479543 (x : nat) (n : nat) : (term60 x n) = (Peano.lt x n).
Proof. exact (EQ_MP (@lem5479542 x n) (@lem5479525 n x)). Qed.
Lemma lem5479544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5479545 (x : nat) (n : nat) : (term62 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem5479544) (@lem5479543 x n)). Qed.
Lemma lem5479547 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5479401 A x (@lem5479400 A x)). Qed.
Lemma lem5479548 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem5479547 nat x). Qed.
Lemma lem5479549 (x : nat) (n : nat) : ((term60 x n) = (@IN nat x (@EMPTY nat))) = ((Peano.lt x n) = False).
Proof. exact (MK_COMB (@lem5479545 x n) (@lem5479548 x)). Qed.
Lemma lem5479551 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5479552 (x : nat) (n : nat) : ((Peano.lt x n) = False) = (term64 x n).
Proof. exact (@lem5479551 (Peano.lt x n)). Qed.
Lemma lem5479553 (x : nat) (n : nat) : ((term60 x n) = (@IN nat x (@EMPTY nat))) = (term64 x n).
Proof. exact (TRANS (@lem5479549 x n) (@lem5479552 x n)). Qed.
Lemma lem5479554 (n : nat) : (term65 n) = (term66 n).
Proof. exact (fun_ext (fun x : nat => @lem5479553 x n)). Qed.
Lemma lem5479555 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479556 (n : nat) : (term44 n) = (term67 n).
Proof. exact (MK_COMB (@lem5479555) (@lem5479554 n)). Qed.
Lemma lem5479561 (n : nat) : ((term28 n) = (@EMPTY nat)) = (term67 n).
Proof. exact (TRANS (@lem5479513 n) (@lem5479556 n)). Qed.
Lemma lem5479562 (n : nat) : (term67 n) = ((term28 n) = (@EMPTY nat)).
Proof. exact (SYM (@lem5479561 n)). Qed.
Lemma lem5479566 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem5479454 A s t) (@lem5479453 A s t)). Qed.
Lemma lem5479567 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term43 s t).
Proof. exact (@lem5479566 nat s t). Qed.
Lemma lem5479568 (n : nat) : ((term28 n) = (term26 n)) = (term68 n).
Proof. exact (@lem5479567 (term28 n) (term26 n)). Qed.
Lemma lem5479578 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5479432 _83095 p x) (@lem5479431 _83095 p x)). Qed.
Lemma lem5479579 (p : nat -> Prop) (x : nat) : (term45 x p) = (p x).
Proof. exact (@lem5479578 nat p x). Qed.
Lemma lem5479580 (n : nat) (x : nat) : (term46 x n) = (term47 n x).
Proof. exact (@lem5479579 (term48 n) x). Qed.
Lemma lem5479581 (x : nat) (n : nat) : (term47 n x) = (Peano.lt x n).
Proof. exact (eq_refl (term47 n x)). Qed.
Lemma lem5479582 (GEN_PVAR_232 : nat) : (@SETSPEC nat GEN_PVAR_232) = (@SETSPEC nat GEN_PVAR_232).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_232)). Qed.
Lemma lem5479583 (GEN_PVAR_232 : nat) (x : nat) (n : nat) : (term49 GEN_PVAR_232 n x) = (term50 GEN_PVAR_232 x n).
Proof. exact (MK_COMB (@lem5479582 GEN_PVAR_232) (@lem5479581 x n)). Qed.
Lemma lem5479584 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5479585 (GEN_PVAR_232 : nat) (n : nat) (x : nat) : (term51 GEN_PVAR_232 n x) = (term52 GEN_PVAR_232 n x).
Proof. exact (MK_COMB (@lem5479583 GEN_PVAR_232 x n) (@lem5479584 x)). Qed.
Lemma lem5479586 (GEN_PVAR_232 : nat) (n : nat) : (term53 GEN_PVAR_232 n) = (term54 GEN_PVAR_232 n).
Proof. exact (fun_ext (fun x : nat => @lem5479585 GEN_PVAR_232 n x)). Qed.
Lemma lem5479587 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5479588 (GEN_PVAR_232 : nat) (n : nat) : (term55 GEN_PVAR_232 n) = (term56 GEN_PVAR_232 n).
Proof. exact (MK_COMB (@lem5479587) (@lem5479586 GEN_PVAR_232 n)). Qed.
Lemma lem5479589 (n : nat) : (term57 n) = (term58 n).
Proof. exact (fun_ext (fun GEN_PVAR_232 : nat => @lem5479588 GEN_PVAR_232 n)). Qed.
Lemma lem5479590 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5479591 (n : nat) : (term59 n) = (term28 n).
Proof. exact (MK_COMB (@lem5479590) (@lem5479589 n)). Qed.
Lemma lem5479592 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5479593 (x : nat) (n : nat) : (term46 x n) = (term60 x n).
Proof. exact (MK_COMB (@lem5479592 x) (@lem5479591 n)). Qed.
Lemma lem5479594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5479595 (x : nat) (n : nat) : (term61 x n) = (term62 x n).
Proof. exact (MK_COMB (@lem5479594) (@lem5479593 x n)). Qed.
Lemma lem5479596 (x : nat) (n : nat) : (term47 n x) = (Peano.lt x n).
Proof. exact (eq_refl (term47 n x)). Qed.
Lemma lem5479597 (x : nat) (n : nat) : ((term46 x n) = (term47 n x)) = ((term60 x n) = (Peano.lt x n)).
Proof. exact (MK_COMB (@lem5479595 x n) (@lem5479596 x n)). Qed.
Lemma lem5479598 (x : nat) (n : nat) : (term60 x n) = (Peano.lt x n).
Proof. exact (EQ_MP (@lem5479597 x n) (@lem5479580 n x)). Qed.
Lemma lem5479599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5479600 (x : nat) (n : nat) : (term62 x n) = (term63 x n).
Proof. exact (MK_COMB (@lem5479599) (@lem5479598 x n)). Qed.
Lemma lem5479602 (m : nat) (p : nat) (n : nat) : (term13 p m n) = (term14 m p n).
Proof. exact (EQ_MP (@lem5479448 m p n) (@lem5479447 m n p)). Qed.
Lemma lem5479603 (x : nat) (n : nat) : (term69 x n) = (term70 x n).
Proof. exact (@lem5479602 (NUMERAL 0) x (term71 n)). Qed.
Lemma lem5479606 (x : nat) (n : nat) : ((term60 x n) = (term69 x n)) = ((Peano.lt x n) = (term70 x n)).
Proof. exact (MK_COMB (@lem5479600 x n) (@lem5479603 x n)). Qed.
Lemma lem5479611 (n : nat) : (term72 n) = (term73 n).
Proof. exact (fun_ext (fun x : nat => @lem5479606 x n)). Qed.
Lemma lem5479612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479613 (n : nat) : (term68 n) = (term74 n).
Proof. exact (MK_COMB (@lem5479612) (@lem5479611 n)). Qed.
Lemma lem5479618 (n : nat) : ((term28 n) = (term26 n)) = (term74 n).
Proof. exact (TRANS (@lem5479568 n) (@lem5479613 n)). Qed.
Lemma lem5479619 (n : nat) : (term74 n) = ((term28 n) = (term26 n)).
Proof. exact (SYM (@lem5479618 n)). Qed.
Lemma lem5479633 (x : nat) (n : nat) : (term64 x n) = (term64 x n).
Proof. exact (eq_refl (term64 x n)). Qed.
Lemma lem5479634 (n : nat) : (term66 n) = (term66 n).
Proof. exact (fun_ext (fun x : nat => @lem5479633 x n)). Qed.
Lemma lem5479635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479636 (n : nat) : (term67 n) = (term67 n).
Proof. exact (MK_COMB (@lem5479635) (@lem5479634 n)). Qed.
Lemma lem5479639 (n : nat) : (term33 n) = (term33 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem5479641 (n : nat) : (term75 n) = (term75 n).
Proof. exact (MK_COMB (@lem5479639 n) (@lem5479636 n)). Qed.
Lemma lem5479643 (x : nat) (n : nat) : (term64 x n) = (term64 x n).
Proof. exact (eq_refl (term64 x n)). Qed.
Lemma lem5479644 (n : nat) : (term66 n) = (term66 n).
Proof. exact (fun_ext (fun x : nat => @lem5479643 x n)). Qed.
Lemma lem5479645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479646 (n : nat) : (term67 n) = (term67 n).
Proof. exact (MK_COMB (@lem5479645) (@lem5479644 n)). Qed.
Lemma lem5479648 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem5479649 (n : nat) : (term77 n) = (term77 n).
Proof. exact (MK_COMB (@lem5479648 n) (@lem5479646 n)). Qed.
Lemma lem5479650 (n : nat) : (term75 n) = (term77 n).
Proof. exact (@lem17265 (n = (NUMERAL 0)) (term67 n)). Qed.
Lemma lem5479651 (n : nat) : (term75 n) = (term77 n).
Proof. exact (TRANS (@lem5479650 n) (@lem5479649 n)). Qed.
Lemma lem5479652 (n : nat) : (term75 n) = (term77 n).
Proof. exact (TRANS (@lem5479641 n) (@lem5479651 n)). Qed.
Lemma lem5479653 (x : nat) (n : nat) : (term64 x n) = (term64 x n).
Proof. exact (eq_refl (term64 x n)). Qed.
Lemma lem5479654 (n : nat) : (term66 n) = (term66 n).
Proof. exact (fun_ext (fun x : nat => @lem5479653 x n)). Qed.
Lemma lem5479655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479656 (n : nat) : (term67 n) = (term67 n).
Proof. exact (MK_COMB (@lem5479655) (@lem5479654 n)). Qed.
Lemma lem5479659 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem5479660 (n : nat) : (term77 n) = (term77 n).
Proof. exact (MK_COMB (@lem5479659 n) (@lem5479656 n)). Qed.
Lemma lem5479675 (n : nat) : (term75 n) = (term77 n).
Proof. exact (TRANS (@lem5479652 n) (@lem5479660 n)). Qed.
Lemma lem5479682 (x : nat) (n : nat) : (term64 x n) = (term64 x n).
Proof. exact (eq_refl (term64 x n)). Qed.
Lemma lem5479683 (n : nat) : (term66 n) = (term66 n).
Proof. exact (fun_ext (fun x : nat => @lem5479682 x n)). Qed.
Lemma lem5479684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479685 (n : nat) : (term67 n) = (term67 n).
Proof. exact (MK_COMB (@lem5479684) (@lem5479683 n)). Qed.
Lemma lem5479694 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem5479695 (n : nat) : (term77 n) = (term77 n).
Proof. exact (MK_COMB (@lem5479694 n) (@lem5479685 n)). Qed.
Lemma lem5479696 (n : nat) : (term75 n) = (term77 n).
Proof. exact (TRANS (@lem5479675 n) (@lem5479695 n)). Qed.
Lemma lem5479698 {A : Type'} (P : Prop) (Q : A -> Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5479699 (P : Prop) (Q : nat -> Prop) : (term80 P Q) = (term81 P Q).
Proof. exact (@lem5479698 nat P Q). Qed.
Lemma lem5479700 (n : nat) : (term82 n) = (term83 n).
Proof. exact (@lem5479699 (term42 n) (term66 n)). Qed.
Lemma lem5479701 (x : nat) (n : nat) : (term84 n x) = (term64 x n).
Proof. exact (eq_refl (term84 n x)). Qed.
Lemma lem5479702 (n : nat) : (term85 n) = (term66 n).
Proof. exact (fun_ext (fun x : nat => @lem5479701 x n)). Qed.
Lemma lem5479703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479704 (n : nat) : (term86 n) = (term67 n).
Proof. exact (MK_COMB (@lem5479703) (@lem5479702 n)). Qed.
Lemma lem5479705 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem5479706 (n : nat) : (term82 n) = (term77 n).
Proof. exact (MK_COMB (@lem5479705 n) (@lem5479704 n)). Qed.
Lemma lem5479707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5479708 (n : nat) : (term87 n) = (term88 n).
Proof. exact (MK_COMB (@lem5479707) (@lem5479706 n)). Qed.
Lemma lem5479709 (x : nat) (n : nat) : (term84 n x) = (term64 x n).
Proof. exact (eq_refl (term84 n x)). Qed.
Lemma lem5479710 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem5479711 (x : nat) (n : nat) : (term89 n x) = (term90 x n).
Proof. exact (MK_COMB (@lem5479710 n) (@lem5479709 x n)). Qed.
Lemma lem5479712 (n : nat) : (term91 n) = (term92 n).
Proof. exact (fun_ext (fun x : nat => @lem5479711 x n)). Qed.
Lemma lem5479713 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479714 (n : nat) : (term83 n) = (term93 n).
Proof. exact (MK_COMB (@lem5479713) (@lem5479712 n)). Qed.
Lemma lem5479715 (n : nat) : ((term82 n) = (term83 n)) = ((term77 n) = (term93 n)).
Proof. exact (MK_COMB (@lem5479708 n) (@lem5479714 n)). Qed.
Lemma lem5479716 (n : nat) : (term77 n) = (term93 n).
Proof. exact (EQ_MP (@lem5479715 n) (@lem5479700 n)). Qed.
Lemma lem5479717 (n : nat) : (term75 n) = (term93 n).
Proof. exact (TRANS (@lem5479696 n) (@lem5479716 n)). Qed.
Lemma lem5479719 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5479720 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term94).
Proof. exact (@lem5479719 n (NUMERAL 0)). Qed.
Lemma lem5479723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5479724 (n : nat) : (term42 n) = (term95 n).
Proof. exact (MK_COMB (@lem5479723) (@lem5479720 n)). Qed.
Lemma lem5479725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5479726 (n : nat) : (term76 n) = (term96 n).
Proof. exact (MK_COMB (@lem5479725) (@lem5479724 n)). Qed.
Lemma lem5479728 (m : nat) (n : nat) : (Peano.lt m n) = (term97 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5479729 (x : nat) (n : nat) : (Peano.lt x n) = (term97 x n).
Proof. exact (@lem5479728 x n). Qed.
Lemma lem5479730 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5479731 (x : nat) (n : nat) : (term64 x n) = (term98 x n).
Proof. exact (MK_COMB (@lem5479730) (@lem5479729 x n)). Qed.
Lemma lem5479732 (x : nat) (n : nat) : (term90 x n) = (term99 x n).
Proof. exact (MK_COMB (@lem5479726 n) (@lem5479731 x n)). Qed.
Lemma lem5479733 (n : nat) : (term92 n) = (term100 n).
Proof. exact (fun_ext (fun x : nat => @lem5479732 x n)). Qed.
Lemma lem5479734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5479735 (n : nat) : (term93 n) = (term101 n).
Proof. exact (MK_COMB (@lem5479734) (@lem5479733 n)). Qed.
Lemma lem5479736 (n : nat) : (term75 n) = (term101 n).
Proof. exact (TRANS (@lem5479717 n) (@lem5479735 n)). Qed.
Lemma lem5479737 (n : nat) : term102 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5479738 (n : nat) : (term102 n) = (term103 n).
Proof. exact (eq_refl (term102 n)). Qed.
Lemma lem5479739 (n : nat) : term103 n.
Proof. exact (EQ_MP (@lem5479738 n) (@lem5479737 n)). Qed.
Lemma lem5479740 (x : nat) : term102 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5479741 (x : nat) : (term102 x) = (term103 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem5479742 (x : nat) : term103 x.
Proof. exact (EQ_MP (@lem5479741 x) (@lem5479740 x)). Qed.
Lemma lem5479743 (_70601 : int) (_70600 : int) : (term104 _70601 _70600) = (term105 _70601 _70600).
Proof. exact (@lem2318604 (term105 _70601 _70600)). Qed.
Lemma lem5479759 (_70600 : int) : (term106 _70600) = (_70600 = term94).
Proof. exact (@lem16933 (_70600 = term94)). Qed.
Lemma lem5479762 (_70601 : int) (_70600 : int) : (term107 _70601 _70600) = (int_lt _70601 _70600).
Proof. exact (@lem16933 (int_lt _70601 _70600)). Qed.
Lemma lem5479763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5479764 (_70600 : int) : (term108 _70600) = (term109 _70600).
Proof. exact (MK_COMB (@lem5479763) (@lem5479759 _70600)). Qed.
Lemma lem5479765 (_70601 : int) (_70600 : int) : (term110 _70601 _70600) = (term111 _70601 _70600).
Proof. exact (MK_COMB (@lem5479764 _70600) (@lem5479762 _70601 _70600)). Qed.
Lemma lem5479766 (_70601 : int) (_70600 : int) : (term112 _70601 _70600) = (term110 _70601 _70600).
Proof. exact (@lem17160 (term113 _70600) (term114 _70601 _70600)). Qed.
Lemma lem5479767 (_70601 : int) (_70600 : int) : (term112 _70601 _70600) = (term111 _70601 _70600).
Proof. exact (TRANS (@lem5479766 _70601 _70600) (@lem5479765 _70601 _70600)). Qed.
Lemma lem5479769 (_70601 : int) : (term115 _70601) = (term115 _70601).
Proof. exact (eq_refl (term115 _70601)). Qed.
Lemma lem5479770 (_70601 : int) (_70600 : int) : (term116 _70601 _70600) = (term117 _70601 _70600).
Proof. exact (MK_COMB (@lem5479769 _70601) (@lem5479767 _70601 _70600)). Qed.
Lemma lem5479771 (_70601 : int) (_70600 : int) : (term118 _70601 _70600) = (term116 _70601 _70600).
Proof. exact (@lem17362 (term119 _70601) (term120 _70601 _70600)). Qed.
Lemma lem5479772 (_70601 : int) (_70600 : int) : (term118 _70601 _70600) = (term117 _70601 _70600).
Proof. exact (TRANS (@lem5479771 _70601 _70600) (@lem5479770 _70601 _70600)). Qed.
Lemma lem5479774 (_70600 : int) : (term115 _70600) = (term115 _70600).
Proof. exact (eq_refl (term115 _70600)). Qed.
Lemma lem5479775 (_70601 : int) (_70600 : int) : (term121 _70601 _70600) = (term122 _70601 _70600).
Proof. exact (MK_COMB (@lem5479774 _70600) (@lem5479772 _70601 _70600)). Qed.
Lemma lem5479776 (_70601 : int) (_70600 : int) : (term123 _70601 _70600) = (term121 _70601 _70600).
Proof. exact (@lem17362 (term119 _70600) (term124 _70601 _70600)). Qed.
Lemma lem5479792 (_70601 : int) (_70600 : int) : (term123 _70601 _70600) = (term122 _70601 _70600).
Proof. exact (TRANS (@lem5479776 _70601 _70600) (@lem5479775 _70601 _70600)). Qed.
Lemma lem5479795 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5479796 (_70600 : int) : (term119 _70600) = (term126 _70600).
Proof. exact (@lem5479795 term94 _70600). Qed.
Lemma lem5479798 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5479799 : term128 = term129.
Proof. exact (@lem5479798 (NUMERAL 0)). Qed.
Lemma lem5479800 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5479801 : term130 = term131.
Proof. exact (MK_COMB (@lem5479800) (@lem5479799)). Qed.
Lemma lem5479802 (_70600 : int) : (real_of_int _70600) = (real_of_int _70600).
Proof. exact (eq_refl (real_of_int _70600)). Qed.
Lemma lem5479803 (_70600 : int) : (term126 _70600) = (term132 _70600).
Proof. exact (MK_COMB (@lem5479801) (@lem5479802 _70600)). Qed.
Lemma lem5479805 (_70600 : int) : (term119 _70600) = (term132 _70600).
Proof. exact (TRANS (@lem5479796 _70600) (@lem5479803 _70600)). Qed.
Lemma lem5479808 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5479809 (_70601 : int) : (term119 _70601) = (term126 _70601).
Proof. exact (@lem5479808 term94 _70601). Qed.
Lemma lem5479811 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5479812 : term128 = term129.
Proof. exact (@lem5479811 (NUMERAL 0)). Qed.
Lemma lem5479813 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5479814 : term130 = term131.
Proof. exact (MK_COMB (@lem5479813) (@lem5479812)). Qed.
Lemma lem5479815 (_70601 : int) : (real_of_int _70601) = (real_of_int _70601).
Proof. exact (eq_refl (real_of_int _70601)). Qed.
Lemma lem5479816 (_70601 : int) : (term126 _70601) = (term132 _70601).
Proof. exact (MK_COMB (@lem5479814) (@lem5479815 _70601)). Qed.
Lemma lem5479818 (_70601 : int) : (term119 _70601) = (term132 _70601).
Proof. exact (TRANS (@lem5479809 _70601) (@lem5479816 _70601)). Qed.
Lemma lem5479821 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5479822 (_70600 : int) : (_70600 = term94) = ((real_of_int _70600) = term128).
Proof. exact (@lem5479821 _70600 term94). Qed.
Lemma lem5479826 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5479827 : term128 = term129.
Proof. exact (@lem5479826 (NUMERAL 0)). Qed.
Lemma lem5479828 (_70600 : int) : (term133 _70600) = (term133 _70600).
Proof. exact (eq_refl (term133 _70600)). Qed.
Lemma lem5479829 (_70600 : int) : ((real_of_int _70600) = term128) = ((real_of_int _70600) = term129).
Proof. exact (MK_COMB (@lem5479828 _70600) (@lem5479827)). Qed.
Lemma lem5479831 (_70600 : int) : (_70600 = term94) = ((real_of_int _70600) = term129).
Proof. exact (TRANS (@lem5479822 _70600) (@lem5479829 _70600)). Qed.
Lemma lem5479833 (x : int) (y : int) : (int_lt x y) = (term134 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5479834 (_70601 : int) (_70600 : int) : (int_lt _70601 _70600) = (term134 _70601 _70600).
Proof. exact (@lem5479833 _70601 _70600). Qed.
Lemma lem5479836 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5479837 (_70601 : int) (_70600 : int) : (term134 _70601 _70600) = (term135 _70601 _70600).
Proof. exact (@lem5479836 (term136 _70601) _70600). Qed.
Lemma lem5479839 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5479840 (_70601 : int) : (term139 _70601) = (term140 _70601).
Proof. exact (@lem5479839 _70601 term141). Qed.
Lemma lem5479842 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5479843 : term142 = term143.
Proof. exact (@lem5479842 term144). Qed.
Lemma lem5479844 (_70601 : int) : (term145 _70601) = (term145 _70601).
Proof. exact (eq_refl (term145 _70601)). Qed.
Lemma lem5479845 (_70601 : int) : (term140 _70601) = (term146 _70601).
Proof. exact (MK_COMB (@lem5479844 _70601) (@lem5479843)). Qed.
Lemma lem5479846 (_70601 : int) : (term139 _70601) = (term146 _70601).
Proof. exact (TRANS (@lem5479840 _70601) (@lem5479845 _70601)). Qed.
Lemma lem5479847 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5479848 (_70601 : int) : (term147 _70601) = (term148 _70601).
Proof. exact (MK_COMB (@lem5479847) (@lem5479846 _70601)). Qed.
Lemma lem5479849 (_70600 : int) : (real_of_int _70600) = (real_of_int _70600).
Proof. exact (eq_refl (real_of_int _70600)). Qed.
Lemma lem5479850 (_70601 : int) (_70600 : int) : (term135 _70601 _70600) = (term149 _70601 _70600).
Proof. exact (MK_COMB (@lem5479848 _70601) (@lem5479849 _70600)). Qed.
Lemma lem5479851 (_70601 : int) (_70600 : int) : (term134 _70601 _70600) = (term149 _70601 _70600).
Proof. exact (TRANS (@lem5479837 _70601 _70600) (@lem5479850 _70601 _70600)). Qed.
Lemma lem5479852 (_70601 : int) (_70600 : int) : (int_lt _70601 _70600) = (term149 _70601 _70600).
Proof. exact (TRANS (@lem5479834 _70601 _70600) (@lem5479851 _70601 _70600)). Qed.
Lemma lem5479853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5479854 (_70600 : int) : (term109 _70600) = (term150 _70600).
Proof. exact (MK_COMB (@lem5479853) (@lem5479831 _70600)). Qed.
Lemma lem5479855 (_70601 : int) (_70600 : int) : (term111 _70601 _70600) = (term151 _70601 _70600).
Proof. exact (MK_COMB (@lem5479854 _70600) (@lem5479852 _70601 _70600)). Qed.
Lemma lem5479856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5479857 (_70601 : int) : (term115 _70601) = (term152 _70601).
Proof. exact (MK_COMB (@lem5479856) (@lem5479818 _70601)). Qed.
Lemma lem5479858 (_70601 : int) (_70600 : int) : (term117 _70601 _70600) = (term153 _70601 _70600).
Proof. exact (MK_COMB (@lem5479857 _70601) (@lem5479855 _70601 _70600)). Qed.
Lemma lem5479859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5479860 (_70600 : int) : (term115 _70600) = (term152 _70600).
Proof. exact (MK_COMB (@lem5479859) (@lem5479805 _70600)). Qed.
Lemma lem5479861 (_70601 : int) (_70600 : int) : (term122 _70601 _70600) = (term154 _70601 _70600).
Proof. exact (MK_COMB (@lem5479860 _70600) (@lem5479858 _70601 _70600)). Qed.
Lemma lem5479862 (_70601 : int) (_70600 : int) : (term123 _70601 _70600) = (term154 _70601 _70600).
Proof. exact (TRANS (@lem5479792 _70601 _70600) (@lem5479861 _70601 _70600)). Qed.
Lemma lem5479866 (t : Prop) : (term155 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5479902 (_70601 : int) (_70600 : int) : (term156 _70601 _70600) = (term154 _70601 _70600).
Proof. exact (@lem5479866 (term154 _70601 _70600)). Qed.
Lemma lem5479903 (_70600 : int) : (term132 _70600) = (term157 _70600).
Proof. exact (@lem1988287 (real_of_int _70600) term129). Qed.
Lemma lem5479909 (_70600 : int) : (term158 _70600) = (term159 _70600).
Proof. exact (@lem1982792 (real_of_int _70600) term129). Qed.
Lemma lem5479911 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5479912 : term129 = term161.
Proof. exact (@lem5479911 (NUMERAL 0)). Qed.
Lemma lem5479914 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5479915 : term164 = term165.
Proof. exact (@lem5479914 term144). Qed.
Lemma lem5479916 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5479917 : term166 = term167.
Proof. exact (MK_COMB (@lem5479916) (@lem5479915)). Qed.
Lemma lem5479918 : term168 = term169.
Proof. exact (MK_COMB (@lem5479917) (@lem5479912)). Qed.
Lemma lem5479919 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5479921 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5479922 : term173 = term174.
Proof. exact (@lem5479921 term144 term144). Qed.
Lemma lem5479923 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479924 : term176 = term144.
Proof. exact (EQ_MP (@lem5479923) (@lem940073)). Qed.
Lemma lem5479925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479926 : term174 = term143.
Proof. exact (MK_COMB (@lem5479925) (@lem5479924)). Qed.
Lemma lem5479927 : term173 = term143.
Proof. exact (TRANS (@lem5479922) (@lem5479926)). Qed.
Lemma lem5479929 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5479930 : term168 = term129.
Proof. exact (@lem5479929 term144). Qed.
Lemma lem5479931 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5479932 : term178 = term179.
Proof. exact (MK_COMB (@lem5479931) (@lem5479930)). Qed.
Lemma lem5479933 : term170 = term161.
Proof. exact (MK_COMB (@lem5479932) (@lem5479927)). Qed.
Lemma lem5479934 : term169 = term161.
Proof. exact (TRANS (@lem5479919) (@lem5479933)). Qed.
Lemma lem5479935 : term168 = term161.
Proof. exact (TRANS (@lem5479918) (@lem5479934)). Qed.
Lemma lem5479937 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5479938 : term161 = term129.
Proof. exact (@lem5479937 term129). Qed.
Lemma lem5479939 : term168 = term129.
Proof. exact (TRANS (@lem5479935) (@lem5479938)). Qed.
Lemma lem5479940 (_70600 : int) : (term145 _70600) = (term145 _70600).
Proof. exact (eq_refl (term145 _70600)). Qed.
Lemma lem5479941 (_70600 : int) : (term159 _70600) = (term181 _70600).
Proof. exact (MK_COMB (@lem5479940 _70600) (@lem5479939)). Qed.
Lemma lem5479942 (_70600 : int) : (term181 _70600) = (real_of_int _70600).
Proof. exact (@lem1982723 (real_of_int _70600)). Qed.
Lemma lem5479943 (_70600 : int) : (term159 _70600) = (real_of_int _70600).
Proof. exact (TRANS (@lem5479941 _70600) (@lem5479942 _70600)). Qed.
Lemma lem5479945 (_70600 : int) : (term158 _70600) = (real_of_int _70600).
Proof. exact (TRANS (@lem5479909 _70600) (@lem5479943 _70600)). Qed.
Lemma lem5479946 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5479947 (_70600 : int) : (term182 _70600) = (term183 _70600).
Proof. exact (MK_COMB (@lem5479946) (@lem5479945 _70600)). Qed.
Lemma lem5479948 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5479949 (_70600 : int) : (term157 _70600) = (term184 _70600).
Proof. exact (MK_COMB (@lem5479947 _70600) (@lem5479948)). Qed.
Lemma lem5479950 (_70600 : int) : (term132 _70600) = (term184 _70600).
Proof. exact (TRANS (@lem5479903 _70600) (@lem5479949 _70600)). Qed.
Lemma lem5479951 (_70601 : int) : (term132 _70601) = (term157 _70601).
Proof. exact (@lem1988287 (real_of_int _70601) term129). Qed.
Lemma lem5479957 (_70601 : int) : (term158 _70601) = (term159 _70601).
Proof. exact (@lem1982792 (real_of_int _70601) term129). Qed.
Lemma lem5479959 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5479960 : term129 = term161.
Proof. exact (@lem5479959 (NUMERAL 0)). Qed.
Lemma lem5479962 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5479963 : term164 = term165.
Proof. exact (@lem5479962 term144). Qed.
Lemma lem5479964 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5479965 : term166 = term167.
Proof. exact (MK_COMB (@lem5479964) (@lem5479963)). Qed.
Lemma lem5479966 : term168 = term169.
Proof. exact (MK_COMB (@lem5479965) (@lem5479960)). Qed.
Lemma lem5479967 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5479969 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5479970 : term173 = term174.
Proof. exact (@lem5479969 term144 term144). Qed.
Lemma lem5479971 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479972 : term176 = term144.
Proof. exact (EQ_MP (@lem5479971) (@lem940073)). Qed.
Lemma lem5479973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479974 : term174 = term143.
Proof. exact (MK_COMB (@lem5479973) (@lem5479972)). Qed.
Lemma lem5479975 : term173 = term143.
Proof. exact (TRANS (@lem5479970) (@lem5479974)). Qed.
Lemma lem5479977 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5479978 : term168 = term129.
Proof. exact (@lem5479977 term144). Qed.
Lemma lem5479979 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5479980 : term178 = term179.
Proof. exact (MK_COMB (@lem5479979) (@lem5479978)). Qed.
Lemma lem5479981 : term170 = term161.
Proof. exact (MK_COMB (@lem5479980) (@lem5479975)). Qed.
Lemma lem5479982 : term169 = term161.
Proof. exact (TRANS (@lem5479967) (@lem5479981)). Qed.
Lemma lem5479983 : term168 = term161.
Proof. exact (TRANS (@lem5479966) (@lem5479982)). Qed.
Lemma lem5479985 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5479986 : term161 = term129.
Proof. exact (@lem5479985 term129). Qed.
Lemma lem5479987 : term168 = term129.
Proof. exact (TRANS (@lem5479983) (@lem5479986)). Qed.
Lemma lem5479988 (_70601 : int) : (term145 _70601) = (term145 _70601).
Proof. exact (eq_refl (term145 _70601)). Qed.
Lemma lem5479989 (_70601 : int) : (term159 _70601) = (term181 _70601).
Proof. exact (MK_COMB (@lem5479988 _70601) (@lem5479987)). Qed.
Lemma lem5479990 (_70601 : int) : (term181 _70601) = (real_of_int _70601).
Proof. exact (@lem1982723 (real_of_int _70601)). Qed.
Lemma lem5479991 (_70601 : int) : (term159 _70601) = (real_of_int _70601).
Proof. exact (TRANS (@lem5479989 _70601) (@lem5479990 _70601)). Qed.
Lemma lem5479993 (_70601 : int) : (term158 _70601) = (real_of_int _70601).
Proof. exact (TRANS (@lem5479957 _70601) (@lem5479991 _70601)). Qed.
Lemma lem5479994 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5479995 (_70601 : int) : (term182 _70601) = (term183 _70601).
Proof. exact (MK_COMB (@lem5479994) (@lem5479993 _70601)). Qed.
Lemma lem5479996 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5479997 (_70601 : int) : (term157 _70601) = (term184 _70601).
Proof. exact (MK_COMB (@lem5479995 _70601) (@lem5479996)). Qed.
Lemma lem5479998 (_70601 : int) : (term132 _70601) = (term184 _70601).
Proof. exact (TRANS (@lem5479951 _70601) (@lem5479997 _70601)). Qed.
Lemma lem5479999 (_70600 : int) : ((real_of_int _70600) = term129) = ((term158 _70600) = term129).
Proof. exact (@lem1988293 (real_of_int _70600) term129). Qed.
Lemma lem5480005 (_70600 : int) : (term158 _70600) = (term159 _70600).
Proof. exact (@lem1982792 (real_of_int _70600) term129). Qed.
Lemma lem5480007 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480008 : term129 = term161.
Proof. exact (@lem5480007 (NUMERAL 0)). Qed.
Lemma lem5480010 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5480011 : term164 = term165.
Proof. exact (@lem5480010 term144). Qed.
Lemma lem5480012 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5480013 : term166 = term167.
Proof. exact (MK_COMB (@lem5480012) (@lem5480011)). Qed.
Lemma lem5480014 : term168 = term169.
Proof. exact (MK_COMB (@lem5480013) (@lem5480008)). Qed.
Lemma lem5480015 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5480017 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480018 : term173 = term174.
Proof. exact (@lem5480017 term144 term144). Qed.
Lemma lem5480019 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480020 : term176 = term144.
Proof. exact (EQ_MP (@lem5480019) (@lem940073)). Qed.
Lemma lem5480021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480022 : term174 = term143.
Proof. exact (MK_COMB (@lem5480021) (@lem5480020)). Qed.
Lemma lem5480023 : term173 = term143.
Proof. exact (TRANS (@lem5480018) (@lem5480022)). Qed.
Lemma lem5480025 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5480026 : term168 = term129.
Proof. exact (@lem5480025 term144). Qed.
Lemma lem5480027 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5480028 : term178 = term179.
Proof. exact (MK_COMB (@lem5480027) (@lem5480026)). Qed.
Lemma lem5480029 : term170 = term161.
Proof. exact (MK_COMB (@lem5480028) (@lem5480023)). Qed.
Lemma lem5480030 : term169 = term161.
Proof. exact (TRANS (@lem5480015) (@lem5480029)). Qed.
Lemma lem5480031 : term168 = term161.
Proof. exact (TRANS (@lem5480014) (@lem5480030)). Qed.
Lemma lem5480033 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5480034 : term161 = term129.
Proof. exact (@lem5480033 term129). Qed.
Lemma lem5480035 : term168 = term129.
Proof. exact (TRANS (@lem5480031) (@lem5480034)). Qed.
Lemma lem5480036 (_70600 : int) : (term145 _70600) = (term145 _70600).
Proof. exact (eq_refl (term145 _70600)). Qed.
Lemma lem5480037 (_70600 : int) : (term159 _70600) = (term181 _70600).
Proof. exact (MK_COMB (@lem5480036 _70600) (@lem5480035)). Qed.
Lemma lem5480038 (_70600 : int) : (term181 _70600) = (real_of_int _70600).
Proof. exact (@lem1982723 (real_of_int _70600)). Qed.
Lemma lem5480039 (_70600 : int) : (term159 _70600) = (real_of_int _70600).
Proof. exact (TRANS (@lem5480037 _70600) (@lem5480038 _70600)). Qed.
Lemma lem5480041 (_70600 : int) : (term158 _70600) = (real_of_int _70600).
Proof. exact (TRANS (@lem5480005 _70600) (@lem5480039 _70600)). Qed.
Lemma lem5480042 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5480043 (_70600 : int) : (term185 _70600) = (term133 _70600).
Proof. exact (MK_COMB (@lem5480042) (@lem5480041 _70600)). Qed.
Lemma lem5480044 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5480045 (_70600 : int) : ((term158 _70600) = term129) = ((real_of_int _70600) = term129).
Proof. exact (MK_COMB (@lem5480043 _70600) (@lem5480044)). Qed.
Lemma lem5480046 (_70600 : int) : ((real_of_int _70600) = term129) = ((real_of_int _70600) = term129).
Proof. exact (TRANS (@lem5479999 _70600) (@lem5480045 _70600)). Qed.
Lemma lem5480047 (_70600 : int) (_70601 : int) : (term149 _70601 _70600) = (term186 _70600 _70601).
Proof. exact (@lem1988287 (real_of_int _70600) (term146 _70601)). Qed.
Lemma lem5480059 (_70600 : int) (_70601 : int) : (term187 _70600 _70601) = (term188 _70600 _70601).
Proof. exact (@lem1982792 (real_of_int _70600) (term146 _70601)). Qed.
Lemma lem5480060 (_70601 : int) : (term189 _70601) = (term190 _70601).
Proof. exact (@lem1982781 (real_of_int _70601) term164 term143). Qed.
Lemma lem5480062 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480063 : term143 = term191.
Proof. exact (@lem5480062 term144). Qed.
Lemma lem5480065 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5480066 : term164 = term165.
Proof. exact (@lem5480065 term144). Qed.
Lemma lem5480067 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5480068 : term166 = term167.
Proof. exact (MK_COMB (@lem5480067) (@lem5480066)). Qed.
Lemma lem5480069 : term192 = term193.
Proof. exact (MK_COMB (@lem5480068) (@lem5480063)). Qed.
Lemma lem5480070 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5480072 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480073 : term173 = term174.
Proof. exact (@lem5480072 term144 term144). Qed.
Lemma lem5480074 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480075 : term176 = term144.
Proof. exact (EQ_MP (@lem5480074) (@lem940073)). Qed.
Lemma lem5480076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480077 : term174 = term143.
Proof. exact (MK_COMB (@lem5480076) (@lem5480075)). Qed.
Lemma lem5480078 : term173 = term143.
Proof. exact (TRANS (@lem5480073) (@lem5480077)). Qed.
Lemma lem5480080 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5480081 : term192 = term197.
Proof. exact (@lem5480080 term144 term144). Qed.
Lemma lem5480082 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480083 : term176 = term144.
Proof. exact (EQ_MP (@lem5480082) (@lem940073)). Qed.
Lemma lem5480084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480085 : term174 = term143.
Proof. exact (MK_COMB (@lem5480084) (@lem5480083)). Qed.
Lemma lem5480086 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5480087 : term197 = term164.
Proof. exact (MK_COMB (@lem5480086) (@lem5480085)). Qed.
Lemma lem5480088 : term192 = term164.
Proof. exact (TRANS (@lem5480081) (@lem5480087)). Qed.
Lemma lem5480089 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5480090 : term198 = term199.
Proof. exact (MK_COMB (@lem5480089) (@lem5480088)). Qed.
Lemma lem5480091 : term194 = term165.
Proof. exact (MK_COMB (@lem5480090) (@lem5480078)). Qed.
Lemma lem5480092 : term193 = term165.
Proof. exact (TRANS (@lem5480070) (@lem5480091)). Qed.
Lemma lem5480093 : term192 = term165.
Proof. exact (TRANS (@lem5480069) (@lem5480092)). Qed.
Lemma lem5480095 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5480096 : term165 = term164.
Proof. exact (@lem5480095 term164). Qed.
Lemma lem5480097 : term192 = term164.
Proof. exact (TRANS (@lem5480093) (@lem5480096)). Qed.
Lemma lem5480100 (_70601 : int) : (term200 _70601) = (term200 _70601).
Proof. exact (eq_refl (term200 _70601)). Qed.
Lemma lem5480101 (_70601 : int) : (term190 _70601) = (term201 _70601).
Proof. exact (MK_COMB (@lem5480100 _70601) (@lem5480097)). Qed.
Lemma lem5480102 (_70601 : int) : (term189 _70601) = (term201 _70601).
Proof. exact (TRANS (@lem5480060 _70601) (@lem5480101 _70601)). Qed.
Lemma lem5480103 (_70600 : int) : (term145 _70600) = (term145 _70600).
Proof. exact (eq_refl (term145 _70600)). Qed.
Lemma lem5480106 (_70600 : int) (_70601 : int) : (term188 _70600 _70601) = (term202 _70600 _70601).
Proof. exact (MK_COMB (@lem5480103 _70600) (@lem5480102 _70601)). Qed.
Lemma lem5480108 (_70600 : int) (_70601 : int) : (term187 _70600 _70601) = (term202 _70600 _70601).
Proof. exact (TRANS (@lem5480059 _70600 _70601) (@lem5480106 _70600 _70601)). Qed.
Lemma lem5480109 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5480110 (_70600 : int) (_70601 : int) : (term203 _70600 _70601) = (term204 _70600 _70601).
Proof. exact (MK_COMB (@lem5480109) (@lem5480108 _70600 _70601)). Qed.
Lemma lem5480111 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5480112 (_70600 : int) (_70601 : int) : (term186 _70600 _70601) = (term205 _70600 _70601).
Proof. exact (MK_COMB (@lem5480110 _70600 _70601) (@lem5480111)). Qed.
Lemma lem5480113 (_70600 : int) (_70601 : int) : (term149 _70601 _70600) = (term205 _70600 _70601).
Proof. exact (TRANS (@lem5480047 _70600 _70601) (@lem5480112 _70600 _70601)). Qed.
Lemma lem5480114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5480115 (_70600 : int) : (term150 _70600) = (term150 _70600).
Proof. exact (MK_COMB (@lem5480114) (@lem5480046 _70600)). Qed.
Lemma lem5480116 (_70600 : int) (_70601 : int) : (term151 _70601 _70600) = (term206 _70600 _70601).
Proof. exact (MK_COMB (@lem5480115 _70600) (@lem5480113 _70600 _70601)). Qed.
Lemma lem5480117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5480118 (_70601 : int) : (term152 _70601) = (term207 _70601).
Proof. exact (MK_COMB (@lem5480117) (@lem5479998 _70601)). Qed.
Lemma lem5480119 (_70600 : int) (_70601 : int) : (term153 _70601 _70600) = (term208 _70600 _70601).
Proof. exact (MK_COMB (@lem5480118 _70601) (@lem5480116 _70600 _70601)). Qed.
Lemma lem5480120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5480121 (_70600 : int) : (term152 _70600) = (term207 _70600).
Proof. exact (MK_COMB (@lem5480120) (@lem5479950 _70600)). Qed.
Lemma lem5480122 (_70600 : int) (_70601 : int) : (term154 _70601 _70600) = (term209 _70600 _70601).
Proof. exact (MK_COMB (@lem5480121 _70600) (@lem5480119 _70600 _70601)). Qed.
Lemma lem5480149 (_70600 : int) (_70601 : int) : (term156 _70601 _70600) = (term209 _70600 _70601).
Proof. exact (TRANS (@lem5479902 _70601 _70600) (@lem5480122 _70600 _70601)). Qed.
Lemma lem5480153 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term209 _70600 _70601.
Proof. exact (h1). Qed.
Lemma lem5480154 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term208 _70600 _70601.
Proof. exact (proj2 (@lem5480153 _70600 _70601 h1)). Qed.
Lemma lem5480156 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term206 _70600 _70601.
Proof. exact (proj2 (@lem5480154 _70600 _70601 h1)). Qed.
Lemma lem5480157 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term184 _70601.
Proof. exact (proj1 (@lem5480154 _70600 _70601 h1)). Qed.
Lemma lem5480158 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term205 _70600 _70601.
Proof. exact (proj2 (@lem5480156 _70600 _70601 h1)). Qed.
Lemma lem5480159 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : (real_of_int _70600) = term129.
Proof. exact (proj1 (@lem5480156 _70600 _70601 h1)). Qed.
Lemma lem5480161 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5480162 : term210 = term211.
Proof. exact (@lem5480161 term129 term143). Qed.
Lemma lem5480164 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480165 : term143 = term191.
Proof. exact (@lem5480164 term144). Qed.
Lemma lem5480167 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480168 : term129 = term161.
Proof. exact (@lem5480167 (NUMERAL 0)). Qed.
Lemma lem5480169 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5480170 : term212 = term213.
Proof. exact (MK_COMB (@lem5480169) (@lem5480168)). Qed.
Lemma lem5480171 : term211 = term214.
Proof. exact (MK_COMB (@lem5480170) (@lem5480165)). Qed.
Lemma lem5480172 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5480174 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480175 : term211 = term217.
Proof. exact (@lem5480174 (NUMERAL 0) term144). Qed.
Lemma lem5480176 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480177 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480178 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480177 h1) (fun h1 : term217 = True => @lem5480176)). Qed.
Lemma lem5480179 : term217 = True.
Proof. exact (EQ_MP (@lem5480178) (@lem5480176)). Qed.
Lemma lem5480180 : term211 = True.
Proof. exact (TRANS (@lem5480175) (@lem5480179)). Qed.
Lemma lem5480181 : True = term211.
Proof. exact (SYM (@lem5480180)). Qed.
Lemma lem5480182 : term211.
Proof. exact (EQ_MP (@lem5480181) (@lem0)). Qed.
Lemma lem5480183 : term219.
Proof. exact (@lem5480172 (@lem5480182)). Qed.
Lemma lem5480185 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480186 : term211 = term217.
Proof. exact (@lem5480185 (NUMERAL 0) term144). Qed.
Lemma lem5480187 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480188 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480189 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480188 h1) (fun h1 : term217 = True => @lem5480187)). Qed.
Lemma lem5480190 : term217 = True.
Proof. exact (EQ_MP (@lem5480189) (@lem5480187)). Qed.
Lemma lem5480191 : term211 = True.
Proof. exact (TRANS (@lem5480186) (@lem5480190)). Qed.
Lemma lem5480192 : True = term211.
Proof. exact (SYM (@lem5480191)). Qed.
Lemma lem5480193 : term211.
Proof. exact (EQ_MP (@lem5480192) (@lem0)). Qed.
Lemma lem5480194 : term214 = term220.
Proof. exact (@lem5480183 (@lem5480193)). Qed.
Lemma lem5480196 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480197 : term173 = term174.
Proof. exact (@lem5480196 term144 term144). Qed.
Lemma lem5480198 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480199 : term176 = term144.
Proof. exact (EQ_MP (@lem5480198) (@lem940073)). Qed.
Lemma lem5480200 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480201 : term174 = term143.
Proof. exact (MK_COMB (@lem5480200) (@lem5480199)). Qed.
Lemma lem5480202 : term173 = term143.
Proof. exact (TRANS (@lem5480197) (@lem5480201)). Qed.
Lemma lem5480204 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480205 : term222 = term129.
Proof. exact (@lem5480204 term144). Qed.
Lemma lem5480206 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5480207 : term223 = term212.
Proof. exact (MK_COMB (@lem5480206) (@lem5480205)). Qed.
Lemma lem5480208 : term220 = term211.
Proof. exact (MK_COMB (@lem5480207) (@lem5480202)). Qed.
Lemma lem5480210 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480211 : term211 = term217.
Proof. exact (@lem5480210 (NUMERAL 0) term144). Qed.
Lemma lem5480212 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480213 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480214 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480213 h1) (fun h1 : term217 = True => @lem5480212)). Qed.
Lemma lem5480215 : term217 = True.
Proof. exact (EQ_MP (@lem5480214) (@lem5480212)). Qed.
Lemma lem5480216 : term211 = True.
Proof. exact (TRANS (@lem5480211) (@lem5480215)). Qed.
Lemma lem5480217 : term220 = True.
Proof. exact (TRANS (@lem5480208) (@lem5480216)). Qed.
Lemma lem5480218 : term214 = True.
Proof. exact (TRANS (@lem5480194) (@lem5480217)). Qed.
Lemma lem5480219 : term211 = True.
Proof. exact (TRANS (@lem5480171) (@lem5480218)). Qed.
Lemma lem5480220 : term210 = True.
Proof. exact (TRANS (@lem5480162) (@lem5480219)). Qed.
Lemma lem5480221 : True = term210.
Proof. exact (SYM (@lem5480220)). Qed.
Lemma lem5480222 : term210.
Proof. exact (EQ_MP (@lem5480221) (@lem0)). Qed.
Lemma lem5480223 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term224 _70601.
Proof. exact (conj (@lem5480222) (@lem5480157 _70600 _70601 h1)). Qed.
Lemma lem5480225 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5480226 (_70601 : int) : term226 _70601.
Proof. exact (@lem5480225 term143 (real_of_int _70601)). Qed.
Lemma lem5480227 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term227 _70601.
Proof. exact (@lem5480226 _70601 (@lem5480223 _70600 _70601 h1)). Qed.
Lemma lem5480228 (_70601 : int) : (term228 _70601) = (real_of_int _70601).
Proof. exact (@lem1982733 (real_of_int _70601)). Qed.
Lemma lem5480229 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5480230 (_70601 : int) : (term229 _70601) = (term183 _70601).
Proof. exact (MK_COMB (@lem5480229) (@lem5480228 _70601)). Qed.
Lemma lem5480231 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5480232 (_70601 : int) : (term227 _70601) = (term184 _70601).
Proof. exact (MK_COMB (@lem5480230 _70601) (@lem5480231)). Qed.
Lemma lem5480233 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term184 _70601.
Proof. exact (EQ_MP (@lem5480232 _70601) (@lem5480227 _70600 _70601 h1)). Qed.
Lemma lem5480235 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5480236 : term210 = term211.
Proof. exact (@lem5480235 term129 term143). Qed.
Lemma lem5480238 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480239 : term143 = term191.
Proof. exact (@lem5480238 term144). Qed.
Lemma lem5480241 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480242 : term129 = term161.
Proof. exact (@lem5480241 (NUMERAL 0)). Qed.
Lemma lem5480243 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5480244 : term212 = term213.
Proof. exact (MK_COMB (@lem5480243) (@lem5480242)). Qed.
Lemma lem5480245 : term211 = term214.
Proof. exact (MK_COMB (@lem5480244) (@lem5480239)). Qed.
Lemma lem5480246 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5480248 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480249 : term211 = term217.
Proof. exact (@lem5480248 (NUMERAL 0) term144). Qed.
Lemma lem5480250 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480251 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480252 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480251 h1) (fun h1 : term217 = True => @lem5480250)). Qed.
Lemma lem5480253 : term217 = True.
Proof. exact (EQ_MP (@lem5480252) (@lem5480250)). Qed.
Lemma lem5480254 : term211 = True.
Proof. exact (TRANS (@lem5480249) (@lem5480253)). Qed.
Lemma lem5480255 : True = term211.
Proof. exact (SYM (@lem5480254)). Qed.
Lemma lem5480256 : term211.
Proof. exact (EQ_MP (@lem5480255) (@lem0)). Qed.
Lemma lem5480257 : term219.
Proof. exact (@lem5480246 (@lem5480256)). Qed.
Lemma lem5480259 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480260 : term211 = term217.
Proof. exact (@lem5480259 (NUMERAL 0) term144). Qed.
Lemma lem5480261 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480262 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480263 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480262 h1) (fun h1 : term217 = True => @lem5480261)). Qed.
Lemma lem5480264 : term217 = True.
Proof. exact (EQ_MP (@lem5480263) (@lem5480261)). Qed.
Lemma lem5480265 : term211 = True.
Proof. exact (TRANS (@lem5480260) (@lem5480264)). Qed.
Lemma lem5480266 : True = term211.
Proof. exact (SYM (@lem5480265)). Qed.
Lemma lem5480267 : term211.
Proof. exact (EQ_MP (@lem5480266) (@lem0)). Qed.
Lemma lem5480268 : term214 = term220.
Proof. exact (@lem5480257 (@lem5480267)). Qed.
Lemma lem5480270 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480271 : term173 = term174.
Proof. exact (@lem5480270 term144 term144). Qed.
Lemma lem5480272 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480273 : term176 = term144.
Proof. exact (EQ_MP (@lem5480272) (@lem940073)). Qed.
Lemma lem5480274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480275 : term174 = term143.
Proof. exact (MK_COMB (@lem5480274) (@lem5480273)). Qed.
Lemma lem5480276 : term173 = term143.
Proof. exact (TRANS (@lem5480271) (@lem5480275)). Qed.
Lemma lem5480278 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480279 : term222 = term129.
Proof. exact (@lem5480278 term144). Qed.
Lemma lem5480280 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5480281 : term223 = term212.
Proof. exact (MK_COMB (@lem5480280) (@lem5480279)). Qed.
Lemma lem5480282 : term220 = term211.
Proof. exact (MK_COMB (@lem5480281) (@lem5480276)). Qed.
Lemma lem5480284 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480285 : term211 = term217.
Proof. exact (@lem5480284 (NUMERAL 0) term144). Qed.
Lemma lem5480286 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480287 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480288 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480287 h1) (fun h1 : term217 = True => @lem5480286)). Qed.
Lemma lem5480289 : term217 = True.
Proof. exact (EQ_MP (@lem5480288) (@lem5480286)). Qed.
Lemma lem5480290 : term211 = True.
Proof. exact (TRANS (@lem5480285) (@lem5480289)). Qed.
Lemma lem5480291 : term220 = True.
Proof. exact (TRANS (@lem5480282) (@lem5480290)). Qed.
Lemma lem5480292 : term214 = True.
Proof. exact (TRANS (@lem5480268) (@lem5480291)). Qed.
Lemma lem5480293 : term211 = True.
Proof. exact (TRANS (@lem5480245) (@lem5480292)). Qed.
Lemma lem5480294 : term210 = True.
Proof. exact (TRANS (@lem5480236) (@lem5480293)). Qed.
Lemma lem5480295 : True = term210.
Proof. exact (SYM (@lem5480294)). Qed.
Lemma lem5480296 : term210.
Proof. exact (EQ_MP (@lem5480295) (@lem0)). Qed.
Lemma lem5480297 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term230 _70600 _70601.
Proof. exact (conj (@lem5480296) (@lem5480158 _70600 _70601 h1)). Qed.
Lemma lem5480299 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5480300 (_70600 : int) (_70601 : int) : term231 _70600 _70601.
Proof. exact (@lem5480299 term143 (term202 _70600 _70601)). Qed.
Lemma lem5480301 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term232 _70600 _70601.
Proof. exact (@lem5480300 _70600 _70601 (@lem5480297 _70600 _70601 h1)). Qed.
Lemma lem5480302 (_70600 : int) (_70601 : int) : (term233 _70600 _70601) = (term202 _70600 _70601).
Proof. exact (@lem1982733 (term202 _70600 _70601)). Qed.
Lemma lem5480303 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5480304 (_70600 : int) (_70601 : int) : (term234 _70600 _70601) = (term204 _70600 _70601).
Proof. exact (MK_COMB (@lem5480303) (@lem5480302 _70600 _70601)). Qed.
Lemma lem5480305 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5480306 (_70600 : int) (_70601 : int) : (term232 _70600 _70601) = (term205 _70600 _70601).
Proof. exact (MK_COMB (@lem5480304 _70600 _70601) (@lem5480305)). Qed.
Lemma lem5480307 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term205 _70600 _70601.
Proof. exact (EQ_MP (@lem5480306 _70600 _70601) (@lem5480301 _70600 _70601 h1)). Qed.
Lemma lem5480309 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5480310 (_70600 : int) : term236 _70600.
Proof. exact (@lem5480309 (real_of_int _70600)). Qed.
Lemma lem5480311 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term237 _70600.
Proof. exact (@lem5480310 _70600 (@lem5480159 _70600 _70601 h1)). Qed.
Lemma lem5480312 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term238 _70600.
Proof. exact (@lem5480311 _70600 _70601 h1 term164). Qed.
Lemma lem5480313 (_70600 : int) : (term238 _70600) = ((term239 _70600) = term129).
Proof. exact (eq_refl (term238 _70600)). Qed.
Lemma lem5480320 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : (term239 _70600) = term129.
Proof. exact (EQ_MP (@lem5480313 _70600) (@lem5480312 _70600 _70601 h1)). Qed.
Lemma lem5480321 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term240 _70600 _70601.
Proof. exact (conj (@lem5480320 _70600 _70601 h1) (@lem5480307 _70600 _70601 h1)). Qed.
Lemma lem5480323 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5480324 (_70600 : int) (_70601 : int) : term242 _70600 _70601.
Proof. exact (@lem5480323 (term239 _70600) (term202 _70600 _70601)). Qed.
Lemma lem5480325 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term243 _70600 _70601.
Proof. exact (@lem5480324 _70600 _70601 (@lem5480321 _70600 _70601 h1)). Qed.
Lemma lem5480326 (_70600 : int) (_70601 : int) : (term244 _70600 _70601) = (term245 _70600 _70601).
Proof. exact (@lem1982763 (term239 _70600) (real_of_int _70600) (term201 _70601)). Qed.
Lemma lem5480327 (_70600 : int) : (term246 _70600) = (term247 _70600).
Proof. exact (@lem1982713 term164 (real_of_int _70600)). Qed.
Lemma lem5480329 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480330 : term143 = term191.
Proof. exact (@lem5480329 term144). Qed.
Lemma lem5480332 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5480333 : term164 = term165.
Proof. exact (@lem5480332 term144). Qed.
Lemma lem5480334 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5480335 : term248 = term249.
Proof. exact (MK_COMB (@lem5480334) (@lem5480333)). Qed.
Lemma lem5480336 : term250 = term251.
Proof. exact (MK_COMB (@lem5480335) (@lem5480330)). Qed.
Lemma lem5480337 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5480339 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480340 : term211 = term217.
Proof. exact (@lem5480339 (NUMERAL 0) term144). Qed.
Lemma lem5480341 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480342 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480343 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480342 h1) (fun h1 : term217 = True => @lem5480341)). Qed.
Lemma lem5480344 : term217 = True.
Proof. exact (EQ_MP (@lem5480343) (@lem5480341)). Qed.
Lemma lem5480345 : term211 = True.
Proof. exact (TRANS (@lem5480340) (@lem5480344)). Qed.
Lemma lem5480346 : True = term211.
Proof. exact (SYM (@lem5480345)). Qed.
Lemma lem5480347 : term211.
Proof. exact (EQ_MP (@lem5480346) (@lem0)). Qed.
Lemma lem5480348 : term253.
Proof. exact (@lem5480337 (@lem5480347)). Qed.
Lemma lem5480350 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480351 : term211 = term217.
Proof. exact (@lem5480350 (NUMERAL 0) term144). Qed.
Lemma lem5480352 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480353 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480354 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480353 h1) (fun h1 : term217 = True => @lem5480352)). Qed.
Lemma lem5480355 : term217 = True.
Proof. exact (EQ_MP (@lem5480354) (@lem5480352)). Qed.
Lemma lem5480356 : term211 = True.
Proof. exact (TRANS (@lem5480351) (@lem5480355)). Qed.
Lemma lem5480357 : True = term211.
Proof. exact (SYM (@lem5480356)). Qed.
Lemma lem5480358 : term211.
Proof. exact (EQ_MP (@lem5480357) (@lem0)). Qed.
Lemma lem5480359 : term254.
Proof. exact (@lem5480348 (@lem5480358)). Qed.
Lemma lem5480361 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480362 : term211 = term217.
Proof. exact (@lem5480361 (NUMERAL 0) term144). Qed.
Lemma lem5480363 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480364 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480365 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480364 h1) (fun h1 : term217 = True => @lem5480363)). Qed.
Lemma lem5480366 : term217 = True.
Proof. exact (EQ_MP (@lem5480365) (@lem5480363)). Qed.
Lemma lem5480367 : term211 = True.
Proof. exact (TRANS (@lem5480362) (@lem5480366)). Qed.
Lemma lem5480368 : True = term211.
Proof. exact (SYM (@lem5480367)). Qed.
Lemma lem5480369 : term211.
Proof. exact (EQ_MP (@lem5480368) (@lem0)). Qed.
Lemma lem5480370 : term255.
Proof. exact (@lem5480359 (@lem5480369)). Qed.
Lemma lem5480372 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480373 : term173 = term174.
Proof. exact (@lem5480372 term144 term144). Qed.
Lemma lem5480374 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480375 : term176 = term144.
Proof. exact (EQ_MP (@lem5480374) (@lem940073)). Qed.
Lemma lem5480376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480377 : term174 = term143.
Proof. exact (MK_COMB (@lem5480376) (@lem5480375)). Qed.
Lemma lem5480378 : term173 = term143.
Proof. exact (TRANS (@lem5480373) (@lem5480377)). Qed.
Lemma lem5480380 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5480381 : term192 = term197.
Proof. exact (@lem5480380 term144 term144). Qed.
Lemma lem5480382 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480383 : term176 = term144.
Proof. exact (EQ_MP (@lem5480382) (@lem940073)). Qed.
Lemma lem5480384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480385 : term174 = term143.
Proof. exact (MK_COMB (@lem5480384) (@lem5480383)). Qed.
Lemma lem5480386 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5480387 : term197 = term164.
Proof. exact (MK_COMB (@lem5480386) (@lem5480385)). Qed.
Lemma lem5480388 : term192 = term164.
Proof. exact (TRANS (@lem5480381) (@lem5480387)). Qed.
Lemma lem5480389 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5480390 : term256 = term248.
Proof. exact (MK_COMB (@lem5480389) (@lem5480388)). Qed.
Lemma lem5480391 : term257 = term250.
Proof. exact (MK_COMB (@lem5480390) (@lem5480378)). Qed.
Lemma lem5480393 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5480394 : term250 = term129.
Proof. exact (@lem5480393 term144). Qed.
Lemma lem5480395 : term257 = term129.
Proof. exact (TRANS (@lem5480391) (@lem5480394)). Qed.
Lemma lem5480396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5480397 : term259 = term260.
Proof. exact (MK_COMB (@lem5480396) (@lem5480395)). Qed.
Lemma lem5480398 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5480399 : term261 = term222.
Proof. exact (MK_COMB (@lem5480397) (@lem5480398)). Qed.
Lemma lem5480401 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480402 : term222 = term129.
Proof. exact (@lem5480401 term144). Qed.
Lemma lem5480403 : term261 = term129.
Proof. exact (TRANS (@lem5480399) (@lem5480402)). Qed.
Lemma lem5480405 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480406 : term173 = term174.
Proof. exact (@lem5480405 term144 term144). Qed.
Lemma lem5480407 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480408 : term176 = term144.
Proof. exact (EQ_MP (@lem5480407) (@lem940073)). Qed.
Lemma lem5480409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480410 : term174 = term143.
Proof. exact (MK_COMB (@lem5480409) (@lem5480408)). Qed.
Lemma lem5480411 : term173 = term143.
Proof. exact (TRANS (@lem5480406) (@lem5480410)). Qed.
Lemma lem5480412 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5480413 : term262 = term222.
Proof. exact (MK_COMB (@lem5480412) (@lem5480411)). Qed.
Lemma lem5480415 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480416 : term222 = term129.
Proof. exact (@lem5480415 term144). Qed.
Lemma lem5480417 : term262 = term129.
Proof. exact (TRANS (@lem5480413) (@lem5480416)). Qed.
Lemma lem5480418 : term129 = term262.
Proof. exact (SYM (@lem5480417)). Qed.
Lemma lem5480419 : term261 = term262.
Proof. exact (TRANS (@lem5480403) (@lem5480418)). Qed.
Lemma lem5480420 : term251 = term161.
Proof. exact (@lem5480370 (@lem5480419)). Qed.
Lemma lem5480421 : term250 = term161.
Proof. exact (TRANS (@lem5480336) (@lem5480420)). Qed.
Lemma lem5480423 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5480424 : term161 = term129.
Proof. exact (@lem5480423 term129). Qed.
Lemma lem5480425 : term250 = term129.
Proof. exact (TRANS (@lem5480421) (@lem5480424)). Qed.
Lemma lem5480426 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5480427 : term263 = term260.
Proof. exact (MK_COMB (@lem5480426) (@lem5480425)). Qed.
Lemma lem5480428 (_70600 : int) : (real_of_int _70600) = (real_of_int _70600).
Proof. exact (eq_refl (real_of_int _70600)). Qed.
Lemma lem5480429 (_70600 : int) : (term247 _70600) = (term264 _70600).
Proof. exact (MK_COMB (@lem5480427) (@lem5480428 _70600)). Qed.
Lemma lem5480430 (_70600 : int) : (term246 _70600) = (term264 _70600).
Proof. exact (TRANS (@lem5480327 _70600) (@lem5480429 _70600)). Qed.
Lemma lem5480431 (_70600 : int) : (term264 _70600) = term129.
Proof. exact (@lem1982719 (real_of_int _70600)). Qed.
Lemma lem5480432 (_70600 : int) : (term246 _70600) = term129.
Proof. exact (TRANS (@lem5480430 _70600) (@lem5480431 _70600)). Qed.
Lemma lem5480433 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5480434 (_70600 : int) : (term265 _70600) = term266.
Proof. exact (MK_COMB (@lem5480433) (@lem5480432 _70600)). Qed.
Lemma lem5480435 (_70601 : int) : (term201 _70601) = (term201 _70601).
Proof. exact (eq_refl (term201 _70601)). Qed.
Lemma lem5480436 (_70600 : int) (_70601 : int) : (term245 _70600 _70601) = (term267 _70601).
Proof. exact (MK_COMB (@lem5480434 _70600) (@lem5480435 _70601)). Qed.
Lemma lem5480437 (_70600 : int) (_70601 : int) : (term244 _70600 _70601) = (term267 _70601).
Proof. exact (TRANS (@lem5480326 _70600 _70601) (@lem5480436 _70600 _70601)). Qed.
Lemma lem5480438 (_70601 : int) : (term267 _70601) = (term201 _70601).
Proof. exact (@lem1982721 (term201 _70601)). Qed.
Lemma lem5480439 (_70600 : int) (_70601 : int) : (term244 _70600 _70601) = (term201 _70601).
Proof. exact (TRANS (@lem5480437 _70600 _70601) (@lem5480438 _70601)). Qed.
Lemma lem5480440 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5480441 (_70600 : int) (_70601 : int) : (term268 _70600 _70601) = (term269 _70601).
Proof. exact (MK_COMB (@lem5480440) (@lem5480439 _70600 _70601)). Qed.
Lemma lem5480442 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5480443 (_70600 : int) (_70601 : int) : (term243 _70600 _70601) = (term270 _70601).
Proof. exact (MK_COMB (@lem5480441 _70600 _70601) (@lem5480442)). Qed.
Lemma lem5480444 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term270 _70601.
Proof. exact (EQ_MP (@lem5480443 _70600 _70601) (@lem5480325 _70600 _70601 h1)). Qed.
Lemma lem5480446 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5480447 : term210 = term211.
Proof. exact (@lem5480446 term129 term143). Qed.
Lemma lem5480449 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480450 : term143 = term191.
Proof. exact (@lem5480449 term144). Qed.
Lemma lem5480452 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480453 : term129 = term161.
Proof. exact (@lem5480452 (NUMERAL 0)). Qed.
Lemma lem5480454 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5480455 : term212 = term213.
Proof. exact (MK_COMB (@lem5480454) (@lem5480453)). Qed.
Lemma lem5480456 : term211 = term214.
Proof. exact (MK_COMB (@lem5480455) (@lem5480450)). Qed.
Lemma lem5480457 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5480459 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480460 : term211 = term217.
Proof. exact (@lem5480459 (NUMERAL 0) term144). Qed.
Lemma lem5480461 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480462 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480463 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480462 h1) (fun h1 : term217 = True => @lem5480461)). Qed.
Lemma lem5480464 : term217 = True.
Proof. exact (EQ_MP (@lem5480463) (@lem5480461)). Qed.
Lemma lem5480465 : term211 = True.
Proof. exact (TRANS (@lem5480460) (@lem5480464)). Qed.
Lemma lem5480466 : True = term211.
Proof. exact (SYM (@lem5480465)). Qed.
Lemma lem5480467 : term211.
Proof. exact (EQ_MP (@lem5480466) (@lem0)). Qed.
Lemma lem5480468 : term219.
Proof. exact (@lem5480457 (@lem5480467)). Qed.
Lemma lem5480470 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480471 : term211 = term217.
Proof. exact (@lem5480470 (NUMERAL 0) term144). Qed.
Lemma lem5480472 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480473 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480474 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480473 h1) (fun h1 : term217 = True => @lem5480472)). Qed.
Lemma lem5480475 : term217 = True.
Proof. exact (EQ_MP (@lem5480474) (@lem5480472)). Qed.
Lemma lem5480476 : term211 = True.
Proof. exact (TRANS (@lem5480471) (@lem5480475)). Qed.
Lemma lem5480477 : True = term211.
Proof. exact (SYM (@lem5480476)). Qed.
Lemma lem5480478 : term211.
Proof. exact (EQ_MP (@lem5480477) (@lem0)). Qed.
Lemma lem5480479 : term214 = term220.
Proof. exact (@lem5480468 (@lem5480478)). Qed.
Lemma lem5480481 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480482 : term173 = term174.
Proof. exact (@lem5480481 term144 term144). Qed.
Lemma lem5480483 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480484 : term176 = term144.
Proof. exact (EQ_MP (@lem5480483) (@lem940073)). Qed.
Lemma lem5480485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480486 : term174 = term143.
Proof. exact (MK_COMB (@lem5480485) (@lem5480484)). Qed.
Lemma lem5480487 : term173 = term143.
Proof. exact (TRANS (@lem5480482) (@lem5480486)). Qed.
Lemma lem5480489 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480490 : term222 = term129.
Proof. exact (@lem5480489 term144). Qed.
Lemma lem5480491 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5480492 : term223 = term212.
Proof. exact (MK_COMB (@lem5480491) (@lem5480490)). Qed.
Lemma lem5480493 : term220 = term211.
Proof. exact (MK_COMB (@lem5480492) (@lem5480487)). Qed.
Lemma lem5480495 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480496 : term211 = term217.
Proof. exact (@lem5480495 (NUMERAL 0) term144). Qed.
Lemma lem5480497 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480498 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480499 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480498 h1) (fun h1 : term217 = True => @lem5480497)). Qed.
Lemma lem5480500 : term217 = True.
Proof. exact (EQ_MP (@lem5480499) (@lem5480497)). Qed.
Lemma lem5480501 : term211 = True.
Proof. exact (TRANS (@lem5480496) (@lem5480500)). Qed.
Lemma lem5480502 : term220 = True.
Proof. exact (TRANS (@lem5480493) (@lem5480501)). Qed.
Lemma lem5480503 : term214 = True.
Proof. exact (TRANS (@lem5480479) (@lem5480502)). Qed.
Lemma lem5480504 : term211 = True.
Proof. exact (TRANS (@lem5480456) (@lem5480503)). Qed.
Lemma lem5480505 : term210 = True.
Proof. exact (TRANS (@lem5480447) (@lem5480504)). Qed.
Lemma lem5480506 : True = term210.
Proof. exact (SYM (@lem5480505)). Qed.
Lemma lem5480507 : term210.
Proof. exact (EQ_MP (@lem5480506) (@lem0)). Qed.
Lemma lem5480508 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term271 _70601.
Proof. exact (conj (@lem5480507) (@lem5480444 _70600 _70601 h1)). Qed.
Lemma lem5480510 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5480511 (_70601 : int) : term272 _70601.
Proof. exact (@lem5480510 term143 (term201 _70601)). Qed.
Lemma lem5480512 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term273 _70601.
Proof. exact (@lem5480511 _70601 (@lem5480508 _70600 _70601 h1)). Qed.
Lemma lem5480513 (_70601 : int) : (term274 _70601) = (term201 _70601).
Proof. exact (@lem1982733 (term201 _70601)). Qed.
Lemma lem5480514 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5480515 (_70601 : int) : (term275 _70601) = (term269 _70601).
Proof. exact (MK_COMB (@lem5480514) (@lem5480513 _70601)). Qed.
Lemma lem5480516 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5480517 (_70601 : int) : (term273 _70601) = (term270 _70601).
Proof. exact (MK_COMB (@lem5480515 _70601) (@lem5480516)). Qed.
Lemma lem5480518 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term270 _70601.
Proof. exact (EQ_MP (@lem5480517 _70601) (@lem5480512 _70600 _70601 h1)). Qed.
Lemma lem5480519 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term276 _70601.
Proof. exact (conj (@lem5480518 _70600 _70601 h1) (@lem5480233 _70600 _70601 h1)). Qed.
Lemma lem5480521 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5480522 (_70601 : int) : term278 _70601.
Proof. exact (@lem5480521 (term201 _70601) (real_of_int _70601)). Qed.
Lemma lem5480523 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term279 _70601.
Proof. exact (@lem5480522 _70601 (@lem5480519 _70600 _70601 h1)). Qed.
Lemma lem5480524 (_70601 : int) : (term280 _70601) = (term281 _70601).
Proof. exact (@lem1982759 (term239 _70601) (real_of_int _70601) term164). Qed.
Lemma lem5480525 (_70601 : int) : (term246 _70601) = (term247 _70601).
Proof. exact (@lem1982713 term164 (real_of_int _70601)). Qed.
Lemma lem5480527 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480528 : term143 = term191.
Proof. exact (@lem5480527 term144). Qed.
Lemma lem5480530 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5480531 : term164 = term165.
Proof. exact (@lem5480530 term144). Qed.
Lemma lem5480532 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5480533 : term248 = term249.
Proof. exact (MK_COMB (@lem5480532) (@lem5480531)). Qed.
Lemma lem5480534 : term250 = term251.
Proof. exact (MK_COMB (@lem5480533) (@lem5480528)). Qed.
Lemma lem5480535 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5480537 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480538 : term211 = term217.
Proof. exact (@lem5480537 (NUMERAL 0) term144). Qed.
Lemma lem5480539 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480540 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480541 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480540 h1) (fun h1 : term217 = True => @lem5480539)). Qed.
Lemma lem5480542 : term217 = True.
Proof. exact (EQ_MP (@lem5480541) (@lem5480539)). Qed.
Lemma lem5480543 : term211 = True.
Proof. exact (TRANS (@lem5480538) (@lem5480542)). Qed.
Lemma lem5480544 : True = term211.
Proof. exact (SYM (@lem5480543)). Qed.
Lemma lem5480545 : term211.
Proof. exact (EQ_MP (@lem5480544) (@lem0)). Qed.
Lemma lem5480546 : term253.
Proof. exact (@lem5480535 (@lem5480545)). Qed.
Lemma lem5480548 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480549 : term211 = term217.
Proof. exact (@lem5480548 (NUMERAL 0) term144). Qed.
Lemma lem5480550 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480551 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480552 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480551 h1) (fun h1 : term217 = True => @lem5480550)). Qed.
Lemma lem5480553 : term217 = True.
Proof. exact (EQ_MP (@lem5480552) (@lem5480550)). Qed.
Lemma lem5480554 : term211 = True.
Proof. exact (TRANS (@lem5480549) (@lem5480553)). Qed.
Lemma lem5480555 : True = term211.
Proof. exact (SYM (@lem5480554)). Qed.
Lemma lem5480556 : term211.
Proof. exact (EQ_MP (@lem5480555) (@lem0)). Qed.
Lemma lem5480557 : term254.
Proof. exact (@lem5480546 (@lem5480556)). Qed.
Lemma lem5480559 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480560 : term211 = term217.
Proof. exact (@lem5480559 (NUMERAL 0) term144). Qed.
Lemma lem5480561 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480562 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480563 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480562 h1) (fun h1 : term217 = True => @lem5480561)). Qed.
Lemma lem5480564 : term217 = True.
Proof. exact (EQ_MP (@lem5480563) (@lem5480561)). Qed.
Lemma lem5480565 : term211 = True.
Proof. exact (TRANS (@lem5480560) (@lem5480564)). Qed.
Lemma lem5480566 : True = term211.
Proof. exact (SYM (@lem5480565)). Qed.
Lemma lem5480567 : term211.
Proof. exact (EQ_MP (@lem5480566) (@lem0)). Qed.
Lemma lem5480568 : term255.
Proof. exact (@lem5480557 (@lem5480567)). Qed.
Lemma lem5480570 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480571 : term173 = term174.
Proof. exact (@lem5480570 term144 term144). Qed.
Lemma lem5480572 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480573 : term176 = term144.
Proof. exact (EQ_MP (@lem5480572) (@lem940073)). Qed.
Lemma lem5480574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480575 : term174 = term143.
Proof. exact (MK_COMB (@lem5480574) (@lem5480573)). Qed.
Lemma lem5480576 : term173 = term143.
Proof. exact (TRANS (@lem5480571) (@lem5480575)). Qed.
Lemma lem5480578 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5480579 : term192 = term197.
Proof. exact (@lem5480578 term144 term144). Qed.
Lemma lem5480580 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480581 : term176 = term144.
Proof. exact (EQ_MP (@lem5480580) (@lem940073)). Qed.
Lemma lem5480582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480583 : term174 = term143.
Proof. exact (MK_COMB (@lem5480582) (@lem5480581)). Qed.
Lemma lem5480584 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5480585 : term197 = term164.
Proof. exact (MK_COMB (@lem5480584) (@lem5480583)). Qed.
Lemma lem5480586 : term192 = term164.
Proof. exact (TRANS (@lem5480579) (@lem5480585)). Qed.
Lemma lem5480587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5480588 : term256 = term248.
Proof. exact (MK_COMB (@lem5480587) (@lem5480586)). Qed.
Lemma lem5480589 : term257 = term250.
Proof. exact (MK_COMB (@lem5480588) (@lem5480576)). Qed.
Lemma lem5480591 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5480592 : term250 = term129.
Proof. exact (@lem5480591 term144). Qed.
Lemma lem5480593 : term257 = term129.
Proof. exact (TRANS (@lem5480589) (@lem5480592)). Qed.
Lemma lem5480594 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5480595 : term259 = term260.
Proof. exact (MK_COMB (@lem5480594) (@lem5480593)). Qed.
Lemma lem5480596 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5480597 : term261 = term222.
Proof. exact (MK_COMB (@lem5480595) (@lem5480596)). Qed.
Lemma lem5480599 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480600 : term222 = term129.
Proof. exact (@lem5480599 term144). Qed.
Lemma lem5480601 : term261 = term129.
Proof. exact (TRANS (@lem5480597) (@lem5480600)). Qed.
Lemma lem5480603 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5480604 : term173 = term174.
Proof. exact (@lem5480603 term144 term144). Qed.
Lemma lem5480605 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480606 : term176 = term144.
Proof. exact (EQ_MP (@lem5480605) (@lem940073)). Qed.
Lemma lem5480607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480608 : term174 = term143.
Proof. exact (MK_COMB (@lem5480607) (@lem5480606)). Qed.
Lemma lem5480609 : term173 = term143.
Proof. exact (TRANS (@lem5480604) (@lem5480608)). Qed.
Lemma lem5480610 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5480611 : term262 = term222.
Proof. exact (MK_COMB (@lem5480610) (@lem5480609)). Qed.
Lemma lem5480613 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480614 : term222 = term129.
Proof. exact (@lem5480613 term144). Qed.
Lemma lem5480615 : term262 = term129.
Proof. exact (TRANS (@lem5480611) (@lem5480614)). Qed.
Lemma lem5480616 : term129 = term262.
Proof. exact (SYM (@lem5480615)). Qed.
Lemma lem5480617 : term261 = term262.
Proof. exact (TRANS (@lem5480601) (@lem5480616)). Qed.
Lemma lem5480618 : term251 = term161.
Proof. exact (@lem5480568 (@lem5480617)). Qed.
Lemma lem5480619 : term250 = term161.
Proof. exact (TRANS (@lem5480534) (@lem5480618)). Qed.
Lemma lem5480621 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5480622 : term161 = term129.
Proof. exact (@lem5480621 term129). Qed.
Lemma lem5480623 : term250 = term129.
Proof. exact (TRANS (@lem5480619) (@lem5480622)). Qed.
Lemma lem5480624 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5480625 : term263 = term260.
Proof. exact (MK_COMB (@lem5480624) (@lem5480623)). Qed.
Lemma lem5480626 (_70601 : int) : (real_of_int _70601) = (real_of_int _70601).
Proof. exact (eq_refl (real_of_int _70601)). Qed.
Lemma lem5480627 (_70601 : int) : (term247 _70601) = (term264 _70601).
Proof. exact (MK_COMB (@lem5480625) (@lem5480626 _70601)). Qed.
Lemma lem5480628 (_70601 : int) : (term246 _70601) = (term264 _70601).
Proof. exact (TRANS (@lem5480525 _70601) (@lem5480627 _70601)). Qed.
Lemma lem5480629 (_70601 : int) : (term264 _70601) = term129.
Proof. exact (@lem1982719 (real_of_int _70601)). Qed.
Lemma lem5480630 (_70601 : int) : (term246 _70601) = term129.
Proof. exact (TRANS (@lem5480628 _70601) (@lem5480629 _70601)). Qed.
Lemma lem5480631 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5480632 (_70601 : int) : (term265 _70601) = term266.
Proof. exact (MK_COMB (@lem5480631) (@lem5480630 _70601)). Qed.
Lemma lem5480633 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5480634 (_70601 : int) : (term281 _70601) = term282.
Proof. exact (MK_COMB (@lem5480632 _70601) (@lem5480633)). Qed.
Lemma lem5480635 (_70601 : int) : (term280 _70601) = term282.
Proof. exact (TRANS (@lem5480524 _70601) (@lem5480634 _70601)). Qed.
Lemma lem5480636 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5480637 (_70601 : int) : (term280 _70601) = term164.
Proof. exact (TRANS (@lem5480635 _70601) (@lem5480636)). Qed.
Lemma lem5480638 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5480639 (_70601 : int) : (term283 _70601) = term284.
Proof. exact (MK_COMB (@lem5480638) (@lem5480637 _70601)). Qed.
Lemma lem5480640 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5480641 (_70601 : int) : (term279 _70601) = term285.
Proof. exact (MK_COMB (@lem5480639 _70601) (@lem5480640)). Qed.
Lemma lem5480642 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term285.
Proof. exact (EQ_MP (@lem5480641 _70601) (@lem5480523 _70600 _70601 h1)). Qed.
Lemma lem5480644 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5480645 : term285 = term286.
Proof. exact (@lem5480644 term129 term164). Qed.
Lemma lem5480647 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5480648 : term164 = term165.
Proof. exact (@lem5480647 term144). Qed.
Lemma lem5480650 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5480651 : term129 = term161.
Proof. exact (@lem5480650 (NUMERAL 0)). Qed.
Lemma lem5480652 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5480653 : term131 = term287.
Proof. exact (MK_COMB (@lem5480652) (@lem5480651)). Qed.
Lemma lem5480654 : term286 = term288.
Proof. exact (MK_COMB (@lem5480653) (@lem5480648)). Qed.
Lemma lem5480655 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5480657 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480658 : term211 = term217.
Proof. exact (@lem5480657 (NUMERAL 0) term144). Qed.
Lemma lem5480659 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480660 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480661 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480660 h1) (fun h1 : term217 = True => @lem5480659)). Qed.
Lemma lem5480662 : term217 = True.
Proof. exact (EQ_MP (@lem5480661) (@lem5480659)). Qed.
Lemma lem5480663 : term211 = True.
Proof. exact (TRANS (@lem5480658) (@lem5480662)). Qed.
Lemma lem5480664 : True = term211.
Proof. exact (SYM (@lem5480663)). Qed.
Lemma lem5480665 : term211.
Proof. exact (EQ_MP (@lem5480664) (@lem0)). Qed.
Lemma lem5480666 : term290.
Proof. exact (@lem5480655 (@lem5480665)). Qed.
Lemma lem5480668 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5480669 : term211 = term217.
Proof. exact (@lem5480668 (NUMERAL 0) term144). Qed.
Lemma lem5480670 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480671 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5480672 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480671 h1) (fun h1 : term217 = True => @lem5480670)). Qed.
Lemma lem5480673 : term217 = True.
Proof. exact (EQ_MP (@lem5480672) (@lem5480670)). Qed.
Lemma lem5480674 : term211 = True.
Proof. exact (TRANS (@lem5480669) (@lem5480673)). Qed.
Lemma lem5480675 : True = term211.
Proof. exact (SYM (@lem5480674)). Qed.
Lemma lem5480676 : term211.
Proof. exact (EQ_MP (@lem5480675) (@lem0)). Qed.
Lemma lem5480677 : term288 = term291.
Proof. exact (@lem5480666 (@lem5480676)). Qed.
Lemma lem5480679 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5480680 : term192 = term197.
Proof. exact (@lem5480679 term144 term144). Qed.
Lemma lem5480681 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5480682 : term176 = term144.
Proof. exact (EQ_MP (@lem5480681) (@lem940073)). Qed.
Lemma lem5480683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5480684 : term174 = term143.
Proof. exact (MK_COMB (@lem5480683) (@lem5480682)). Qed.
Lemma lem5480685 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5480686 : term197 = term164.
Proof. exact (MK_COMB (@lem5480685) (@lem5480684)). Qed.
Lemma lem5480687 : term192 = term164.
Proof. exact (TRANS (@lem5480680) (@lem5480686)). Qed.
Lemma lem5480689 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5480690 : term222 = term129.
Proof. exact (@lem5480689 term144). Qed.
Lemma lem5480691 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5480692 : term292 = term131.
Proof. exact (MK_COMB (@lem5480691) (@lem5480690)). Qed.
Lemma lem5480693 : term291 = term286.
Proof. exact (MK_COMB (@lem5480692) (@lem5480687)). Qed.
Lemma lem5480695 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5480696 : term286 = term295.
Proof. exact (@lem5480695 (NUMERAL 0) term144). Qed.
Lemma lem5480697 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5480698 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5480699 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5480698 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5480697)). Qed.
Lemma lem5480700 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5480699) (@lem5480697)). Qed.
Lemma lem5480701 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5480702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5480703 : term296 = (and True).
Proof. exact (MK_COMB (@lem5480702) (@lem5480701)). Qed.
Lemma lem5480704 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5480703) (@lem5480700)). Qed.
Lemma lem5480706 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5480707 : term295 = False.
Proof. exact (TRANS (@lem5480704) (@lem5480706)). Qed.
Lemma lem5480708 : term286 = False.
Proof. exact (TRANS (@lem5480696) (@lem5480707)). Qed.
Lemma lem5480709 : term291 = False.
Proof. exact (TRANS (@lem5480693) (@lem5480708)). Qed.
Lemma lem5480710 : term288 = False.
Proof. exact (TRANS (@lem5480677) (@lem5480709)). Qed.
Lemma lem5480711 : term286 = False.
Proof. exact (TRANS (@lem5480654) (@lem5480710)). Qed.
Lemma lem5480712 : term285 = False.
Proof. exact (TRANS (@lem5480645) (@lem5480711)). Qed.
Lemma lem5480713 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : False.
Proof. exact (EQ_MP (@lem5480712) (@lem5480642 _70600 _70601 h1)). Qed.
Lemma lem5480715 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : term209 _70600 _70601.
Proof. exact (h1). Qed.
Lemma lem5480716 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : (term209 _70600 _70601) = False.
Proof. exact (prop_ext (fun h2 : term209 _70600 _70601 => @lem5480713 _70600 _70601 h1) (fun h2 : False => @lem5480715 _70600 _70601 h1)). Qed.
Lemma lem5480717 (_70600 : int) (_70601 : int) (h1 : term209 _70600 _70601) : False.
Proof. exact (EQ_MP (@lem5480716 _70600 _70601 h1) (@lem5480715 _70600 _70601 h1)). Qed.
Lemma lem5480718 (_70601 : int) (_70600 : int) (h1 : term156 _70601 _70600) : term156 _70601 _70600.
Proof. exact (h1). Qed.
Lemma lem5480719 (_70601 : int) (_70600 : int) (h1 : term156 _70601 _70600) : term209 _70600 _70601.
Proof. exact (EQ_MP (@lem5480149 _70600 _70601) (@lem5480718 _70601 _70600 h1)). Qed.
Lemma lem5480720 (_70601 : int) (_70600 : int) (h1 : term156 _70601 _70600) : (term209 _70600 _70601) = False.
Proof. exact (prop_ext (fun h2 : term209 _70600 _70601 => @lem5480717 _70600 _70601 h2) (fun h2 : False => @lem5480719 _70601 _70600 h1)). Qed.
Lemma lem5480721 (_70601 : int) (_70600 : int) (h1 : term156 _70601 _70600) : False.
Proof. exact (EQ_MP (@lem5480720 _70601 _70600 h1) (@lem5480719 _70601 _70600 h1)). Qed.
Lemma lem5480722 (_70601 : int) (_70600 : int) : term297 _70601 _70600.
Proof. exact (fun h0 : term156 _70601 _70600 => @lem5480721 _70601 _70600 h0). Qed.
Lemma lem5480723 (_70601 : int) (_70600 : int) : term298 _70601 _70600.
Proof. exact (@lem1386578 (term299 _70601 _70600)). Qed.
Lemma lem5480726 (_70601 : int) (_70600 : int) : term299 _70601 _70600.
Proof. exact (@lem5480723 _70601 _70600 (@lem5480722 _70601 _70600)). Qed.
Lemma lem5480727 (_70601 : int) (_70600 : int) : (term154 _70601 _70600) = (term123 _70601 _70600).
Proof. exact (SYM (@lem5479862 _70601 _70600)). Qed.
Lemma lem5480728 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5480729 (_70601 : int) (_70600 : int) : (term299 _70601 _70600) = (term104 _70601 _70600).
Proof. exact (MK_COMB (@lem5480728) (@lem5480727 _70601 _70600)). Qed.
Lemma lem5480730 (_70601 : int) (_70600 : int) : term104 _70601 _70600.
Proof. exact (EQ_MP (@lem5480729 _70601 _70600) (@lem5480726 _70601 _70600)). Qed.
Lemma lem5480731 (_70601 : int) (_70600 : int) : term105 _70601 _70600.
Proof. exact (EQ_MP (@lem5479743 _70601 _70600) (@lem5480730 _70601 _70600)). Qed.
Lemma lem5480732 (x : nat) (n : nat) : term300 x n.
Proof. exact (@lem5480731 (int_of_num x) (int_of_num n)). Qed.
Lemma lem5480733 (x : nat) (n : nat) : term301 x n.
Proof. exact (@lem5480732 x n (@lem5479739 n)). Qed.
Lemma lem5480734 (x : nat) (n : nat) : term99 x n.
Proof. exact (@lem5480733 x n (@lem5479742 x)). Qed.
Lemma lem5480735 (n : nat) : term101 n.
Proof. exact (fun x : nat => @lem5480734 x n). Qed.
Lemma lem5480736 (n : nat) : (term101 n) = (term75 n).
Proof. exact (SYM (@lem5479736 n)). Qed.
Lemma lem5480737 (n : nat) : term75 n.
Proof. exact (EQ_MP (@lem5480736 n) (@lem5480735 n)). Qed.
Lemma lem5480738 (n : nat) : (term75 n) = ((term75 n) = True).
Proof. exact (@lem7 (term75 n)). Qed.
Lemma lem5480739 (n : nat) : (term75 n) = True.
Proof. exact (EQ_MP (@lem5480738 n) (@lem5480737 n)). Qed.
Lemma lem5480740 (n : nat) : True = (term75 n).
Proof. exact (SYM (@lem5480739 n)). Qed.
Lemma lem5480741 (n : nat) : term75 n.
Proof. exact (EQ_MP (@lem5480740 n) (@lem0)). Qed.
Lemma lem5480742 (n : nat) (h1 : n = (NUMERAL 0)) : term67 n.
Proof. exact (@lem5480741 n (@lem5479474 n h1)). Qed.
Lemma lem5480764 (x : nat) (n : nat) : ((Peano.lt x n) = (term70 x n)) = ((Peano.lt x n) = (term70 x n)).
Proof. exact (eq_refl ((Peano.lt x n) = (term70 x n))). Qed.
Lemma lem5480765 (n : nat) : (term73 n) = (term73 n).
Proof. exact (fun_ext (fun x : nat => @lem5480764 x n)). Qed.
Lemma lem5480766 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480767 (n : nat) : (term74 n) = (term74 n).
Proof. exact (MK_COMB (@lem5480766) (@lem5480765 n)). Qed.
Lemma lem5480772 (n : nat) : (term29 n) = (term29 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem5480774 (n : nat) : (term302 n) = (term302 n).
Proof. exact (MK_COMB (@lem5480772 n) (@lem5480767 n)). Qed.
Lemma lem5480777 (n : nat) : (term303 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem5480788 (x : nat) (n : nat) : (term304 x n) = (term305 x n).
Proof. exact (@lem17045 (term306 x) (term307 x n)). Qed.
Lemma lem5480794 (x : nat) (n : nat) : (term308 x n) = (term308 x n).
Proof. exact (eq_refl (term308 x n)). Qed.
Lemma lem5480796 (x : nat) (n : nat) : (term309 x n) = (term309 x n).
Proof. exact (eq_refl (term309 x n)). Qed.
Lemma lem5480797 (x : nat) (n : nat) : (term310 x n) = (term311 x n).
Proof. exact (MK_COMB (@lem5480796 x n) (@lem5480788 x n)). Qed.
Lemma lem5480798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5480799 (x : nat) (n : nat) : (term312 x n) = (term313 x n).
Proof. exact (MK_COMB (@lem5480798) (@lem5480797 x n)). Qed.
Lemma lem5480800 (x : nat) (n : nat) : (term314 x n) = (term315 x n).
Proof. exact (MK_COMB (@lem5480799 x n) (@lem5480794 x n)). Qed.
Lemma lem5480801 (x : nat) (n : nat) : ((Peano.lt x n) = (term70 x n)) = (term314 x n).
Proof. exact (@lem17784 (Peano.lt x n) (term70 x n)). Qed.
Lemma lem5480802 (x : nat) (n : nat) : ((Peano.lt x n) = (term70 x n)) = (term315 x n).
Proof. exact (TRANS (@lem5480801 x n) (@lem5480800 x n)). Qed.
Lemma lem5480803 (n : nat) : (term73 n) = (term316 n).
Proof. exact (fun_ext (fun x : nat => @lem5480802 x n)). Qed.
Lemma lem5480804 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480805 (n : nat) : (term74 n) = (term317 n).
Proof. exact (MK_COMB (@lem5480804) (@lem5480803 n)). Qed.
Lemma lem5480806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5480807 (n : nat) : (term318 n) = (term319 n).
Proof. exact (MK_COMB (@lem5480806) (@lem5480777 n)). Qed.
Lemma lem5480808 (n : nat) : (term320 n) = (term321 n).
Proof. exact (MK_COMB (@lem5480807 n) (@lem5480805 n)). Qed.
Lemma lem5480809 (n : nat) : (term302 n) = (term320 n).
Proof. exact (@lem17265 (term42 n) (term74 n)). Qed.
Lemma lem5480810 (n : nat) : (term302 n) = (term321 n).
Proof. exact (TRANS (@lem5480809 n) (@lem5480808 n)). Qed.
Lemma lem5480811 (n : nat) : (term302 n) = (term321 n).
Proof. exact (TRANS (@lem5480774 n) (@lem5480810 n)). Qed.
Lemma lem5480812 (n : nat) (x : nat) : (term322 x n) = (term323 n x).
Proof. exact (@lem1032781 n term144 (term324 n x)). Qed.
Lemma lem5480813 (n : nat) (x : nat) (d : nat) : (term325 n x d) = (term326 n x d).
Proof. exact (eq_refl (term325 n x d)). Qed.
Lemma lem5480814 (n : nat) (d : nat) : (term327 n d) = (term327 n d).
Proof. exact (eq_refl (term327 n d)). Qed.
Lemma lem5480815 (n : nat) (x : nat) (d : nat) : (term328 n x d) = (term329 n x d).
Proof. exact (MK_COMB (@lem5480814 n d) (@lem5480813 n x d)). Qed.
Lemma lem5480816 (n : nat) (x : nat) : (term330 n x) = (term331 n x).
Proof. exact (fun_ext (fun d : nat => @lem5480815 n x d)). Qed.
Lemma lem5480817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480818 (n : nat) (x : nat) : (term323 n x) = (term332 n x).
Proof. exact (MK_COMB (@lem5480817) (@lem5480816 n x)). Qed.
Lemma lem5480819 (x : nat) (n : nat) : (term322 x n) = (term315 x n).
Proof. exact (eq_refl (term322 x n)). Qed.
Lemma lem5480820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5480821 (x : nat) (n : nat) : (term333 x n) = (term334 x n).
Proof. exact (MK_COMB (@lem5480820) (@lem5480819 x n)). Qed.
Lemma lem5480822 (n : nat) (x : nat) : ((term322 x n) = (term323 n x)) = ((term315 x n) = (term332 n x)).
Proof. exact (MK_COMB (@lem5480821 x n) (@lem5480818 n x)). Qed.
Lemma lem5480823 (n : nat) (x : nat) : (term315 x n) = (term332 n x).
Proof. exact (EQ_MP (@lem5480822 n x) (@lem5480812 n x)). Qed.
Lemma lem5480824 (n : nat) (x : nat) (d : nat) : (term329 n x d) = (term329 n x d).
Proof. exact (eq_refl (term329 n x d)). Qed.
Lemma lem5480825 (n : nat) (x : nat) : (term331 n x) = (term331 n x).
Proof. exact (fun_ext (fun d : nat => @lem5480824 n x d)). Qed.
Lemma lem5480826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480827 (n : nat) (x : nat) : (term332 n x) = (term332 n x).
Proof. exact (MK_COMB (@lem5480826) (@lem5480825 n x)). Qed.
Lemma lem5480828 (x : nat) (n : nat) : (term334 x n) = (term334 x n).
Proof. exact (eq_refl (term334 x n)). Qed.
Lemma lem5480829 (n : nat) (x : nat) : ((term315 x n) = (term332 n x)) = ((term315 x n) = (term332 n x)).
Proof. exact (MK_COMB (@lem5480828 x n) (@lem5480827 n x)). Qed.
Lemma lem5480830 (n : nat) (x : nat) : (term315 x n) = (term332 n x).
Proof. exact (EQ_MP (@lem5480829 n x) (@lem5480823 n x)). Qed.
Lemma lem5480831 (n : nat) : (term316 n) = (term335 n).
Proof. exact (fun_ext (fun x : nat => @lem5480830 n x)). Qed.
Lemma lem5480832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480833 (n : nat) : (term317 n) = (term336 n).
Proof. exact (MK_COMB (@lem5480832) (@lem5480831 n)). Qed.
Lemma lem5480836 (n : nat) : (term319 n) = (term319 n).
Proof. exact (eq_refl (term319 n)). Qed.
Lemma lem5480837 (n : nat) : (term321 n) = (term337 n).
Proof. exact (MK_COMB (@lem5480836 n) (@lem5480833 n)). Qed.
Lemma lem5480876 (n : nat) : (term302 n) = (term337 n).
Proof. exact (TRANS (@lem5480811 n) (@lem5480837 n)). Qed.
Lemma lem5480927 (n : nat) (x : nat) (d : nat) : (term326 n x d) = (term326 n x d).
Proof. exact (eq_refl (term326 n x d)). Qed.
Lemma lem5480944 (n : nat) (d : nat) : (term338 n d) = (term338 n d).
Proof. exact (eq_refl (term338 n d)). Qed.
Lemma lem5480951 (d : nat) : (term339 d) = (term340 d).
Proof. exact (@lem1032098 d term144). Qed.
Lemma lem5480954 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem5480955 (n : nat) (d : nat) : (n = (term339 d)) = (n = (term340 d)).
Proof. exact (MK_COMB (@lem5480954 n) (@lem5480951 d)). Qed.
Lemma lem5480956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5480957 (n : nat) (d : nat) : (term341 n d) = (term342 n d).
Proof. exact (MK_COMB (@lem5480956) (@lem5480955 n d)). Qed.
Lemma lem5480958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5480959 (n : nat) (d : nat) : (term343 n d) = (term344 n d).
Proof. exact (MK_COMB (@lem5480958) (@lem5480957 n d)). Qed.
Lemma lem5480960 (n : nat) (d : nat) : (term345 n d) = (term346 n d).
Proof. exact (MK_COMB (@lem5480959 n d) (@lem5480944 n d)). Qed.
Lemma lem5480961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5480962 (n : nat) (d : nat) : (term327 n d) = (term347 n d).
Proof. exact (MK_COMB (@lem5480961) (@lem5480960 n d)). Qed.
Lemma lem5480963 (n : nat) (x : nat) (d : nat) : (term329 n x d) = (term348 n x d).
Proof. exact (MK_COMB (@lem5480962 n d) (@lem5480927 n x d)). Qed.
Lemma lem5480964 (n : nat) (x : nat) : (term331 n x) = (term349 n x).
Proof. exact (fun_ext (fun d : nat => @lem5480963 n x d)). Qed.
Lemma lem5480965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480966 (n : nat) (x : nat) : (term332 n x) = (term350 n x).
Proof. exact (MK_COMB (@lem5480965) (@lem5480964 n x)). Qed.
Lemma lem5480967 (n : nat) : (term335 n) = (term351 n).
Proof. exact (fun_ext (fun x : nat => @lem5480966 n x)). Qed.
Lemma lem5480968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480969 (n : nat) : (term336 n) = (term352 n).
Proof. exact (MK_COMB (@lem5480968) (@lem5480967 n)). Qed.
Lemma lem5480976 (n : nat) : (term319 n) = (term319 n).
Proof. exact (eq_refl (term319 n)). Qed.
Lemma lem5480977 (n : nat) : (term337 n) = (term353 n).
Proof. exact (MK_COMB (@lem5480976 n) (@lem5480969 n)). Qed.
Lemma lem5480978 (n : nat) : (term302 n) = (term353 n).
Proof. exact (TRANS (@lem5480876 n) (@lem5480977 n)). Qed.
Lemma lem5480980 {A : Type'} (P : Prop) (Q : A -> Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5480981 (P : Prop) (Q : nat -> Prop) : (term80 P Q) = (term81 P Q).
Proof. exact (@lem5480980 nat P Q). Qed.
Lemma lem5480982 (n : nat) : (term354 n) = (term355 n).
Proof. exact (@lem5480981 (n = (NUMERAL 0)) (term351 n)). Qed.
Lemma lem5480983 (n : nat) (x : nat) : (term356 n x) = (term350 n x).
Proof. exact (eq_refl (term356 n x)). Qed.
Lemma lem5480984 (n : nat) : (term357 n) = (term351 n).
Proof. exact (fun_ext (fun x : nat => @lem5480983 n x)). Qed.
Lemma lem5480985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480986 (n : nat) : (term358 n) = (term352 n).
Proof. exact (MK_COMB (@lem5480985) (@lem5480984 n)). Qed.
Lemma lem5480987 (n : nat) : (term319 n) = (term319 n).
Proof. exact (eq_refl (term319 n)). Qed.
Lemma lem5480988 (n : nat) : (term354 n) = (term353 n).
Proof. exact (MK_COMB (@lem5480987 n) (@lem5480986 n)). Qed.
Lemma lem5480989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5480990 (n : nat) : (term359 n) = (term360 n).
Proof. exact (MK_COMB (@lem5480989) (@lem5480988 n)). Qed.
Lemma lem5480991 (n : nat) (x : nat) : (term356 n x) = (term350 n x).
Proof. exact (eq_refl (term356 n x)). Qed.
Lemma lem5480992 (n : nat) : (term319 n) = (term319 n).
Proof. exact (eq_refl (term319 n)). Qed.
Lemma lem5480993 (n : nat) (x : nat) : (term361 n x) = (term362 n x).
Proof. exact (MK_COMB (@lem5480992 n) (@lem5480991 n x)). Qed.
Lemma lem5480994 (n : nat) : (term363 n) = (term364 n).
Proof. exact (fun_ext (fun x : nat => @lem5480993 n x)). Qed.
Lemma lem5480995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5480996 (n : nat) : (term355 n) = (term365 n).
Proof. exact (MK_COMB (@lem5480995) (@lem5480994 n)). Qed.
Lemma lem5480997 (n : nat) : ((term354 n) = (term355 n)) = ((term353 n) = (term365 n)).
Proof. exact (MK_COMB (@lem5480990 n) (@lem5480996 n)). Qed.
Lemma lem5480998 (n : nat) : (term353 n) = (term365 n).
Proof. exact (EQ_MP (@lem5480997 n) (@lem5480982 n)). Qed.
Lemma lem5481000 {A : Type'} (P : Prop) (Q : A -> Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5481001 (P : Prop) (Q : nat -> Prop) : (term80 P Q) = (term81 P Q).
Proof. exact (@lem5481000 nat P Q). Qed.
Lemma lem5481002 (n : nat) (x : nat) : (term366 n x) = (term367 n x).
Proof. exact (@lem5481001 (n = (NUMERAL 0)) (term349 n x)). Qed.
Lemma lem5481003 (n : nat) (x : nat) (d : nat) : (term368 n x d) = (term348 n x d).
Proof. exact (eq_refl (term368 n x d)). Qed.
Lemma lem5481004 (n : nat) (x : nat) : (term369 n x) = (term349 n x).
Proof. exact (fun_ext (fun d : nat => @lem5481003 n x d)). Qed.
Lemma lem5481005 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5481006 (n : nat) (x : nat) : (term370 n x) = (term350 n x).
Proof. exact (MK_COMB (@lem5481005) (@lem5481004 n x)). Qed.
Lemma lem5481007 (n : nat) : (term319 n) = (term319 n).
Proof. exact (eq_refl (term319 n)). Qed.
Lemma lem5481008 (n : nat) (x : nat) : (term366 n x) = (term362 n x).
Proof. exact (MK_COMB (@lem5481007 n) (@lem5481006 n x)). Qed.
Lemma lem5481009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5481010 (n : nat) (x : nat) : (term371 n x) = (term372 n x).
Proof. exact (MK_COMB (@lem5481009) (@lem5481008 n x)). Qed.
Lemma lem5481011 (n : nat) (x : nat) (d : nat) : (term368 n x d) = (term348 n x d).
Proof. exact (eq_refl (term368 n x d)). Qed.
Lemma lem5481012 (n : nat) : (term319 n) = (term319 n).
Proof. exact (eq_refl (term319 n)). Qed.
Lemma lem5481013 (n : nat) (x : nat) (d : nat) : (term373 n x d) = (term374 n x d).
Proof. exact (MK_COMB (@lem5481012 n) (@lem5481011 n x d)). Qed.
Lemma lem5481014 (n : nat) (x : nat) : (term375 n x) = (term376 n x).
Proof. exact (fun_ext (fun d : nat => @lem5481013 n x d)). Qed.
Lemma lem5481015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5481016 (n : nat) (x : nat) : (term367 n x) = (term377 n x).
Proof. exact (MK_COMB (@lem5481015) (@lem5481014 n x)). Qed.
Lemma lem5481017 (n : nat) (x : nat) : ((term366 n x) = (term367 n x)) = ((term362 n x) = (term377 n x)).
Proof. exact (MK_COMB (@lem5481010 n x) (@lem5481016 n x)). Qed.
Lemma lem5481018 (n : nat) (x : nat) : (term362 n x) = (term377 n x).
Proof. exact (EQ_MP (@lem5481017 n x) (@lem5481002 n x)). Qed.
Lemma lem5481019 (n : nat) : (term364 n) = (term378 n).
Proof. exact (fun_ext (fun x : nat => @lem5481018 n x)). Qed.
Lemma lem5481020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5481021 (n : nat) : (term365 n) = (term379 n).
Proof. exact (MK_COMB (@lem5481020) (@lem5481019 n)). Qed.
Lemma lem5481022 (n : nat) : (term353 n) = (term379 n).
Proof. exact (TRANS (@lem5480998 n) (@lem5481021 n)). Qed.
Lemma lem5481023 (n : nat) : (term302 n) = (term379 n).
Proof. exact (TRANS (@lem5480978 n) (@lem5481022 n)). Qed.
Lemma lem5481025 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5481026 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term94).
Proof. exact (@lem5481025 n (NUMERAL 0)). Qed.
Lemma lem5481029 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481030 (n : nat) : (term319 n) = (term380 n).
Proof. exact (MK_COMB (@lem5481029) (@lem5481026 n)). Qed.
Lemma lem5481032 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5481033 (n : nat) (d : nat) : (n = (term340 d)) = ((int_of_num n) = (term381 d)).
Proof. exact (@lem5481032 n (term340 d)). Qed.
Lemma lem5481037 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5481038 (d : nat) : (term381 d) = (term384 d).
Proof. exact (@lem5481037 d term144). Qed.
Lemma lem5481039 (n : nat) : (term385 n) = (term385 n).
Proof. exact (eq_refl (term385 n)). Qed.
Lemma lem5481040 (n : nat) (d : nat) : ((int_of_num n) = (term381 d)) = ((int_of_num n) = (term384 d)).
Proof. exact (MK_COMB (@lem5481039 n) (@lem5481038 d)). Qed.
Lemma lem5481041 (n : nat) (d : nat) : (n = (term340 d)) = ((int_of_num n) = (term384 d)).
Proof. exact (TRANS (@lem5481033 n d) (@lem5481040 n d)). Qed.
Lemma lem5481042 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5481043 (n : nat) (d : nat) : (term342 n d) = (term386 n d).
Proof. exact (MK_COMB (@lem5481042) (@lem5481041 n d)). Qed.
Lemma lem5481044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481045 (n : nat) (d : nat) : (term344 n d) = (term387 n d).
Proof. exact (MK_COMB (@lem5481044) (@lem5481043 n d)). Qed.
Lemma lem5481047 (m : nat) (n : nat) : (Peano.lt m n) = (term97 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5481048 (n : nat) : (term388 n) = (term389 n).
Proof. exact (@lem5481047 n term144). Qed.
Lemma lem5481049 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5481050 (n : nat) : (term390 n) = (term391 n).
Proof. exact (MK_COMB (@lem5481049) (@lem5481048 n)). Qed.
Lemma lem5481051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481052 (n : nat) : (term392 n) = (term393 n).
Proof. exact (MK_COMB (@lem5481051) (@lem5481050 n)). Qed.
Lemma lem5481054 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5481055 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term94).
Proof. exact (@lem5481054 d (NUMERAL 0)). Qed.
Lemma lem5481058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5481059 (d : nat) : (term42 d) = (term95 d).
Proof. exact (MK_COMB (@lem5481058) (@lem5481055 d)). Qed.
Lemma lem5481060 (n : nat) (d : nat) : (term338 n d) = (term394 n d).
Proof. exact (MK_COMB (@lem5481052 n) (@lem5481059 d)). Qed.
Lemma lem5481061 (n : nat) (d : nat) : (term346 n d) = (term395 n d).
Proof. exact (MK_COMB (@lem5481045 n d) (@lem5481060 n d)). Qed.
Lemma lem5481062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481063 (n : nat) (d : nat) : (term347 n d) = (term396 n d).
Proof. exact (MK_COMB (@lem5481062) (@lem5481061 n d)). Qed.
Lemma lem5481065 (m : nat) (n : nat) : (Peano.lt m n) = (term97 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5481066 (x : nat) (n : nat) : (Peano.lt x n) = (term97 x n).
Proof. exact (@lem5481065 x n). Qed.
Lemma lem5481067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481068 (x : nat) (n : nat) : (term309 x n) = (term397 x n).
Proof. exact (MK_COMB (@lem5481067) (@lem5481066 x n)). Qed.
Lemma lem5481070 (m : nat) (n : nat) : (Peano.le m n) = (term398 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5481071 (x : nat) : (term306 x) = (term103 x).
Proof. exact (@lem5481070 (NUMERAL 0) x). Qed.
Lemma lem5481072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5481073 (x : nat) : (term399 x) = (term400 x).
Proof. exact (MK_COMB (@lem5481072) (@lem5481071 x)). Qed.
Lemma lem5481074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481075 (x : nat) : (term401 x) = (term402 x).
Proof. exact (MK_COMB (@lem5481074) (@lem5481073 x)). Qed.
Lemma lem5481077 (m : nat) (n : nat) : (Peano.le m n) = (term398 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5481078 (x : nat) (d : nat) : (Peano.le x d) = (term398 x d).
Proof. exact (@lem5481077 x d). Qed.
Lemma lem5481079 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5481080 (x : nat) (d : nat) : (term403 x d) = (term404 x d).
Proof. exact (MK_COMB (@lem5481079) (@lem5481078 x d)). Qed.
Lemma lem5481081 (x : nat) (d : nat) : (term405 x d) = (term406 x d).
Proof. exact (MK_COMB (@lem5481075 x) (@lem5481080 x d)). Qed.
Lemma lem5481082 (n : nat) (x : nat) (d : nat) : (term407 n x d) = (term408 n x d).
Proof. exact (MK_COMB (@lem5481068 x n) (@lem5481081 x d)). Qed.
Lemma lem5481083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481084 (n : nat) (x : nat) (d : nat) : (term409 n x d) = (term410 n x d).
Proof. exact (MK_COMB (@lem5481083) (@lem5481082 n x d)). Qed.
Lemma lem5481086 (m : nat) (n : nat) : (Peano.lt m n) = (term97 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5481087 (x : nat) (n : nat) : (Peano.lt x n) = (term97 x n).
Proof. exact (@lem5481086 x n). Qed.
Lemma lem5481088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5481089 (x : nat) (n : nat) : (term64 x n) = (term98 x n).
Proof. exact (MK_COMB (@lem5481088) (@lem5481087 x n)). Qed.
Lemma lem5481090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481091 (x : nat) (n : nat) : (term411 x n) = (term412 x n).
Proof. exact (MK_COMB (@lem5481090) (@lem5481089 x n)). Qed.
Lemma lem5481093 (m : nat) (n : nat) : (Peano.le m n) = (term398 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5481094 (x : nat) : (term306 x) = (term103 x).
Proof. exact (@lem5481093 (NUMERAL 0) x). Qed.
Lemma lem5481095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481096 (x : nat) : (term413 x) = (term414 x).
Proof. exact (MK_COMB (@lem5481095) (@lem5481094 x)). Qed.
Lemma lem5481098 (m : nat) (n : nat) : (Peano.le m n) = (term398 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5481099 (x : nat) (d : nat) : (Peano.le x d) = (term398 x d).
Proof. exact (@lem5481098 x d). Qed.
Lemma lem5481100 (x : nat) (d : nat) : (term415 x d) = (term416 x d).
Proof. exact (MK_COMB (@lem5481096 x) (@lem5481099 x d)). Qed.
Lemma lem5481101 (n : nat) (x : nat) (d : nat) : (term417 n x d) = (term418 n x d).
Proof. exact (MK_COMB (@lem5481091 x n) (@lem5481100 x d)). Qed.
Lemma lem5481102 (n : nat) (x : nat) (d : nat) : (term326 n x d) = (term419 n x d).
Proof. exact (MK_COMB (@lem5481084 n x d) (@lem5481101 n x d)). Qed.
Lemma lem5481103 (n : nat) (x : nat) (d : nat) : (term348 n x d) = (term420 n x d).
Proof. exact (MK_COMB (@lem5481063 n d) (@lem5481102 n x d)). Qed.
Lemma lem5481104 (n : nat) (x : nat) (d : nat) : (term374 n x d) = (term421 n x d).
Proof. exact (MK_COMB (@lem5481030 n) (@lem5481103 n x d)). Qed.
Lemma lem5481105 (n : nat) (x : nat) : (term376 n x) = (term422 n x).
Proof. exact (fun_ext (fun d : nat => @lem5481104 n x d)). Qed.
Lemma lem5481106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5481107 (n : nat) (x : nat) : (term377 n x) = (term423 n x).
Proof. exact (MK_COMB (@lem5481106) (@lem5481105 n x)). Qed.
Lemma lem5481108 (n : nat) : (term378 n) = (term424 n).
Proof. exact (fun_ext (fun x : nat => @lem5481107 n x)). Qed.
Lemma lem5481109 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5481110 (n : nat) : (term379 n) = (term425 n).
Proof. exact (MK_COMB (@lem5481109) (@lem5481108 n)). Qed.
Lemma lem5481111 (n : nat) : (term302 n) = (term425 n).
Proof. exact (TRANS (@lem5481023 n) (@lem5481110 n)). Qed.
Lemma lem5481112 (d : nat) : term102 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem5481113 (d : nat) : (term102 d) = (term103 d).
Proof. exact (eq_refl (term102 d)). Qed.
Lemma lem5481114 (d : nat) : term103 d.
Proof. exact (EQ_MP (@lem5481113 d) (@lem5481112 d)). Qed.
Lemma lem5481115 (n : nat) : term102 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5481116 (n : nat) : (term102 n) = (term103 n).
Proof. exact (eq_refl (term102 n)). Qed.
Lemma lem5481117 (n : nat) : term103 n.
Proof. exact (EQ_MP (@lem5481116 n) (@lem5481115 n)). Qed.
Lemma lem5481118 (x : nat) : term102 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5481119 (x : nat) : (term102 x) = (term103 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem5481120 (x : nat) : term103 x.
Proof. exact (EQ_MP (@lem5481119 x) (@lem5481118 x)). Qed.
Lemma lem5481121 (_70607 : int) (_70608 : int) (_70606 : int) : (term426 _70607 _70608 _70606) = (term427 _70607 _70608 _70606).
Proof. exact (@lem2318604 (term427 _70607 _70608 _70606)). Qed.
Lemma lem5481157 (_70607 : int) (_70606 : int) : (term428 _70607 _70606) = (_70607 = (term136 _70606)).
Proof. exact (@lem16933 (_70607 = (term136 _70606))). Qed.
Lemma lem5481160 (_70607 : int) : (term429 _70607) = (term430 _70607).
Proof. exact (@lem16933 (term430 _70607)). Qed.
Lemma lem5481163 (_70606 : int) : (term106 _70606) = (_70606 = term94).
Proof. exact (@lem16933 (_70606 = term94)). Qed.
Lemma lem5481164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481165 (_70607 : int) : (term431 _70607) = (term432 _70607).
Proof. exact (MK_COMB (@lem5481164) (@lem5481160 _70607)). Qed.
Lemma lem5481166 (_70607 : int) (_70606 : int) : (term433 _70607 _70606) = (term434 _70607 _70606).
Proof. exact (MK_COMB (@lem5481165 _70607) (@lem5481163 _70606)). Qed.
Lemma lem5481167 (_70607 : int) (_70606 : int) : (term435 _70607 _70606) = (term433 _70607 _70606).
Proof. exact (@lem17160 (term436 _70607) (term113 _70606)). Qed.
Lemma lem5481168 (_70607 : int) (_70606 : int) : (term435 _70607 _70606) = (term434 _70607 _70606).
Proof. exact (TRANS (@lem5481167 _70607 _70606) (@lem5481166 _70607 _70606)). Qed.
Lemma lem5481169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481170 (_70607 : int) (_70606 : int) : (term437 _70607 _70606) = (term438 _70607 _70606).
Proof. exact (MK_COMB (@lem5481169) (@lem5481157 _70607 _70606)). Qed.
Lemma lem5481171 (_70607 : int) (_70606 : int) : (term439 _70607 _70606) = (term440 _70607 _70606).
Proof. exact (MK_COMB (@lem5481170 _70607 _70606) (@lem5481168 _70607 _70606)). Qed.
Lemma lem5481172 (_70607 : int) (_70606 : int) : (term441 _70607 _70606) = (term439 _70607 _70606).
Proof. exact (@lem17045 (term442 _70607 _70606) (term443 _70607 _70606)). Qed.
Lemma lem5481173 (_70607 : int) (_70606 : int) : (term441 _70607 _70606) = (term440 _70607 _70606).
Proof. exact (TRANS (@lem5481172 _70607 _70606) (@lem5481171 _70607 _70606)). Qed.
Lemma lem5481177 (_70608 : int) : (term444 _70608) = (term119 _70608).
Proof. exact (@lem16933 (term119 _70608)). Qed.
Lemma lem5481180 (_70608 : int) (_70606 : int) : (term445 _70608 _70606) = (int_le _70608 _70606).
Proof. exact (@lem16933 (int_le _70608 _70606)). Qed.
Lemma lem5481181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481182 (_70608 : int) : (term446 _70608) = (term115 _70608).
Proof. exact (MK_COMB (@lem5481181) (@lem5481177 _70608)). Qed.
Lemma lem5481183 (_70608 : int) (_70606 : int) : (term447 _70608 _70606) = (term448 _70608 _70606).
Proof. exact (MK_COMB (@lem5481182 _70608) (@lem5481180 _70608 _70606)). Qed.
Lemma lem5481184 (_70608 : int) (_70606 : int) : (term449 _70608 _70606) = (term447 _70608 _70606).
Proof. exact (@lem17160 (term450 _70608) (term451 _70608 _70606)). Qed.
Lemma lem5481185 (_70608 : int) (_70606 : int) : (term449 _70608 _70606) = (term448 _70608 _70606).
Proof. exact (TRANS (@lem5481184 _70608 _70606) (@lem5481183 _70608 _70606)). Qed.
Lemma lem5481187 (_70608 : int) (_70607 : int) : (term452 _70608 _70607) = (term452 _70608 _70607).
Proof. exact (eq_refl (term452 _70608 _70607)). Qed.
Lemma lem5481188 (_70607 : int) (_70608 : int) (_70606 : int) : (term453 _70607 _70608 _70606) = (term454 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481187 _70608 _70607) (@lem5481185 _70608 _70606)). Qed.
Lemma lem5481189 (_70607 : int) (_70608 : int) (_70606 : int) : (term455 _70607 _70608 _70606) = (term453 _70607 _70608 _70606).
Proof. exact (@lem17160 (int_lt _70608 _70607) (term456 _70608 _70606)). Qed.
Lemma lem5481190 (_70607 : int) (_70608 : int) (_70606 : int) : (term455 _70607 _70608 _70606) = (term454 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481189 _70607 _70608 _70606) (@lem5481188 _70607 _70608 _70606)). Qed.
Lemma lem5481193 (_70608 : int) (_70607 : int) : (term107 _70608 _70607) = (int_lt _70608 _70607).
Proof. exact (@lem16933 (int_lt _70608 _70607)). Qed.
Lemma lem5481200 (_70608 : int) (_70606 : int) : (term457 _70608 _70606) = (term456 _70608 _70606).
Proof. exact (@lem17045 (term119 _70608) (int_le _70608 _70606)). Qed.
Lemma lem5481201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481202 (_70608 : int) (_70607 : int) : (term458 _70608 _70607) = (term459 _70608 _70607).
Proof. exact (MK_COMB (@lem5481201) (@lem5481193 _70608 _70607)). Qed.
Lemma lem5481203 (_70607 : int) (_70608 : int) (_70606 : int) : (term460 _70607 _70608 _70606) = (term461 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481202 _70608 _70607) (@lem5481200 _70608 _70606)). Qed.
Lemma lem5481204 (_70607 : int) (_70608 : int) (_70606 : int) : (term462 _70607 _70608 _70606) = (term460 _70607 _70608 _70606).
Proof. exact (@lem17160 (term114 _70608 _70607) (term448 _70608 _70606)). Qed.
Lemma lem5481205 (_70607 : int) (_70608 : int) (_70606 : int) : (term462 _70607 _70608 _70606) = (term461 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481204 _70607 _70608 _70606) (@lem5481203 _70607 _70608 _70606)). Qed.
Lemma lem5481206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481207 (_70607 : int) (_70608 : int) (_70606 : int) : (term463 _70607 _70608 _70606) = (term464 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481206) (@lem5481190 _70607 _70608 _70606)). Qed.
Lemma lem5481208 (_70607 : int) (_70608 : int) (_70606 : int) : (term465 _70607 _70608 _70606) = (term466 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481207 _70607 _70608 _70606) (@lem5481205 _70607 _70608 _70606)). Qed.
Lemma lem5481209 (_70607 : int) (_70608 : int) (_70606 : int) : (term467 _70607 _70608 _70606) = (term465 _70607 _70608 _70606).
Proof. exact (@lem17045 (term468 _70607 _70608 _70606) (term469 _70607 _70608 _70606)). Qed.
Lemma lem5481210 (_70607 : int) (_70608 : int) (_70606 : int) : (term467 _70607 _70608 _70606) = (term466 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481209 _70607 _70608 _70606) (@lem5481208 _70607 _70608 _70606)). Qed.
Lemma lem5481211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481212 (_70607 : int) (_70606 : int) : (term470 _70607 _70606) = (term471 _70607 _70606).
Proof. exact (MK_COMB (@lem5481211) (@lem5481173 _70607 _70606)). Qed.
Lemma lem5481213 (_70607 : int) (_70608 : int) (_70606 : int) : (term472 _70607 _70608 _70606) = (term473 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481212 _70607 _70606) (@lem5481210 _70607 _70608 _70606)). Qed.
Lemma lem5481214 (_70607 : int) (_70608 : int) (_70606 : int) : (term474 _70607 _70608 _70606) = (term472 _70607 _70608 _70606).
Proof. exact (@lem17160 (term475 _70607 _70606) (term476 _70607 _70608 _70606)). Qed.
Lemma lem5481215 (_70607 : int) (_70608 : int) (_70606 : int) : (term474 _70607 _70608 _70606) = (term473 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481214 _70607 _70608 _70606) (@lem5481213 _70607 _70608 _70606)). Qed.
Lemma lem5481217 (_70607 : int) : (term477 _70607) = (term477 _70607).
Proof. exact (eq_refl (term477 _70607)). Qed.
Lemma lem5481218 (_70607 : int) (_70608 : int) (_70606 : int) : (term478 _70607 _70608 _70606) = (term479 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481217 _70607) (@lem5481215 _70607 _70608 _70606)). Qed.
Lemma lem5481219 (_70607 : int) (_70608 : int) (_70606 : int) : (term480 _70607 _70608 _70606) = (term478 _70607 _70608 _70606).
Proof. exact (@lem17160 (_70607 = term94) (term481 _70607 _70608 _70606)). Qed.
Lemma lem5481220 (_70607 : int) (_70608 : int) (_70606 : int) : (term480 _70607 _70608 _70606) = (term479 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481219 _70607 _70608 _70606) (@lem5481218 _70607 _70608 _70606)). Qed.
Lemma lem5481222 (_70608 : int) : (term115 _70608) = (term115 _70608).
Proof. exact (eq_refl (term115 _70608)). Qed.
Lemma lem5481223 (_70607 : int) (_70608 : int) (_70606 : int) : (term482 _70607 _70608 _70606) = (term483 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481222 _70608) (@lem5481220 _70607 _70608 _70606)). Qed.
Lemma lem5481224 (_70607 : int) (_70608 : int) (_70606 : int) : (term484 _70607 _70608 _70606) = (term482 _70607 _70608 _70606).
Proof. exact (@lem17362 (term119 _70608) (term485 _70607 _70608 _70606)). Qed.
Lemma lem5481225 (_70607 : int) (_70608 : int) (_70606 : int) : (term484 _70607 _70608 _70606) = (term483 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481224 _70607 _70608 _70606) (@lem5481223 _70607 _70608 _70606)). Qed.
Lemma lem5481227 (_70607 : int) : (term115 _70607) = (term115 _70607).
Proof. exact (eq_refl (term115 _70607)). Qed.
Lemma lem5481228 (_70607 : int) (_70608 : int) (_70606 : int) : (term486 _70607 _70608 _70606) = (term487 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481227 _70607) (@lem5481225 _70607 _70608 _70606)). Qed.
Lemma lem5481229 (_70607 : int) (_70608 : int) (_70606 : int) : (term488 _70607 _70608 _70606) = (term486 _70607 _70608 _70606).
Proof. exact (@lem17362 (term119 _70607) (term489 _70607 _70608 _70606)). Qed.
Lemma lem5481230 (_70607 : int) (_70608 : int) (_70606 : int) : (term488 _70607 _70608 _70606) = (term487 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481229 _70607 _70608 _70606) (@lem5481228 _70607 _70608 _70606)). Qed.
Lemma lem5481232 (_70606 : int) : (term115 _70606) = (term115 _70606).
Proof. exact (eq_refl (term115 _70606)). Qed.
Lemma lem5481233 (_70607 : int) (_70608 : int) (_70606 : int) : (term490 _70607 _70608 _70606) = (term491 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481232 _70606) (@lem5481230 _70607 _70608 _70606)). Qed.
Lemma lem5481234 (_70607 : int) (_70608 : int) (_70606 : int) : (term492 _70607 _70608 _70606) = (term490 _70607 _70608 _70606).
Proof. exact (@lem17362 (term119 _70606) (term493 _70607 _70608 _70606)). Qed.
Lemma lem5481294 (_70607 : int) (_70608 : int) (_70606 : int) : (term492 _70607 _70608 _70606) = (term491 _70607 _70608 _70606).
Proof. exact (TRANS (@lem5481234 _70607 _70608 _70606) (@lem5481233 _70607 _70608 _70606)). Qed.
Lemma lem5481297 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481298 (_70606 : int) : (term119 _70606) = (term126 _70606).
Proof. exact (@lem5481297 term94 _70606). Qed.
Lemma lem5481300 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481301 : term128 = term129.
Proof. exact (@lem5481300 (NUMERAL 0)). Qed.
Lemma lem5481302 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481303 : term130 = term131.
Proof. exact (MK_COMB (@lem5481302) (@lem5481301)). Qed.
Lemma lem5481304 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5481305 (_70606 : int) : (term126 _70606) = (term132 _70606).
Proof. exact (MK_COMB (@lem5481303) (@lem5481304 _70606)). Qed.
Lemma lem5481307 (_70606 : int) : (term119 _70606) = (term132 _70606).
Proof. exact (TRANS (@lem5481298 _70606) (@lem5481305 _70606)). Qed.
Lemma lem5481310 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481311 (_70607 : int) : (term119 _70607) = (term126 _70607).
Proof. exact (@lem5481310 term94 _70607). Qed.
Lemma lem5481313 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481314 : term128 = term129.
Proof. exact (@lem5481313 (NUMERAL 0)). Qed.
Lemma lem5481315 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481316 : term130 = term131.
Proof. exact (MK_COMB (@lem5481315) (@lem5481314)). Qed.
Lemma lem5481317 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5481318 (_70607 : int) : (term126 _70607) = (term132 _70607).
Proof. exact (MK_COMB (@lem5481316) (@lem5481317 _70607)). Qed.
Lemma lem5481320 (_70607 : int) : (term119 _70607) = (term132 _70607).
Proof. exact (TRANS (@lem5481311 _70607) (@lem5481318 _70607)). Qed.
Lemma lem5481323 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481324 (_70608 : int) : (term119 _70608) = (term126 _70608).
Proof. exact (@lem5481323 term94 _70608). Qed.
Lemma lem5481326 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481327 : term128 = term129.
Proof. exact (@lem5481326 (NUMERAL 0)). Qed.
Lemma lem5481328 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481329 : term130 = term131.
Proof. exact (MK_COMB (@lem5481328) (@lem5481327)). Qed.
Lemma lem5481330 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5481331 (_70608 : int) : (term126 _70608) = (term132 _70608).
Proof. exact (MK_COMB (@lem5481329) (@lem5481330 _70608)). Qed.
Lemma lem5481333 (_70608 : int) : (term119 _70608) = (term132 _70608).
Proof. exact (TRANS (@lem5481324 _70608) (@lem5481331 _70608)). Qed.
Lemma lem5481335 (y : int) (x : int) : (term494 x y) = (term495 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5481336 (_70607 : int) : (term113 _70607) = (term496 _70607).
Proof. exact (@lem5481335 term94 _70607). Qed.
Lemma lem5481338 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481339 (_70607 : int) : (term497 _70607) = (term498 _70607).
Proof. exact (@lem5481338 (term136 _70607) term94). Qed.
Lemma lem5481341 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5481342 (_70607 : int) : (term139 _70607) = (term140 _70607).
Proof. exact (@lem5481341 _70607 term141). Qed.
Lemma lem5481344 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481345 : term142 = term143.
Proof. exact (@lem5481344 term144). Qed.
Lemma lem5481346 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5481347 (_70607 : int) : (term140 _70607) = (term146 _70607).
Proof. exact (MK_COMB (@lem5481346 _70607) (@lem5481345)). Qed.
Lemma lem5481348 (_70607 : int) : (term139 _70607) = (term146 _70607).
Proof. exact (TRANS (@lem5481342 _70607) (@lem5481347 _70607)). Qed.
Lemma lem5481349 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481350 (_70607 : int) : (term147 _70607) = (term148 _70607).
Proof. exact (MK_COMB (@lem5481349) (@lem5481348 _70607)). Qed.
Lemma lem5481352 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481353 : term128 = term129.
Proof. exact (@lem5481352 (NUMERAL 0)). Qed.
Lemma lem5481354 (_70607 : int) : (term498 _70607) = (term499 _70607).
Proof. exact (MK_COMB (@lem5481350 _70607) (@lem5481353)). Qed.
Lemma lem5481355 (_70607 : int) : (term497 _70607) = (term499 _70607).
Proof. exact (TRANS (@lem5481339 _70607) (@lem5481354 _70607)). Qed.
Lemma lem5481356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481357 (_70607 : int) : (term500 _70607) = (term501 _70607).
Proof. exact (MK_COMB (@lem5481356) (@lem5481355 _70607)). Qed.
Lemma lem5481359 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481360 (_70607 : int) : (term502 _70607) = (term503 _70607).
Proof. exact (@lem5481359 term504 _70607). Qed.
Lemma lem5481362 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5481363 : term505 = term506.
Proof. exact (@lem5481362 term94 term141). Qed.
Lemma lem5481365 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481366 : term128 = term129.
Proof. exact (@lem5481365 (NUMERAL 0)). Qed.
Lemma lem5481367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5481368 : term507 = term266.
Proof. exact (MK_COMB (@lem5481367) (@lem5481366)). Qed.
Lemma lem5481370 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481371 : term142 = term143.
Proof. exact (@lem5481370 term144). Qed.
Lemma lem5481372 : term506 = term508.
Proof. exact (MK_COMB (@lem5481368) (@lem5481371)). Qed.
Lemma lem5481373 : term505 = term508.
Proof. exact (TRANS (@lem5481363) (@lem5481372)). Qed.
Lemma lem5481374 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481375 : term509 = term510.
Proof. exact (MK_COMB (@lem5481374) (@lem5481373)). Qed.
Lemma lem5481376 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5481377 (_70607 : int) : (term503 _70607) = (term511 _70607).
Proof. exact (MK_COMB (@lem5481375) (@lem5481376 _70607)). Qed.
Lemma lem5481378 (_70607 : int) : (term502 _70607) = (term511 _70607).
Proof. exact (TRANS (@lem5481360 _70607) (@lem5481377 _70607)). Qed.
Lemma lem5481379 (_70607 : int) : (term496 _70607) = (term512 _70607).
Proof. exact (MK_COMB (@lem5481357 _70607) (@lem5481378 _70607)). Qed.
Lemma lem5481380 (_70607 : int) : (term113 _70607) = (term512 _70607).
Proof. exact (TRANS (@lem5481336 _70607) (@lem5481379 _70607)). Qed.
Lemma lem5481383 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5481384 (_70607 : int) (_70606 : int) : (_70607 = (term136 _70606)) = ((real_of_int _70607) = (term139 _70606)).
Proof. exact (@lem5481383 _70607 (term136 _70606)). Qed.
Lemma lem5481388 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5481389 (_70606 : int) : (term139 _70606) = (term140 _70606).
Proof. exact (@lem5481388 _70606 term141). Qed.
Lemma lem5481391 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481392 : term142 = term143.
Proof. exact (@lem5481391 term144). Qed.
Lemma lem5481393 (_70606 : int) : (term145 _70606) = (term145 _70606).
Proof. exact (eq_refl (term145 _70606)). Qed.
Lemma lem5481394 (_70606 : int) : (term140 _70606) = (term146 _70606).
Proof. exact (MK_COMB (@lem5481393 _70606) (@lem5481392)). Qed.
Lemma lem5481395 (_70606 : int) : (term139 _70606) = (term146 _70606).
Proof. exact (TRANS (@lem5481389 _70606) (@lem5481394 _70606)). Qed.
Lemma lem5481396 (_70607 : int) : (term133 _70607) = (term133 _70607).
Proof. exact (eq_refl (term133 _70607)). Qed.
Lemma lem5481397 (_70607 : int) (_70606 : int) : ((real_of_int _70607) = (term139 _70606)) = ((real_of_int _70607) = (term146 _70606)).
Proof. exact (MK_COMB (@lem5481396 _70607) (@lem5481395 _70606)). Qed.
Lemma lem5481399 (_70607 : int) (_70606 : int) : (_70607 = (term136 _70606)) = ((real_of_int _70607) = (term146 _70606)).
Proof. exact (TRANS (@lem5481384 _70607 _70606) (@lem5481397 _70607 _70606)). Qed.
Lemma lem5481401 (x : int) (y : int) : (int_lt x y) = (term134 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5481402 (_70607 : int) : (term430 _70607) = (term513 _70607).
Proof. exact (@lem5481401 _70607 term141). Qed.
Lemma lem5481404 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481405 (_70607 : int) : (term513 _70607) = (term514 _70607).
Proof. exact (@lem5481404 (term136 _70607) term141). Qed.
Lemma lem5481407 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5481408 (_70607 : int) : (term139 _70607) = (term140 _70607).
Proof. exact (@lem5481407 _70607 term141). Qed.
Lemma lem5481410 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481411 : term142 = term143.
Proof. exact (@lem5481410 term144). Qed.
Lemma lem5481412 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5481413 (_70607 : int) : (term140 _70607) = (term146 _70607).
Proof. exact (MK_COMB (@lem5481412 _70607) (@lem5481411)). Qed.
Lemma lem5481414 (_70607 : int) : (term139 _70607) = (term146 _70607).
Proof. exact (TRANS (@lem5481408 _70607) (@lem5481413 _70607)). Qed.
Lemma lem5481415 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481416 (_70607 : int) : (term147 _70607) = (term148 _70607).
Proof. exact (MK_COMB (@lem5481415) (@lem5481414 _70607)). Qed.
Lemma lem5481418 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481419 : term142 = term143.
Proof. exact (@lem5481418 term144). Qed.
Lemma lem5481420 (_70607 : int) : (term514 _70607) = (term515 _70607).
Proof. exact (MK_COMB (@lem5481416 _70607) (@lem5481419)). Qed.
Lemma lem5481421 (_70607 : int) : (term513 _70607) = (term515 _70607).
Proof. exact (TRANS (@lem5481405 _70607) (@lem5481420 _70607)). Qed.
Lemma lem5481422 (_70607 : int) : (term430 _70607) = (term515 _70607).
Proof. exact (TRANS (@lem5481402 _70607) (@lem5481421 _70607)). Qed.
Lemma lem5481425 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5481426 (_70606 : int) : (_70606 = term94) = ((real_of_int _70606) = term128).
Proof. exact (@lem5481425 _70606 term94). Qed.
Lemma lem5481430 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481431 : term128 = term129.
Proof. exact (@lem5481430 (NUMERAL 0)). Qed.
Lemma lem5481432 (_70606 : int) : (term133 _70606) = (term133 _70606).
Proof. exact (eq_refl (term133 _70606)). Qed.
Lemma lem5481433 (_70606 : int) : ((real_of_int _70606) = term128) = ((real_of_int _70606) = term129).
Proof. exact (MK_COMB (@lem5481432 _70606) (@lem5481431)). Qed.
Lemma lem5481435 (_70606 : int) : (_70606 = term94) = ((real_of_int _70606) = term129).
Proof. exact (TRANS (@lem5481426 _70606) (@lem5481433 _70606)). Qed.
Lemma lem5481436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481437 (_70607 : int) : (term432 _70607) = (term516 _70607).
Proof. exact (MK_COMB (@lem5481436) (@lem5481422 _70607)). Qed.
Lemma lem5481438 (_70607 : int) (_70606 : int) : (term434 _70607 _70606) = (term517 _70607 _70606).
Proof. exact (MK_COMB (@lem5481437 _70607) (@lem5481435 _70606)). Qed.
Lemma lem5481439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481440 (_70607 : int) (_70606 : int) : (term438 _70607 _70606) = (term518 _70607 _70606).
Proof. exact (MK_COMB (@lem5481439) (@lem5481399 _70607 _70606)). Qed.
Lemma lem5481441 (_70607 : int) (_70606 : int) : (term440 _70607 _70606) = (term519 _70607 _70606).
Proof. exact (MK_COMB (@lem5481440 _70607 _70606) (@lem5481438 _70607 _70606)). Qed.
Lemma lem5481443 (y : int) (x : int) : (term114 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem5481444 (_70607 : int) (_70608 : int) : (term114 _70608 _70607) = (int_le _70607 _70608).
Proof. exact (@lem5481443 _70607 _70608). Qed.
Lemma lem5481446 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481447 (_70607 : int) (_70608 : int) : (int_le _70607 _70608) = (term125 _70607 _70608).
Proof. exact (@lem5481446 _70607 _70608). Qed.
Lemma lem5481448 (_70607 : int) (_70608 : int) : (term114 _70608 _70607) = (term125 _70607 _70608).
Proof. exact (TRANS (@lem5481444 _70607 _70608) (@lem5481447 _70607 _70608)). Qed.
Lemma lem5481451 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481452 (_70608 : int) : (term119 _70608) = (term126 _70608).
Proof. exact (@lem5481451 term94 _70608). Qed.
Lemma lem5481454 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481455 : term128 = term129.
Proof. exact (@lem5481454 (NUMERAL 0)). Qed.
Lemma lem5481456 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481457 : term130 = term131.
Proof. exact (MK_COMB (@lem5481456) (@lem5481455)). Qed.
Lemma lem5481458 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5481459 (_70608 : int) : (term126 _70608) = (term132 _70608).
Proof. exact (MK_COMB (@lem5481457) (@lem5481458 _70608)). Qed.
Lemma lem5481461 (_70608 : int) : (term119 _70608) = (term132 _70608).
Proof. exact (TRANS (@lem5481452 _70608) (@lem5481459 _70608)). Qed.
Lemma lem5481464 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481466 (_70608 : int) (_70606 : int) : (int_le _70608 _70606) = (term125 _70608 _70606).
Proof. exact (@lem5481464 _70608 _70606). Qed.
Lemma lem5481467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481468 (_70608 : int) : (term115 _70608) = (term152 _70608).
Proof. exact (MK_COMB (@lem5481467) (@lem5481461 _70608)). Qed.
Lemma lem5481469 (_70608 : int) (_70606 : int) : (term448 _70608 _70606) = (term520 _70608 _70606).
Proof. exact (MK_COMB (@lem5481468 _70608) (@lem5481466 _70608 _70606)). Qed.
Lemma lem5481470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481471 (_70607 : int) (_70608 : int) : (term452 _70608 _70607) = (term521 _70607 _70608).
Proof. exact (MK_COMB (@lem5481470) (@lem5481448 _70607 _70608)). Qed.
Lemma lem5481472 (_70607 : int) (_70608 : int) (_70606 : int) : (term454 _70607 _70608 _70606) = (term522 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481471 _70607 _70608) (@lem5481469 _70608 _70606)). Qed.
Lemma lem5481474 (x : int) (y : int) : (int_lt x y) = (term134 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5481475 (_70608 : int) (_70607 : int) : (int_lt _70608 _70607) = (term134 _70608 _70607).
Proof. exact (@lem5481474 _70608 _70607). Qed.
Lemma lem5481477 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481478 (_70608 : int) (_70607 : int) : (term134 _70608 _70607) = (term135 _70608 _70607).
Proof. exact (@lem5481477 (term136 _70608) _70607). Qed.
Lemma lem5481480 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5481481 (_70608 : int) : (term139 _70608) = (term140 _70608).
Proof. exact (@lem5481480 _70608 term141). Qed.
Lemma lem5481483 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481484 : term142 = term143.
Proof. exact (@lem5481483 term144). Qed.
Lemma lem5481485 (_70608 : int) : (term145 _70608) = (term145 _70608).
Proof. exact (eq_refl (term145 _70608)). Qed.
Lemma lem5481486 (_70608 : int) : (term140 _70608) = (term146 _70608).
Proof. exact (MK_COMB (@lem5481485 _70608) (@lem5481484)). Qed.
Lemma lem5481487 (_70608 : int) : (term139 _70608) = (term146 _70608).
Proof. exact (TRANS (@lem5481481 _70608) (@lem5481486 _70608)). Qed.
Lemma lem5481488 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481489 (_70608 : int) : (term147 _70608) = (term148 _70608).
Proof. exact (MK_COMB (@lem5481488) (@lem5481487 _70608)). Qed.
Lemma lem5481490 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5481491 (_70608 : int) (_70607 : int) : (term135 _70608 _70607) = (term149 _70608 _70607).
Proof. exact (MK_COMB (@lem5481489 _70608) (@lem5481490 _70607)). Qed.
Lemma lem5481492 (_70608 : int) (_70607 : int) : (term134 _70608 _70607) = (term149 _70608 _70607).
Proof. exact (TRANS (@lem5481478 _70608 _70607) (@lem5481491 _70608 _70607)). Qed.
Lemma lem5481493 (_70608 : int) (_70607 : int) : (int_lt _70608 _70607) = (term149 _70608 _70607).
Proof. exact (TRANS (@lem5481475 _70608 _70607) (@lem5481492 _70608 _70607)). Qed.
Lemma lem5481495 (y : int) (x : int) : (term451 x y) = (term134 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5481496 (_70608 : int) : (term450 _70608) = (term497 _70608).
Proof. exact (@lem5481495 _70608 term94). Qed.
Lemma lem5481498 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481499 (_70608 : int) : (term497 _70608) = (term498 _70608).
Proof. exact (@lem5481498 (term136 _70608) term94). Qed.
Lemma lem5481501 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5481502 (_70608 : int) : (term139 _70608) = (term140 _70608).
Proof. exact (@lem5481501 _70608 term141). Qed.
Lemma lem5481504 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481505 : term142 = term143.
Proof. exact (@lem5481504 term144). Qed.
Lemma lem5481506 (_70608 : int) : (term145 _70608) = (term145 _70608).
Proof. exact (eq_refl (term145 _70608)). Qed.
Lemma lem5481507 (_70608 : int) : (term140 _70608) = (term146 _70608).
Proof. exact (MK_COMB (@lem5481506 _70608) (@lem5481505)). Qed.
Lemma lem5481508 (_70608 : int) : (term139 _70608) = (term146 _70608).
Proof. exact (TRANS (@lem5481502 _70608) (@lem5481507 _70608)). Qed.
Lemma lem5481509 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481510 (_70608 : int) : (term147 _70608) = (term148 _70608).
Proof. exact (MK_COMB (@lem5481509) (@lem5481508 _70608)). Qed.
Lemma lem5481512 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481513 : term128 = term129.
Proof. exact (@lem5481512 (NUMERAL 0)). Qed.
Lemma lem5481514 (_70608 : int) : (term498 _70608) = (term499 _70608).
Proof. exact (MK_COMB (@lem5481510 _70608) (@lem5481513)). Qed.
Lemma lem5481515 (_70608 : int) : (term497 _70608) = (term499 _70608).
Proof. exact (TRANS (@lem5481499 _70608) (@lem5481514 _70608)). Qed.
Lemma lem5481516 (_70608 : int) : (term450 _70608) = (term499 _70608).
Proof. exact (TRANS (@lem5481496 _70608) (@lem5481515 _70608)). Qed.
Lemma lem5481518 (y : int) (x : int) : (term451 x y) = (term134 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5481519 (_70606 : int) (_70608 : int) : (term451 _70608 _70606) = (term134 _70606 _70608).
Proof. exact (@lem5481518 _70606 _70608). Qed.
Lemma lem5481521 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5481522 (_70606 : int) (_70608 : int) : (term134 _70606 _70608) = (term135 _70606 _70608).
Proof. exact (@lem5481521 (term136 _70606) _70608). Qed.
Lemma lem5481524 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5481525 (_70606 : int) : (term139 _70606) = (term140 _70606).
Proof. exact (@lem5481524 _70606 term141). Qed.
Lemma lem5481527 (n : nat) : (term127 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5481528 : term142 = term143.
Proof. exact (@lem5481527 term144). Qed.
Lemma lem5481529 (_70606 : int) : (term145 _70606) = (term145 _70606).
Proof. exact (eq_refl (term145 _70606)). Qed.
Lemma lem5481530 (_70606 : int) : (term140 _70606) = (term146 _70606).
Proof. exact (MK_COMB (@lem5481529 _70606) (@lem5481528)). Qed.
Lemma lem5481531 (_70606 : int) : (term139 _70606) = (term146 _70606).
Proof. exact (TRANS (@lem5481525 _70606) (@lem5481530 _70606)). Qed.
Lemma lem5481532 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5481533 (_70606 : int) : (term147 _70606) = (term148 _70606).
Proof. exact (MK_COMB (@lem5481532) (@lem5481531 _70606)). Qed.
Lemma lem5481534 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5481535 (_70606 : int) (_70608 : int) : (term135 _70606 _70608) = (term149 _70606 _70608).
Proof. exact (MK_COMB (@lem5481533 _70606) (@lem5481534 _70608)). Qed.
Lemma lem5481536 (_70606 : int) (_70608 : int) : (term134 _70606 _70608) = (term149 _70606 _70608).
Proof. exact (TRANS (@lem5481522 _70606 _70608) (@lem5481535 _70606 _70608)). Qed.
Lemma lem5481537 (_70606 : int) (_70608 : int) : (term451 _70608 _70606) = (term149 _70606 _70608).
Proof. exact (TRANS (@lem5481519 _70606 _70608) (@lem5481536 _70606 _70608)). Qed.
Lemma lem5481538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481539 (_70608 : int) : (term523 _70608) = (term501 _70608).
Proof. exact (MK_COMB (@lem5481538) (@lem5481516 _70608)). Qed.
Lemma lem5481540 (_70606 : int) (_70608 : int) : (term456 _70608 _70606) = (term524 _70606 _70608).
Proof. exact (MK_COMB (@lem5481539 _70608) (@lem5481537 _70606 _70608)). Qed.
Lemma lem5481541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481542 (_70608 : int) (_70607 : int) : (term459 _70608 _70607) = (term525 _70608 _70607).
Proof. exact (MK_COMB (@lem5481541) (@lem5481493 _70608 _70607)). Qed.
Lemma lem5481543 (_70607 : int) (_70606 : int) (_70608 : int) : (term461 _70607 _70608 _70606) = (term526 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5481542 _70608 _70607) (@lem5481540 _70606 _70608)). Qed.
Lemma lem5481544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481545 (_70607 : int) (_70608 : int) (_70606 : int) : (term464 _70607 _70608 _70606) = (term527 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5481544) (@lem5481472 _70607 _70608 _70606)). Qed.
Lemma lem5481546 (_70607 : int) (_70606 : int) (_70608 : int) : (term466 _70607 _70608 _70606) = (term528 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5481545 _70607 _70608 _70606) (@lem5481543 _70607 _70606 _70608)). Qed.
Lemma lem5481547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481548 (_70607 : int) (_70606 : int) : (term471 _70607 _70606) = (term529 _70607 _70606).
Proof. exact (MK_COMB (@lem5481547) (@lem5481441 _70607 _70606)). Qed.
Lemma lem5481549 (_70607 : int) (_70606 : int) (_70608 : int) : (term473 _70607 _70608 _70606) = (term530 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5481548 _70607 _70606) (@lem5481546 _70607 _70606 _70608)). Qed.
Lemma lem5481550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481551 (_70607 : int) : (term477 _70607) = (term531 _70607).
Proof. exact (MK_COMB (@lem5481550) (@lem5481380 _70607)). Qed.
Lemma lem5481552 (_70607 : int) (_70606 : int) (_70608 : int) : (term479 _70607 _70608 _70606) = (term532 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5481551 _70607) (@lem5481549 _70607 _70606 _70608)). Qed.
Lemma lem5481553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481554 (_70608 : int) : (term115 _70608) = (term152 _70608).
Proof. exact (MK_COMB (@lem5481553) (@lem5481333 _70608)). Qed.
Lemma lem5481555 (_70607 : int) (_70606 : int) (_70608 : int) : (term483 _70607 _70608 _70606) = (term533 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5481554 _70608) (@lem5481552 _70607 _70606 _70608)). Qed.
Lemma lem5481556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481557 (_70607 : int) : (term115 _70607) = (term152 _70607).
Proof. exact (MK_COMB (@lem5481556) (@lem5481320 _70607)). Qed.
Lemma lem5481558 (_70607 : int) (_70606 : int) (_70608 : int) : (term487 _70607 _70608 _70606) = (term534 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5481557 _70607) (@lem5481555 _70607 _70606 _70608)). Qed.
Lemma lem5481559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5481560 (_70606 : int) : (term115 _70606) = (term152 _70606).
Proof. exact (MK_COMB (@lem5481559) (@lem5481307 _70606)). Qed.
Lemma lem5481561 (_70607 : int) (_70606 : int) (_70608 : int) : (term491 _70607 _70608 _70606) = (term535 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5481560 _70606) (@lem5481558 _70607 _70606 _70608)). Qed.
Lemma lem5481562 (_70607 : int) (_70606 : int) (_70608 : int) : (term492 _70607 _70608 _70606) = (term535 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5481294 _70607 _70608 _70606) (@lem5481561 _70607 _70606 _70608)). Qed.
Lemma lem5481566 (t : Prop) : (term155 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5481702 (_70607 : int) (_70606 : int) (_70608 : int) : (term536 _70607 _70606 _70608) = (term535 _70607 _70606 _70608).
Proof. exact (@lem5481566 (term535 _70607 _70606 _70608)). Qed.
Lemma lem5481703 (_70606 : int) : (term132 _70606) = (term157 _70606).
Proof. exact (@lem1988287 (real_of_int _70606) term129). Qed.
Lemma lem5481709 (_70606 : int) : (term158 _70606) = (term159 _70606).
Proof. exact (@lem1982792 (real_of_int _70606) term129). Qed.
Lemma lem5481711 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5481712 : term129 = term161.
Proof. exact (@lem5481711 (NUMERAL 0)). Qed.
Lemma lem5481714 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5481715 : term164 = term165.
Proof. exact (@lem5481714 term144). Qed.
Lemma lem5481716 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5481717 : term166 = term167.
Proof. exact (MK_COMB (@lem5481716) (@lem5481715)). Qed.
Lemma lem5481718 : term168 = term169.
Proof. exact (MK_COMB (@lem5481717) (@lem5481712)). Qed.
Lemma lem5481719 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5481721 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5481722 : term173 = term174.
Proof. exact (@lem5481721 term144 term144). Qed.
Lemma lem5481723 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5481724 : term176 = term144.
Proof. exact (EQ_MP (@lem5481723) (@lem940073)). Qed.
Lemma lem5481725 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5481726 : term174 = term143.
Proof. exact (MK_COMB (@lem5481725) (@lem5481724)). Qed.
Lemma lem5481727 : term173 = term143.
Proof. exact (TRANS (@lem5481722) (@lem5481726)). Qed.
Lemma lem5481729 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5481730 : term168 = term129.
Proof. exact (@lem5481729 term144). Qed.
Lemma lem5481731 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5481732 : term178 = term179.
Proof. exact (MK_COMB (@lem5481731) (@lem5481730)). Qed.
Lemma lem5481733 : term170 = term161.
Proof. exact (MK_COMB (@lem5481732) (@lem5481727)). Qed.
Lemma lem5481734 : term169 = term161.
Proof. exact (TRANS (@lem5481719) (@lem5481733)). Qed.
Lemma lem5481735 : term168 = term161.
Proof. exact (TRANS (@lem5481718) (@lem5481734)). Qed.
Lemma lem5481737 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5481738 : term161 = term129.
Proof. exact (@lem5481737 term129). Qed.
Lemma lem5481739 : term168 = term129.
Proof. exact (TRANS (@lem5481735) (@lem5481738)). Qed.
Lemma lem5481740 (_70606 : int) : (term145 _70606) = (term145 _70606).
Proof. exact (eq_refl (term145 _70606)). Qed.
Lemma lem5481741 (_70606 : int) : (term159 _70606) = (term181 _70606).
Proof. exact (MK_COMB (@lem5481740 _70606) (@lem5481739)). Qed.
Lemma lem5481742 (_70606 : int) : (term181 _70606) = (real_of_int _70606).
Proof. exact (@lem1982723 (real_of_int _70606)). Qed.
Lemma lem5481743 (_70606 : int) : (term159 _70606) = (real_of_int _70606).
Proof. exact (TRANS (@lem5481741 _70606) (@lem5481742 _70606)). Qed.
Lemma lem5481745 (_70606 : int) : (term158 _70606) = (real_of_int _70606).
Proof. exact (TRANS (@lem5481709 _70606) (@lem5481743 _70606)). Qed.
Lemma lem5481746 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5481747 (_70606 : int) : (term182 _70606) = (term183 _70606).
Proof. exact (MK_COMB (@lem5481746) (@lem5481745 _70606)). Qed.
Lemma lem5481748 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5481749 (_70606 : int) : (term157 _70606) = (term184 _70606).
Proof. exact (MK_COMB (@lem5481747 _70606) (@lem5481748)). Qed.
Lemma lem5481750 (_70606 : int) : (term132 _70606) = (term184 _70606).
Proof. exact (TRANS (@lem5481703 _70606) (@lem5481749 _70606)). Qed.
Lemma lem5481751 (_70607 : int) : (term132 _70607) = (term157 _70607).
Proof. exact (@lem1988287 (real_of_int _70607) term129). Qed.
Lemma lem5481757 (_70607 : int) : (term158 _70607) = (term159 _70607).
Proof. exact (@lem1982792 (real_of_int _70607) term129). Qed.
Lemma lem5481759 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5481760 : term129 = term161.
Proof. exact (@lem5481759 (NUMERAL 0)). Qed.
Lemma lem5481762 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5481763 : term164 = term165.
Proof. exact (@lem5481762 term144). Qed.
Lemma lem5481764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5481765 : term166 = term167.
Proof. exact (MK_COMB (@lem5481764) (@lem5481763)). Qed.
Lemma lem5481766 : term168 = term169.
Proof. exact (MK_COMB (@lem5481765) (@lem5481760)). Qed.
Lemma lem5481767 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5481769 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5481770 : term173 = term174.
Proof. exact (@lem5481769 term144 term144). Qed.
Lemma lem5481771 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5481772 : term176 = term144.
Proof. exact (EQ_MP (@lem5481771) (@lem940073)). Qed.
Lemma lem5481773 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5481774 : term174 = term143.
Proof. exact (MK_COMB (@lem5481773) (@lem5481772)). Qed.
Lemma lem5481775 : term173 = term143.
Proof. exact (TRANS (@lem5481770) (@lem5481774)). Qed.
Lemma lem5481777 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5481778 : term168 = term129.
Proof. exact (@lem5481777 term144). Qed.
Lemma lem5481779 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5481780 : term178 = term179.
Proof. exact (MK_COMB (@lem5481779) (@lem5481778)). Qed.
Lemma lem5481781 : term170 = term161.
Proof. exact (MK_COMB (@lem5481780) (@lem5481775)). Qed.
Lemma lem5481782 : term169 = term161.
Proof. exact (TRANS (@lem5481767) (@lem5481781)). Qed.
Lemma lem5481783 : term168 = term161.
Proof. exact (TRANS (@lem5481766) (@lem5481782)). Qed.
Lemma lem5481785 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5481786 : term161 = term129.
Proof. exact (@lem5481785 term129). Qed.
Lemma lem5481787 : term168 = term129.
Proof. exact (TRANS (@lem5481783) (@lem5481786)). Qed.
Lemma lem5481788 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5481789 (_70607 : int) : (term159 _70607) = (term181 _70607).
Proof. exact (MK_COMB (@lem5481788 _70607) (@lem5481787)). Qed.
Lemma lem5481790 (_70607 : int) : (term181 _70607) = (real_of_int _70607).
Proof. exact (@lem1982723 (real_of_int _70607)). Qed.
Lemma lem5481791 (_70607 : int) : (term159 _70607) = (real_of_int _70607).
Proof. exact (TRANS (@lem5481789 _70607) (@lem5481790 _70607)). Qed.
Lemma lem5481793 (_70607 : int) : (term158 _70607) = (real_of_int _70607).
Proof. exact (TRANS (@lem5481757 _70607) (@lem5481791 _70607)). Qed.
Lemma lem5481794 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5481795 (_70607 : int) : (term182 _70607) = (term183 _70607).
Proof. exact (MK_COMB (@lem5481794) (@lem5481793 _70607)). Qed.
Lemma lem5481796 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5481797 (_70607 : int) : (term157 _70607) = (term184 _70607).
Proof. exact (MK_COMB (@lem5481795 _70607) (@lem5481796)). Qed.
Lemma lem5481798 (_70607 : int) : (term132 _70607) = (term184 _70607).
Proof. exact (TRANS (@lem5481751 _70607) (@lem5481797 _70607)). Qed.
Lemma lem5481799 (_70608 : int) : (term132 _70608) = (term157 _70608).
Proof. exact (@lem1988287 (real_of_int _70608) term129). Qed.
Lemma lem5481805 (_70608 : int) : (term158 _70608) = (term159 _70608).
Proof. exact (@lem1982792 (real_of_int _70608) term129). Qed.
Lemma lem5481807 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5481808 : term129 = term161.
Proof. exact (@lem5481807 (NUMERAL 0)). Qed.
Lemma lem5481810 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5481811 : term164 = term165.
Proof. exact (@lem5481810 term144). Qed.
Lemma lem5481812 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5481813 : term166 = term167.
Proof. exact (MK_COMB (@lem5481812) (@lem5481811)). Qed.
Lemma lem5481814 : term168 = term169.
Proof. exact (MK_COMB (@lem5481813) (@lem5481808)). Qed.
Lemma lem5481815 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5481817 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5481818 : term173 = term174.
Proof. exact (@lem5481817 term144 term144). Qed.
Lemma lem5481819 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5481820 : term176 = term144.
Proof. exact (EQ_MP (@lem5481819) (@lem940073)). Qed.
Lemma lem5481821 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5481822 : term174 = term143.
Proof. exact (MK_COMB (@lem5481821) (@lem5481820)). Qed.
Lemma lem5481823 : term173 = term143.
Proof. exact (TRANS (@lem5481818) (@lem5481822)). Qed.
Lemma lem5481825 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5481826 : term168 = term129.
Proof. exact (@lem5481825 term144). Qed.
Lemma lem5481827 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5481828 : term178 = term179.
Proof. exact (MK_COMB (@lem5481827) (@lem5481826)). Qed.
Lemma lem5481829 : term170 = term161.
Proof. exact (MK_COMB (@lem5481828) (@lem5481823)). Qed.
Lemma lem5481830 : term169 = term161.
Proof. exact (TRANS (@lem5481815) (@lem5481829)). Qed.
Lemma lem5481831 : term168 = term161.
Proof. exact (TRANS (@lem5481814) (@lem5481830)). Qed.
Lemma lem5481833 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5481834 : term161 = term129.
Proof. exact (@lem5481833 term129). Qed.
Lemma lem5481835 : term168 = term129.
Proof. exact (TRANS (@lem5481831) (@lem5481834)). Qed.
Lemma lem5481836 (_70608 : int) : (term145 _70608) = (term145 _70608).
Proof. exact (eq_refl (term145 _70608)). Qed.
Lemma lem5481837 (_70608 : int) : (term159 _70608) = (term181 _70608).
Proof. exact (MK_COMB (@lem5481836 _70608) (@lem5481835)). Qed.
Lemma lem5481838 (_70608 : int) : (term181 _70608) = (real_of_int _70608).
Proof. exact (@lem1982723 (real_of_int _70608)). Qed.
Lemma lem5481839 (_70608 : int) : (term159 _70608) = (real_of_int _70608).
Proof. exact (TRANS (@lem5481837 _70608) (@lem5481838 _70608)). Qed.
Lemma lem5481841 (_70608 : int) : (term158 _70608) = (real_of_int _70608).
Proof. exact (TRANS (@lem5481805 _70608) (@lem5481839 _70608)). Qed.
Lemma lem5481842 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5481843 (_70608 : int) : (term182 _70608) = (term183 _70608).
Proof. exact (MK_COMB (@lem5481842) (@lem5481841 _70608)). Qed.
Lemma lem5481844 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5481845 (_70608 : int) : (term157 _70608) = (term184 _70608).
Proof. exact (MK_COMB (@lem5481843 _70608) (@lem5481844)). Qed.
Lemma lem5481846 (_70608 : int) : (term132 _70608) = (term184 _70608).
Proof. exact (TRANS (@lem5481799 _70608) (@lem5481845 _70608)). Qed.
Lemma lem5481847 (_70607 : int) : (term499 _70607) = (term537 _70607).
Proof. exact (@lem1988287 term129 (term146 _70607)). Qed.
Lemma lem5481859 (_70607 : int) : (term538 _70607) = (term539 _70607).
Proof. exact (@lem1982792 term129 (term146 _70607)). Qed.
Lemma lem5481860 (_70607 : int) : (term189 _70607) = (term190 _70607).
Proof. exact (@lem1982781 (real_of_int _70607) term164 term143). Qed.
Lemma lem5481862 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5481863 : term143 = term191.
Proof. exact (@lem5481862 term144). Qed.
Lemma lem5481865 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5481866 : term164 = term165.
Proof. exact (@lem5481865 term144). Qed.
Lemma lem5481867 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5481868 : term166 = term167.
Proof. exact (MK_COMB (@lem5481867) (@lem5481866)). Qed.
Lemma lem5481869 : term192 = term193.
Proof. exact (MK_COMB (@lem5481868) (@lem5481863)). Qed.
Lemma lem5481870 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5481872 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5481873 : term173 = term174.
Proof. exact (@lem5481872 term144 term144). Qed.
Lemma lem5481874 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5481875 : term176 = term144.
Proof. exact (EQ_MP (@lem5481874) (@lem940073)). Qed.
Lemma lem5481876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5481877 : term174 = term143.
Proof. exact (MK_COMB (@lem5481876) (@lem5481875)). Qed.
Lemma lem5481878 : term173 = term143.
Proof. exact (TRANS (@lem5481873) (@lem5481877)). Qed.
Lemma lem5481880 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5481881 : term192 = term197.
Proof. exact (@lem5481880 term144 term144). Qed.
Lemma lem5481882 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5481883 : term176 = term144.
Proof. exact (EQ_MP (@lem5481882) (@lem940073)). Qed.
Lemma lem5481884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5481885 : term174 = term143.
Proof. exact (MK_COMB (@lem5481884) (@lem5481883)). Qed.
Lemma lem5481886 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5481887 : term197 = term164.
Proof. exact (MK_COMB (@lem5481886) (@lem5481885)). Qed.
Lemma lem5481888 : term192 = term164.
Proof. exact (TRANS (@lem5481881) (@lem5481887)). Qed.
Lemma lem5481889 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5481890 : term198 = term199.
Proof. exact (MK_COMB (@lem5481889) (@lem5481888)). Qed.
Lemma lem5481891 : term194 = term165.
Proof. exact (MK_COMB (@lem5481890) (@lem5481878)). Qed.
Lemma lem5481892 : term193 = term165.
Proof. exact (TRANS (@lem5481870) (@lem5481891)). Qed.
Lemma lem5481893 : term192 = term165.
Proof. exact (TRANS (@lem5481869) (@lem5481892)). Qed.
Lemma lem5481895 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5481896 : term165 = term164.
Proof. exact (@lem5481895 term164). Qed.
Lemma lem5481897 : term192 = term164.
Proof. exact (TRANS (@lem5481893) (@lem5481896)). Qed.
Lemma lem5481900 (_70607 : int) : (term200 _70607) = (term200 _70607).
Proof. exact (eq_refl (term200 _70607)). Qed.
Lemma lem5481901 (_70607 : int) : (term190 _70607) = (term201 _70607).
Proof. exact (MK_COMB (@lem5481900 _70607) (@lem5481897)). Qed.
Lemma lem5481902 (_70607 : int) : (term189 _70607) = (term201 _70607).
Proof. exact (TRANS (@lem5481860 _70607) (@lem5481901 _70607)). Qed.
Lemma lem5481903 : term266 = term266.
Proof. exact (eq_refl term266). Qed.
Lemma lem5481904 (_70607 : int) : (term539 _70607) = (term267 _70607).
Proof. exact (MK_COMB (@lem5481903) (@lem5481902 _70607)). Qed.
Lemma lem5481905 (_70607 : int) : (term267 _70607) = (term201 _70607).
Proof. exact (@lem1982721 (term201 _70607)). Qed.
Lemma lem5481906 (_70607 : int) : (term539 _70607) = (term201 _70607).
Proof. exact (TRANS (@lem5481904 _70607) (@lem5481905 _70607)). Qed.
Lemma lem5481908 (_70607 : int) : (term538 _70607) = (term201 _70607).
Proof. exact (TRANS (@lem5481859 _70607) (@lem5481906 _70607)). Qed.
Lemma lem5481909 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5481910 (_70607 : int) : (term540 _70607) = (term269 _70607).
Proof. exact (MK_COMB (@lem5481909) (@lem5481908 _70607)). Qed.
Lemma lem5481911 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5481912 (_70607 : int) : (term537 _70607) = (term270 _70607).
Proof. exact (MK_COMB (@lem5481910 _70607) (@lem5481911)). Qed.
Lemma lem5481913 (_70607 : int) : (term499 _70607) = (term270 _70607).
Proof. exact (TRANS (@lem5481847 _70607) (@lem5481912 _70607)). Qed.
Lemma lem5481914 (_70607 : int) : (term511 _70607) = (term541 _70607).
Proof. exact (@lem1988287 (real_of_int _70607) term508). Qed.
Lemma lem5481921 : term508 = term143.
Proof. exact (@lem1982721 term143). Qed.
Lemma lem5481924 (_70607 : int) : (term542 _70607) = (term542 _70607).
Proof. exact (eq_refl (term542 _70607)). Qed.
Lemma lem5481925 (_70607 : int) : (term543 _70607) = (term544 _70607).
Proof. exact (MK_COMB (@lem5481924 _70607) (@lem5481921)). Qed.
Lemma lem5481926 (_70607 : int) : (term544 _70607) = (term545 _70607).
Proof. exact (@lem1982792 (real_of_int _70607) term143). Qed.
Lemma lem5481928 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5481929 : term143 = term191.
Proof. exact (@lem5481928 term144). Qed.
Lemma lem5481931 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5481932 : term164 = term165.
Proof. exact (@lem5481931 term144). Qed.
Lemma lem5481933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5481934 : term166 = term167.
Proof. exact (MK_COMB (@lem5481933) (@lem5481932)). Qed.
Lemma lem5481935 : term192 = term193.
Proof. exact (MK_COMB (@lem5481934) (@lem5481929)). Qed.
Lemma lem5481936 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5481938 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5481939 : term173 = term174.
Proof. exact (@lem5481938 term144 term144). Qed.
Lemma lem5481940 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5481941 : term176 = term144.
Proof. exact (EQ_MP (@lem5481940) (@lem940073)). Qed.
Lemma lem5481942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5481943 : term174 = term143.
Proof. exact (MK_COMB (@lem5481942) (@lem5481941)). Qed.
Lemma lem5481944 : term173 = term143.
Proof. exact (TRANS (@lem5481939) (@lem5481943)). Qed.
Lemma lem5481946 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5481947 : term192 = term197.
Proof. exact (@lem5481946 term144 term144). Qed.
Lemma lem5481948 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5481949 : term176 = term144.
Proof. exact (EQ_MP (@lem5481948) (@lem940073)). Qed.
Lemma lem5481950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5481951 : term174 = term143.
Proof. exact (MK_COMB (@lem5481950) (@lem5481949)). Qed.
Lemma lem5481952 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5481953 : term197 = term164.
Proof. exact (MK_COMB (@lem5481952) (@lem5481951)). Qed.
Lemma lem5481954 : term192 = term164.
Proof. exact (TRANS (@lem5481947) (@lem5481953)). Qed.
Lemma lem5481955 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5481956 : term198 = term199.
Proof. exact (MK_COMB (@lem5481955) (@lem5481954)). Qed.
Lemma lem5481957 : term194 = term165.
Proof. exact (MK_COMB (@lem5481956) (@lem5481944)). Qed.
Lemma lem5481958 : term193 = term165.
Proof. exact (TRANS (@lem5481936) (@lem5481957)). Qed.
Lemma lem5481959 : term192 = term165.
Proof. exact (TRANS (@lem5481935) (@lem5481958)). Qed.
Lemma lem5481961 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5481962 : term165 = term164.
Proof. exact (@lem5481961 term164). Qed.
Lemma lem5481963 : term192 = term164.
Proof. exact (TRANS (@lem5481959) (@lem5481962)). Qed.
Lemma lem5481964 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5481967 (_70607 : int) : (term545 _70607) = (term546 _70607).
Proof. exact (MK_COMB (@lem5481964 _70607) (@lem5481963)). Qed.
Lemma lem5481968 (_70607 : int) : (term544 _70607) = (term546 _70607).
Proof. exact (TRANS (@lem5481926 _70607) (@lem5481967 _70607)). Qed.
Lemma lem5481969 (_70607 : int) : (term543 _70607) = (term546 _70607).
Proof. exact (TRANS (@lem5481925 _70607) (@lem5481968 _70607)). Qed.
Lemma lem5481970 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5481971 (_70607 : int) : (term547 _70607) = (term548 _70607).
Proof. exact (MK_COMB (@lem5481970) (@lem5481969 _70607)). Qed.
Lemma lem5481972 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5481973 (_70607 : int) : (term541 _70607) = (term549 _70607).
Proof. exact (MK_COMB (@lem5481971 _70607) (@lem5481972)). Qed.
Lemma lem5481974 (_70607 : int) : (term511 _70607) = (term549 _70607).
Proof. exact (TRANS (@lem5481914 _70607) (@lem5481973 _70607)). Qed.
Lemma lem5481975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5481976 (_70607 : int) : (term501 _70607) = (term550 _70607).
Proof. exact (MK_COMB (@lem5481975) (@lem5481913 _70607)). Qed.
Lemma lem5481977 (_70607 : int) : (term512 _70607) = (term551 _70607).
Proof. exact (MK_COMB (@lem5481976 _70607) (@lem5481974 _70607)). Qed.
Lemma lem5481978 (_70607 : int) (_70606 : int) : ((real_of_int _70607) = (term146 _70606)) = ((term187 _70607 _70606) = term129).
Proof. exact (@lem1988293 (real_of_int _70607) (term146 _70606)). Qed.
Lemma lem5481990 (_70607 : int) (_70606 : int) : (term187 _70607 _70606) = (term188 _70607 _70606).
Proof. exact (@lem1982792 (real_of_int _70607) (term146 _70606)). Qed.
Lemma lem5481991 (_70606 : int) : (term189 _70606) = (term190 _70606).
Proof. exact (@lem1982781 (real_of_int _70606) term164 term143). Qed.
Lemma lem5481993 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5481994 : term143 = term191.
Proof. exact (@lem5481993 term144). Qed.
Lemma lem5481996 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5481997 : term164 = term165.
Proof. exact (@lem5481996 term144). Qed.
Lemma lem5481998 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5481999 : term166 = term167.
Proof. exact (MK_COMB (@lem5481998) (@lem5481997)). Qed.
Lemma lem5482000 : term192 = term193.
Proof. exact (MK_COMB (@lem5481999) (@lem5481994)). Qed.
Lemma lem5482001 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5482003 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482004 : term173 = term174.
Proof. exact (@lem5482003 term144 term144). Qed.
Lemma lem5482005 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482006 : term176 = term144.
Proof. exact (EQ_MP (@lem5482005) (@lem940073)). Qed.
Lemma lem5482007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482008 : term174 = term143.
Proof. exact (MK_COMB (@lem5482007) (@lem5482006)). Qed.
Lemma lem5482009 : term173 = term143.
Proof. exact (TRANS (@lem5482004) (@lem5482008)). Qed.
Lemma lem5482011 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5482012 : term192 = term197.
Proof. exact (@lem5482011 term144 term144). Qed.
Lemma lem5482013 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482014 : term176 = term144.
Proof. exact (EQ_MP (@lem5482013) (@lem940073)). Qed.
Lemma lem5482015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482016 : term174 = term143.
Proof. exact (MK_COMB (@lem5482015) (@lem5482014)). Qed.
Lemma lem5482017 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5482018 : term197 = term164.
Proof. exact (MK_COMB (@lem5482017) (@lem5482016)). Qed.
Lemma lem5482019 : term192 = term164.
Proof. exact (TRANS (@lem5482012) (@lem5482018)). Qed.
Lemma lem5482020 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5482021 : term198 = term199.
Proof. exact (MK_COMB (@lem5482020) (@lem5482019)). Qed.
Lemma lem5482022 : term194 = term165.
Proof. exact (MK_COMB (@lem5482021) (@lem5482009)). Qed.
Lemma lem5482023 : term193 = term165.
Proof. exact (TRANS (@lem5482001) (@lem5482022)). Qed.
Lemma lem5482024 : term192 = term165.
Proof. exact (TRANS (@lem5482000) (@lem5482023)). Qed.
Lemma lem5482026 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5482027 : term165 = term164.
Proof. exact (@lem5482026 term164). Qed.
Lemma lem5482028 : term192 = term164.
Proof. exact (TRANS (@lem5482024) (@lem5482027)). Qed.
Lemma lem5482031 (_70606 : int) : (term200 _70606) = (term200 _70606).
Proof. exact (eq_refl (term200 _70606)). Qed.
Lemma lem5482032 (_70606 : int) : (term190 _70606) = (term201 _70606).
Proof. exact (MK_COMB (@lem5482031 _70606) (@lem5482028)). Qed.
Lemma lem5482033 (_70606 : int) : (term189 _70606) = (term201 _70606).
Proof. exact (TRANS (@lem5481991 _70606) (@lem5482032 _70606)). Qed.
Lemma lem5482034 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5482035 (_70607 : int) (_70606 : int) : (term188 _70607 _70606) = (term202 _70607 _70606).
Proof. exact (MK_COMB (@lem5482034 _70607) (@lem5482033 _70606)). Qed.
Lemma lem5482040 (_70606 : int) (_70607 : int) : (term202 _70607 _70606) = (term552 _70606 _70607).
Proof. exact (@lem1982757 (term239 _70606) (real_of_int _70607) term164). Qed.
Lemma lem5482041 (_70606 : int) (_70607 : int) : (term188 _70607 _70606) = (term552 _70606 _70607).
Proof. exact (TRANS (@lem5482035 _70607 _70606) (@lem5482040 _70606 _70607)). Qed.
Lemma lem5482043 (_70606 : int) (_70607 : int) : (term187 _70607 _70606) = (term552 _70606 _70607).
Proof. exact (TRANS (@lem5481990 _70607 _70606) (@lem5482041 _70606 _70607)). Qed.
Lemma lem5482044 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5482045 (_70606 : int) (_70607 : int) : (term553 _70607 _70606) = (term554 _70606 _70607).
Proof. exact (MK_COMB (@lem5482044) (@lem5482043 _70606 _70607)). Qed.
Lemma lem5482046 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482047 (_70606 : int) (_70607 : int) : ((term187 _70607 _70606) = term129) = ((term552 _70606 _70607) = term129).
Proof. exact (MK_COMB (@lem5482045 _70606 _70607) (@lem5482046)). Qed.
Lemma lem5482048 (_70606 : int) (_70607 : int) : ((real_of_int _70607) = (term146 _70606)) = ((term552 _70606 _70607) = term129).
Proof. exact (TRANS (@lem5481978 _70607 _70606) (@lem5482047 _70606 _70607)). Qed.
Lemma lem5482049 (_70607 : int) : (term515 _70607) = (term555 _70607).
Proof. exact (@lem1988287 term143 (term146 _70607)). Qed.
Lemma lem5482061 (_70607 : int) : (term556 _70607) = (term557 _70607).
Proof. exact (@lem1982792 term143 (term146 _70607)). Qed.
Lemma lem5482062 (_70607 : int) : (term189 _70607) = (term190 _70607).
Proof. exact (@lem1982781 (real_of_int _70607) term164 term143). Qed.
Lemma lem5482064 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5482065 : term143 = term191.
Proof. exact (@lem5482064 term144). Qed.
Lemma lem5482067 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5482068 : term164 = term165.
Proof. exact (@lem5482067 term144). Qed.
Lemma lem5482069 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5482070 : term166 = term167.
Proof. exact (MK_COMB (@lem5482069) (@lem5482068)). Qed.
Lemma lem5482071 : term192 = term193.
Proof. exact (MK_COMB (@lem5482070) (@lem5482065)). Qed.
Lemma lem5482072 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5482074 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482075 : term173 = term174.
Proof. exact (@lem5482074 term144 term144). Qed.
Lemma lem5482076 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482077 : term176 = term144.
Proof. exact (EQ_MP (@lem5482076) (@lem940073)). Qed.
Lemma lem5482078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482079 : term174 = term143.
Proof. exact (MK_COMB (@lem5482078) (@lem5482077)). Qed.
Lemma lem5482080 : term173 = term143.
Proof. exact (TRANS (@lem5482075) (@lem5482079)). Qed.
Lemma lem5482082 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5482083 : term192 = term197.
Proof. exact (@lem5482082 term144 term144). Qed.
Lemma lem5482084 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482085 : term176 = term144.
Proof. exact (EQ_MP (@lem5482084) (@lem940073)). Qed.
Lemma lem5482086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482087 : term174 = term143.
Proof. exact (MK_COMB (@lem5482086) (@lem5482085)). Qed.
Lemma lem5482088 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5482089 : term197 = term164.
Proof. exact (MK_COMB (@lem5482088) (@lem5482087)). Qed.
Lemma lem5482090 : term192 = term164.
Proof. exact (TRANS (@lem5482083) (@lem5482089)). Qed.
Lemma lem5482091 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5482092 : term198 = term199.
Proof. exact (MK_COMB (@lem5482091) (@lem5482090)). Qed.
Lemma lem5482093 : term194 = term165.
Proof. exact (MK_COMB (@lem5482092) (@lem5482080)). Qed.
Lemma lem5482094 : term193 = term165.
Proof. exact (TRANS (@lem5482072) (@lem5482093)). Qed.
Lemma lem5482095 : term192 = term165.
Proof. exact (TRANS (@lem5482071) (@lem5482094)). Qed.
Lemma lem5482097 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5482098 : term165 = term164.
Proof. exact (@lem5482097 term164). Qed.
Lemma lem5482099 : term192 = term164.
Proof. exact (TRANS (@lem5482095) (@lem5482098)). Qed.
Lemma lem5482102 (_70607 : int) : (term200 _70607) = (term200 _70607).
Proof. exact (eq_refl (term200 _70607)). Qed.
Lemma lem5482103 (_70607 : int) : (term190 _70607) = (term201 _70607).
Proof. exact (MK_COMB (@lem5482102 _70607) (@lem5482099)). Qed.
Lemma lem5482104 (_70607 : int) : (term189 _70607) = (term201 _70607).
Proof. exact (TRANS (@lem5482062 _70607) (@lem5482103 _70607)). Qed.
Lemma lem5482105 : term558 = term558.
Proof. exact (eq_refl term558). Qed.
Lemma lem5482106 (_70607 : int) : (term557 _70607) = (term559 _70607).
Proof. exact (MK_COMB (@lem5482105) (@lem5482104 _70607)). Qed.
Lemma lem5482107 (_70607 : int) : (term559 _70607) = (term560 _70607).
Proof. exact (@lem1982757 (term239 _70607) term143 term164). Qed.
Lemma lem5482109 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5482110 : term164 = term165.
Proof. exact (@lem5482109 term144). Qed.
Lemma lem5482112 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5482113 : term143 = term191.
Proof. exact (@lem5482112 term144). Qed.
Lemma lem5482114 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5482115 : term558 = term561.
Proof. exact (MK_COMB (@lem5482114) (@lem5482113)). Qed.
Lemma lem5482116 : term562 = term563.
Proof. exact (MK_COMB (@lem5482115) (@lem5482110)). Qed.
Lemma lem5482117 : term564.
Proof. exact (@lem1981473 term143 term143 term164 term143 term129 term143). Qed.
Lemma lem5482119 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5482120 : term211 = term217.
Proof. exact (@lem5482119 (NUMERAL 0) term144). Qed.
Lemma lem5482121 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5482122 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5482123 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5482122 h1) (fun h1 : term217 = True => @lem5482121)). Qed.
Lemma lem5482124 : term217 = True.
Proof. exact (EQ_MP (@lem5482123) (@lem5482121)). Qed.
Lemma lem5482125 : term211 = True.
Proof. exact (TRANS (@lem5482120) (@lem5482124)). Qed.
Lemma lem5482126 : True = term211.
Proof. exact (SYM (@lem5482125)). Qed.
Lemma lem5482127 : term211.
Proof. exact (EQ_MP (@lem5482126) (@lem0)). Qed.
Lemma lem5482128 : term565.
Proof. exact (@lem5482117 (@lem5482127)). Qed.
Lemma lem5482130 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5482131 : term211 = term217.
Proof. exact (@lem5482130 (NUMERAL 0) term144). Qed.
Lemma lem5482132 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5482133 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5482134 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5482133 h1) (fun h1 : term217 = True => @lem5482132)). Qed.
Lemma lem5482135 : term217 = True.
Proof. exact (EQ_MP (@lem5482134) (@lem5482132)). Qed.
Lemma lem5482136 : term211 = True.
Proof. exact (TRANS (@lem5482131) (@lem5482135)). Qed.
Lemma lem5482137 : True = term211.
Proof. exact (SYM (@lem5482136)). Qed.
Lemma lem5482138 : term211.
Proof. exact (EQ_MP (@lem5482137) (@lem0)). Qed.
Lemma lem5482139 : term566.
Proof. exact (@lem5482128 (@lem5482138)). Qed.
Lemma lem5482141 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5482142 : term211 = term217.
Proof. exact (@lem5482141 (NUMERAL 0) term144). Qed.
Lemma lem5482143 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5482144 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5482145 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5482144 h1) (fun h1 : term217 = True => @lem5482143)). Qed.
Lemma lem5482146 : term217 = True.
Proof. exact (EQ_MP (@lem5482145) (@lem5482143)). Qed.
Lemma lem5482147 : term211 = True.
Proof. exact (TRANS (@lem5482142) (@lem5482146)). Qed.
Lemma lem5482148 : True = term211.
Proof. exact (SYM (@lem5482147)). Qed.
Lemma lem5482149 : term211.
Proof. exact (EQ_MP (@lem5482148) (@lem0)). Qed.
Lemma lem5482150 : term567.
Proof. exact (@lem5482139 (@lem5482149)). Qed.
Lemma lem5482152 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5482153 : term192 = term197.
Proof. exact (@lem5482152 term144 term144). Qed.
Lemma lem5482154 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482155 : term176 = term144.
Proof. exact (EQ_MP (@lem5482154) (@lem940073)). Qed.
Lemma lem5482156 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482157 : term174 = term143.
Proof. exact (MK_COMB (@lem5482156) (@lem5482155)). Qed.
Lemma lem5482158 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5482159 : term197 = term164.
Proof. exact (MK_COMB (@lem5482158) (@lem5482157)). Qed.
Lemma lem5482160 : term192 = term164.
Proof. exact (TRANS (@lem5482153) (@lem5482159)). Qed.
Lemma lem5482162 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482163 : term173 = term174.
Proof. exact (@lem5482162 term144 term144). Qed.
Lemma lem5482164 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482165 : term176 = term144.
Proof. exact (EQ_MP (@lem5482164) (@lem940073)). Qed.
Lemma lem5482166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482167 : term174 = term143.
Proof. exact (MK_COMB (@lem5482166) (@lem5482165)). Qed.
Lemma lem5482168 : term173 = term143.
Proof. exact (TRANS (@lem5482163) (@lem5482167)). Qed.
Lemma lem5482169 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5482170 : term568 = term558.
Proof. exact (MK_COMB (@lem5482169) (@lem5482168)). Qed.
Lemma lem5482171 : term569 = term562.
Proof. exact (MK_COMB (@lem5482170) (@lem5482160)). Qed.
Lemma lem5482173 (m : nat) : (term570 m) = term129.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5482174 : term562 = term129.
Proof. exact (@lem5482173 term144). Qed.
Lemma lem5482175 : term569 = term129.
Proof. exact (TRANS (@lem5482171) (@lem5482174)). Qed.
Lemma lem5482176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5482177 : term571 = term260.
Proof. exact (MK_COMB (@lem5482176) (@lem5482175)). Qed.
Lemma lem5482178 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5482179 : term572 = term222.
Proof. exact (MK_COMB (@lem5482177) (@lem5482178)). Qed.
Lemma lem5482181 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5482182 : term222 = term129.
Proof. exact (@lem5482181 term144). Qed.
Lemma lem5482183 : term572 = term129.
Proof. exact (TRANS (@lem5482179) (@lem5482182)). Qed.
Lemma lem5482185 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482186 : term173 = term174.
Proof. exact (@lem5482185 term144 term144). Qed.
Lemma lem5482187 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482188 : term176 = term144.
Proof. exact (EQ_MP (@lem5482187) (@lem940073)). Qed.
Lemma lem5482189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482190 : term174 = term143.
Proof. exact (MK_COMB (@lem5482189) (@lem5482188)). Qed.
Lemma lem5482191 : term173 = term143.
Proof. exact (TRANS (@lem5482186) (@lem5482190)). Qed.
Lemma lem5482192 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5482193 : term262 = term222.
Proof. exact (MK_COMB (@lem5482192) (@lem5482191)). Qed.
Lemma lem5482195 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5482196 : term222 = term129.
Proof. exact (@lem5482195 term144). Qed.
Lemma lem5482197 : term262 = term129.
Proof. exact (TRANS (@lem5482193) (@lem5482196)). Qed.
Lemma lem5482198 : term129 = term262.
Proof. exact (SYM (@lem5482197)). Qed.
Lemma lem5482199 : term572 = term262.
Proof. exact (TRANS (@lem5482183) (@lem5482198)). Qed.
Lemma lem5482200 : term563 = term161.
Proof. exact (@lem5482150 (@lem5482199)). Qed.
Lemma lem5482201 : term562 = term161.
Proof. exact (TRANS (@lem5482116) (@lem5482200)). Qed.
Lemma lem5482203 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5482204 : term161 = term129.
Proof. exact (@lem5482203 term129). Qed.
Lemma lem5482205 : term562 = term129.
Proof. exact (TRANS (@lem5482201) (@lem5482204)). Qed.
Lemma lem5482206 (_70607 : int) : (term200 _70607) = (term200 _70607).
Proof. exact (eq_refl (term200 _70607)). Qed.
Lemma lem5482207 (_70607 : int) : (term560 _70607) = (term573 _70607).
Proof. exact (MK_COMB (@lem5482206 _70607) (@lem5482205)). Qed.
Lemma lem5482208 (_70607 : int) : (term559 _70607) = (term573 _70607).
Proof. exact (TRANS (@lem5482107 _70607) (@lem5482207 _70607)). Qed.
Lemma lem5482209 (_70607 : int) : (term573 _70607) = (term239 _70607).
Proof. exact (@lem1982723 (term239 _70607)). Qed.
Lemma lem5482210 (_70607 : int) : (term559 _70607) = (term239 _70607).
Proof. exact (TRANS (@lem5482208 _70607) (@lem5482209 _70607)). Qed.
Lemma lem5482211 (_70607 : int) : (term557 _70607) = (term239 _70607).
Proof. exact (TRANS (@lem5482106 _70607) (@lem5482210 _70607)). Qed.
Lemma lem5482213 (_70607 : int) : (term556 _70607) = (term239 _70607).
Proof. exact (TRANS (@lem5482061 _70607) (@lem5482211 _70607)). Qed.
Lemma lem5482214 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5482215 (_70607 : int) : (term574 _70607) = (term575 _70607).
Proof. exact (MK_COMB (@lem5482214) (@lem5482213 _70607)). Qed.
Lemma lem5482216 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482217 (_70607 : int) : (term555 _70607) = (term576 _70607).
Proof. exact (MK_COMB (@lem5482215 _70607) (@lem5482216)). Qed.
Lemma lem5482218 (_70607 : int) : (term515 _70607) = (term576 _70607).
Proof. exact (TRANS (@lem5482049 _70607) (@lem5482217 _70607)). Qed.
Lemma lem5482219 (_70606 : int) : ((real_of_int _70606) = term129) = ((term158 _70606) = term129).
Proof. exact (@lem1988293 (real_of_int _70606) term129). Qed.
Lemma lem5482225 (_70606 : int) : (term158 _70606) = (term159 _70606).
Proof. exact (@lem1982792 (real_of_int _70606) term129). Qed.
Lemma lem5482227 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5482228 : term129 = term161.
Proof. exact (@lem5482227 (NUMERAL 0)). Qed.
Lemma lem5482230 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5482231 : term164 = term165.
Proof. exact (@lem5482230 term144). Qed.
Lemma lem5482232 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5482233 : term166 = term167.
Proof. exact (MK_COMB (@lem5482232) (@lem5482231)). Qed.
Lemma lem5482234 : term168 = term169.
Proof. exact (MK_COMB (@lem5482233) (@lem5482228)). Qed.
Lemma lem5482235 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5482237 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482238 : term173 = term174.
Proof. exact (@lem5482237 term144 term144). Qed.
Lemma lem5482239 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482240 : term176 = term144.
Proof. exact (EQ_MP (@lem5482239) (@lem940073)). Qed.
Lemma lem5482241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482242 : term174 = term143.
Proof. exact (MK_COMB (@lem5482241) (@lem5482240)). Qed.
Lemma lem5482243 : term173 = term143.
Proof. exact (TRANS (@lem5482238) (@lem5482242)). Qed.
Lemma lem5482245 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5482246 : term168 = term129.
Proof. exact (@lem5482245 term144). Qed.
Lemma lem5482247 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5482248 : term178 = term179.
Proof. exact (MK_COMB (@lem5482247) (@lem5482246)). Qed.
Lemma lem5482249 : term170 = term161.
Proof. exact (MK_COMB (@lem5482248) (@lem5482243)). Qed.
Lemma lem5482250 : term169 = term161.
Proof. exact (TRANS (@lem5482235) (@lem5482249)). Qed.
Lemma lem5482251 : term168 = term161.
Proof. exact (TRANS (@lem5482234) (@lem5482250)). Qed.
Lemma lem5482253 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5482254 : term161 = term129.
Proof. exact (@lem5482253 term129). Qed.
Lemma lem5482255 : term168 = term129.
Proof. exact (TRANS (@lem5482251) (@lem5482254)). Qed.
Lemma lem5482256 (_70606 : int) : (term145 _70606) = (term145 _70606).
Proof. exact (eq_refl (term145 _70606)). Qed.
Lemma lem5482257 (_70606 : int) : (term159 _70606) = (term181 _70606).
Proof. exact (MK_COMB (@lem5482256 _70606) (@lem5482255)). Qed.
Lemma lem5482258 (_70606 : int) : (term181 _70606) = (real_of_int _70606).
Proof. exact (@lem1982723 (real_of_int _70606)). Qed.
Lemma lem5482259 (_70606 : int) : (term159 _70606) = (real_of_int _70606).
Proof. exact (TRANS (@lem5482257 _70606) (@lem5482258 _70606)). Qed.
Lemma lem5482261 (_70606 : int) : (term158 _70606) = (real_of_int _70606).
Proof. exact (TRANS (@lem5482225 _70606) (@lem5482259 _70606)). Qed.
Lemma lem5482262 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5482263 (_70606 : int) : (term185 _70606) = (term133 _70606).
Proof. exact (MK_COMB (@lem5482262) (@lem5482261 _70606)). Qed.
Lemma lem5482264 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482265 (_70606 : int) : ((term158 _70606) = term129) = ((real_of_int _70606) = term129).
Proof. exact (MK_COMB (@lem5482263 _70606) (@lem5482264)). Qed.
Lemma lem5482266 (_70606 : int) : ((real_of_int _70606) = term129) = ((real_of_int _70606) = term129).
Proof. exact (TRANS (@lem5482219 _70606) (@lem5482265 _70606)). Qed.
Lemma lem5482267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482268 (_70607 : int) : (term516 _70607) = (term577 _70607).
Proof. exact (MK_COMB (@lem5482267) (@lem5482218 _70607)). Qed.
Lemma lem5482269 (_70607 : int) (_70606 : int) : (term517 _70607 _70606) = (term578 _70607 _70606).
Proof. exact (MK_COMB (@lem5482268 _70607) (@lem5482266 _70606)). Qed.
Lemma lem5482270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482271 (_70606 : int) (_70607 : int) : (term518 _70607 _70606) = (term579 _70606 _70607).
Proof. exact (MK_COMB (@lem5482270) (@lem5482048 _70606 _70607)). Qed.
Lemma lem5482272 (_70607 : int) (_70606 : int) : (term519 _70607 _70606) = (term580 _70607 _70606).
Proof. exact (MK_COMB (@lem5482271 _70606 _70607) (@lem5482269 _70607 _70606)). Qed.
Lemma lem5482273 (_70608 : int) (_70607 : int) : (term125 _70607 _70608) = (term581 _70608 _70607).
Proof. exact (@lem1988287 (real_of_int _70608) (real_of_int _70607)). Qed.
Lemma lem5482279 (_70608 : int) (_70607 : int) : (term582 _70608 _70607) = (term583 _70608 _70607).
Proof. exact (@lem1982792 (real_of_int _70608) (real_of_int _70607)). Qed.
Lemma lem5482284 (_70607 : int) (_70608 : int) : (term583 _70608 _70607) = (term584 _70607 _70608).
Proof. exact (@lem1982761 (term239 _70607) (real_of_int _70608)). Qed.
Lemma lem5482286 (_70607 : int) (_70608 : int) : (term582 _70608 _70607) = (term584 _70607 _70608).
Proof. exact (TRANS (@lem5482279 _70608 _70607) (@lem5482284 _70607 _70608)). Qed.
Lemma lem5482287 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5482288 (_70607 : int) (_70608 : int) : (term585 _70608 _70607) = (term586 _70607 _70608).
Proof. exact (MK_COMB (@lem5482287) (@lem5482286 _70607 _70608)). Qed.
Lemma lem5482289 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482290 (_70607 : int) (_70608 : int) : (term581 _70608 _70607) = (term587 _70607 _70608).
Proof. exact (MK_COMB (@lem5482288 _70607 _70608) (@lem5482289)). Qed.
Lemma lem5482291 (_70607 : int) (_70608 : int) : (term125 _70607 _70608) = (term587 _70607 _70608).
Proof. exact (TRANS (@lem5482273 _70608 _70607) (@lem5482290 _70607 _70608)). Qed.
Lemma lem5482292 (_70608 : int) : (term132 _70608) = (term157 _70608).
Proof. exact (@lem1988287 (real_of_int _70608) term129). Qed.
Lemma lem5482298 (_70608 : int) : (term158 _70608) = (term159 _70608).
Proof. exact (@lem1982792 (real_of_int _70608) term129). Qed.
Lemma lem5482300 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5482301 : term129 = term161.
Proof. exact (@lem5482300 (NUMERAL 0)). Qed.
Lemma lem5482303 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5482304 : term164 = term165.
Proof. exact (@lem5482303 term144). Qed.
Lemma lem5482305 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5482306 : term166 = term167.
Proof. exact (MK_COMB (@lem5482305) (@lem5482304)). Qed.
Lemma lem5482307 : term168 = term169.
Proof. exact (MK_COMB (@lem5482306) (@lem5482301)). Qed.
Lemma lem5482308 : term169 = term170.
Proof. exact (@lem1981613 term164 term129 term143 term143). Qed.
Lemma lem5482310 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482311 : term173 = term174.
Proof. exact (@lem5482310 term144 term144). Qed.
Lemma lem5482312 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482313 : term176 = term144.
Proof. exact (EQ_MP (@lem5482312) (@lem940073)). Qed.
Lemma lem5482314 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482315 : term174 = term143.
Proof. exact (MK_COMB (@lem5482314) (@lem5482313)). Qed.
Lemma lem5482316 : term173 = term143.
Proof. exact (TRANS (@lem5482311) (@lem5482315)). Qed.
Lemma lem5482318 (x : nat) : (term177 x) = term129.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5482319 : term168 = term129.
Proof. exact (@lem5482318 term144). Qed.
Lemma lem5482320 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5482321 : term178 = term179.
Proof. exact (MK_COMB (@lem5482320) (@lem5482319)). Qed.
Lemma lem5482322 : term170 = term161.
Proof. exact (MK_COMB (@lem5482321) (@lem5482316)). Qed.
Lemma lem5482323 : term169 = term161.
Proof. exact (TRANS (@lem5482308) (@lem5482322)). Qed.
Lemma lem5482324 : term168 = term161.
Proof. exact (TRANS (@lem5482307) (@lem5482323)). Qed.
Lemma lem5482326 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5482327 : term161 = term129.
Proof. exact (@lem5482326 term129). Qed.
Lemma lem5482328 : term168 = term129.
Proof. exact (TRANS (@lem5482324) (@lem5482327)). Qed.
Lemma lem5482329 (_70608 : int) : (term145 _70608) = (term145 _70608).
Proof. exact (eq_refl (term145 _70608)). Qed.
Lemma lem5482330 (_70608 : int) : (term159 _70608) = (term181 _70608).
Proof. exact (MK_COMB (@lem5482329 _70608) (@lem5482328)). Qed.
Lemma lem5482331 (_70608 : int) : (term181 _70608) = (real_of_int _70608).
Proof. exact (@lem1982723 (real_of_int _70608)). Qed.
Lemma lem5482332 (_70608 : int) : (term159 _70608) = (real_of_int _70608).
Proof. exact (TRANS (@lem5482330 _70608) (@lem5482331 _70608)). Qed.
Lemma lem5482334 (_70608 : int) : (term158 _70608) = (real_of_int _70608).
Proof. exact (TRANS (@lem5482298 _70608) (@lem5482332 _70608)). Qed.
Lemma lem5482335 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5482336 (_70608 : int) : (term182 _70608) = (term183 _70608).
Proof. exact (MK_COMB (@lem5482335) (@lem5482334 _70608)). Qed.
Lemma lem5482337 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482338 (_70608 : int) : (term157 _70608) = (term184 _70608).
Proof. exact (MK_COMB (@lem5482336 _70608) (@lem5482337)). Qed.
Lemma lem5482339 (_70608 : int) : (term132 _70608) = (term184 _70608).
Proof. exact (TRANS (@lem5482292 _70608) (@lem5482338 _70608)). Qed.
Lemma lem5482340 (_70606 : int) (_70608 : int) : (term125 _70608 _70606) = (term581 _70606 _70608).
Proof. exact (@lem1988287 (real_of_int _70606) (real_of_int _70608)). Qed.
Lemma lem5482353 (_70606 : int) (_70608 : int) : (term582 _70606 _70608) = (term583 _70606 _70608).
Proof. exact (@lem1982792 (real_of_int _70606) (real_of_int _70608)). Qed.
Lemma lem5482354 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5482355 (_70606 : int) (_70608 : int) : (term585 _70606 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5482354) (@lem5482353 _70606 _70608)). Qed.
Lemma lem5482356 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482357 (_70606 : int) (_70608 : int) : (term581 _70606 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5482355 _70606 _70608) (@lem5482356)). Qed.
Lemma lem5482358 (_70606 : int) (_70608 : int) : (term125 _70608 _70606) = (term589 _70606 _70608).
Proof. exact (TRANS (@lem5482340 _70606 _70608) (@lem5482357 _70606 _70608)). Qed.
Lemma lem5482359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482360 (_70608 : int) : (term152 _70608) = (term207 _70608).
Proof. exact (MK_COMB (@lem5482359) (@lem5482339 _70608)). Qed.
Lemma lem5482361 (_70606 : int) (_70608 : int) : (term520 _70608 _70606) = (term590 _70606 _70608).
Proof. exact (MK_COMB (@lem5482360 _70608) (@lem5482358 _70606 _70608)). Qed.
Lemma lem5482362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482363 (_70607 : int) (_70608 : int) : (term521 _70607 _70608) = (term591 _70607 _70608).
Proof. exact (MK_COMB (@lem5482362) (@lem5482291 _70607 _70608)). Qed.
Lemma lem5482364 (_70607 : int) (_70606 : int) (_70608 : int) : (term522 _70607 _70608 _70606) = (term592 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482363 _70607 _70608) (@lem5482361 _70606 _70608)). Qed.
Lemma lem5482365 (_70607 : int) (_70608 : int) : (term149 _70608 _70607) = (term186 _70607 _70608).
Proof. exact (@lem1988287 (real_of_int _70607) (term146 _70608)). Qed.
Lemma lem5482377 (_70607 : int) (_70608 : int) : (term187 _70607 _70608) = (term188 _70607 _70608).
Proof. exact (@lem1982792 (real_of_int _70607) (term146 _70608)). Qed.
Lemma lem5482378 (_70608 : int) : (term189 _70608) = (term190 _70608).
Proof. exact (@lem1982781 (real_of_int _70608) term164 term143). Qed.
Lemma lem5482380 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5482381 : term143 = term191.
Proof. exact (@lem5482380 term144). Qed.
Lemma lem5482383 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5482384 : term164 = term165.
Proof. exact (@lem5482383 term144). Qed.
Lemma lem5482385 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5482386 : term166 = term167.
Proof. exact (MK_COMB (@lem5482385) (@lem5482384)). Qed.
Lemma lem5482387 : term192 = term193.
Proof. exact (MK_COMB (@lem5482386) (@lem5482381)). Qed.
Lemma lem5482388 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5482390 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482391 : term173 = term174.
Proof. exact (@lem5482390 term144 term144). Qed.
Lemma lem5482392 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482393 : term176 = term144.
Proof. exact (EQ_MP (@lem5482392) (@lem940073)). Qed.
Lemma lem5482394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482395 : term174 = term143.
Proof. exact (MK_COMB (@lem5482394) (@lem5482393)). Qed.
Lemma lem5482396 : term173 = term143.
Proof. exact (TRANS (@lem5482391) (@lem5482395)). Qed.
Lemma lem5482398 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5482399 : term192 = term197.
Proof. exact (@lem5482398 term144 term144). Qed.
Lemma lem5482400 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482401 : term176 = term144.
Proof. exact (EQ_MP (@lem5482400) (@lem940073)). Qed.
Lemma lem5482402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482403 : term174 = term143.
Proof. exact (MK_COMB (@lem5482402) (@lem5482401)). Qed.
Lemma lem5482404 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5482405 : term197 = term164.
Proof. exact (MK_COMB (@lem5482404) (@lem5482403)). Qed.
Lemma lem5482406 : term192 = term164.
Proof. exact (TRANS (@lem5482399) (@lem5482405)). Qed.
Lemma lem5482407 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5482408 : term198 = term199.
Proof. exact (MK_COMB (@lem5482407) (@lem5482406)). Qed.
Lemma lem5482409 : term194 = term165.
Proof. exact (MK_COMB (@lem5482408) (@lem5482396)). Qed.
Lemma lem5482410 : term193 = term165.
Proof. exact (TRANS (@lem5482388) (@lem5482409)). Qed.
Lemma lem5482411 : term192 = term165.
Proof. exact (TRANS (@lem5482387) (@lem5482410)). Qed.
Lemma lem5482413 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5482414 : term165 = term164.
Proof. exact (@lem5482413 term164). Qed.
Lemma lem5482415 : term192 = term164.
Proof. exact (TRANS (@lem5482411) (@lem5482414)). Qed.
Lemma lem5482418 (_70608 : int) : (term200 _70608) = (term200 _70608).
Proof. exact (eq_refl (term200 _70608)). Qed.
Lemma lem5482419 (_70608 : int) : (term190 _70608) = (term201 _70608).
Proof. exact (MK_COMB (@lem5482418 _70608) (@lem5482415)). Qed.
Lemma lem5482420 (_70608 : int) : (term189 _70608) = (term201 _70608).
Proof. exact (TRANS (@lem5482378 _70608) (@lem5482419 _70608)). Qed.
Lemma lem5482421 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5482424 (_70607 : int) (_70608 : int) : (term188 _70607 _70608) = (term202 _70607 _70608).
Proof. exact (MK_COMB (@lem5482421 _70607) (@lem5482420 _70608)). Qed.
Lemma lem5482426 (_70607 : int) (_70608 : int) : (term187 _70607 _70608) = (term202 _70607 _70608).
Proof. exact (TRANS (@lem5482377 _70607 _70608) (@lem5482424 _70607 _70608)). Qed.
Lemma lem5482427 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5482428 (_70607 : int) (_70608 : int) : (term203 _70607 _70608) = (term204 _70607 _70608).
Proof. exact (MK_COMB (@lem5482427) (@lem5482426 _70607 _70608)). Qed.
Lemma lem5482429 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482430 (_70607 : int) (_70608 : int) : (term186 _70607 _70608) = (term205 _70607 _70608).
Proof. exact (MK_COMB (@lem5482428 _70607 _70608) (@lem5482429)). Qed.
Lemma lem5482431 (_70607 : int) (_70608 : int) : (term149 _70608 _70607) = (term205 _70607 _70608).
Proof. exact (TRANS (@lem5482365 _70607 _70608) (@lem5482430 _70607 _70608)). Qed.
Lemma lem5482432 (_70608 : int) : (term499 _70608) = (term537 _70608).
Proof. exact (@lem1988287 term129 (term146 _70608)). Qed.
Lemma lem5482444 (_70608 : int) : (term538 _70608) = (term539 _70608).
Proof. exact (@lem1982792 term129 (term146 _70608)). Qed.
Lemma lem5482445 (_70608 : int) : (term189 _70608) = (term190 _70608).
Proof. exact (@lem1982781 (real_of_int _70608) term164 term143). Qed.
Lemma lem5482447 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5482448 : term143 = term191.
Proof. exact (@lem5482447 term144). Qed.
Lemma lem5482450 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5482451 : term164 = term165.
Proof. exact (@lem5482450 term144). Qed.
Lemma lem5482452 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5482453 : term166 = term167.
Proof. exact (MK_COMB (@lem5482452) (@lem5482451)). Qed.
Lemma lem5482454 : term192 = term193.
Proof. exact (MK_COMB (@lem5482453) (@lem5482448)). Qed.
Lemma lem5482455 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5482457 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482458 : term173 = term174.
Proof. exact (@lem5482457 term144 term144). Qed.
Lemma lem5482459 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482460 : term176 = term144.
Proof. exact (EQ_MP (@lem5482459) (@lem940073)). Qed.
Lemma lem5482461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482462 : term174 = term143.
Proof. exact (MK_COMB (@lem5482461) (@lem5482460)). Qed.
Lemma lem5482463 : term173 = term143.
Proof. exact (TRANS (@lem5482458) (@lem5482462)). Qed.
Lemma lem5482465 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5482466 : term192 = term197.
Proof. exact (@lem5482465 term144 term144). Qed.
Lemma lem5482467 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482468 : term176 = term144.
Proof. exact (EQ_MP (@lem5482467) (@lem940073)). Qed.
Lemma lem5482469 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482470 : term174 = term143.
Proof. exact (MK_COMB (@lem5482469) (@lem5482468)). Qed.
Lemma lem5482471 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5482472 : term197 = term164.
Proof. exact (MK_COMB (@lem5482471) (@lem5482470)). Qed.
Lemma lem5482473 : term192 = term164.
Proof. exact (TRANS (@lem5482466) (@lem5482472)). Qed.
Lemma lem5482474 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5482475 : term198 = term199.
Proof. exact (MK_COMB (@lem5482474) (@lem5482473)). Qed.
Lemma lem5482476 : term194 = term165.
Proof. exact (MK_COMB (@lem5482475) (@lem5482463)). Qed.
Lemma lem5482477 : term193 = term165.
Proof. exact (TRANS (@lem5482455) (@lem5482476)). Qed.
Lemma lem5482478 : term192 = term165.
Proof. exact (TRANS (@lem5482454) (@lem5482477)). Qed.
Lemma lem5482480 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5482481 : term165 = term164.
Proof. exact (@lem5482480 term164). Qed.
Lemma lem5482482 : term192 = term164.
Proof. exact (TRANS (@lem5482478) (@lem5482481)). Qed.
Lemma lem5482485 (_70608 : int) : (term200 _70608) = (term200 _70608).
Proof. exact (eq_refl (term200 _70608)). Qed.
Lemma lem5482486 (_70608 : int) : (term190 _70608) = (term201 _70608).
Proof. exact (MK_COMB (@lem5482485 _70608) (@lem5482482)). Qed.
Lemma lem5482487 (_70608 : int) : (term189 _70608) = (term201 _70608).
Proof. exact (TRANS (@lem5482445 _70608) (@lem5482486 _70608)). Qed.
Lemma lem5482488 : term266 = term266.
Proof. exact (eq_refl term266). Qed.
Lemma lem5482489 (_70608 : int) : (term539 _70608) = (term267 _70608).
Proof. exact (MK_COMB (@lem5482488) (@lem5482487 _70608)). Qed.
Lemma lem5482490 (_70608 : int) : (term267 _70608) = (term201 _70608).
Proof. exact (@lem1982721 (term201 _70608)). Qed.
Lemma lem5482491 (_70608 : int) : (term539 _70608) = (term201 _70608).
Proof. exact (TRANS (@lem5482489 _70608) (@lem5482490 _70608)). Qed.
Lemma lem5482493 (_70608 : int) : (term538 _70608) = (term201 _70608).
Proof. exact (TRANS (@lem5482444 _70608) (@lem5482491 _70608)). Qed.
Lemma lem5482494 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5482495 (_70608 : int) : (term540 _70608) = (term269 _70608).
Proof. exact (MK_COMB (@lem5482494) (@lem5482493 _70608)). Qed.
Lemma lem5482496 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482497 (_70608 : int) : (term537 _70608) = (term270 _70608).
Proof. exact (MK_COMB (@lem5482495 _70608) (@lem5482496)). Qed.
Lemma lem5482498 (_70608 : int) : (term499 _70608) = (term270 _70608).
Proof. exact (TRANS (@lem5482432 _70608) (@lem5482497 _70608)). Qed.
Lemma lem5482499 (_70608 : int) (_70606 : int) : (term149 _70606 _70608) = (term186 _70608 _70606).
Proof. exact (@lem1988287 (real_of_int _70608) (term146 _70606)). Qed.
Lemma lem5482511 (_70608 : int) (_70606 : int) : (term187 _70608 _70606) = (term188 _70608 _70606).
Proof. exact (@lem1982792 (real_of_int _70608) (term146 _70606)). Qed.
Lemma lem5482512 (_70606 : int) : (term189 _70606) = (term190 _70606).
Proof. exact (@lem1982781 (real_of_int _70606) term164 term143). Qed.
Lemma lem5482514 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5482515 : term143 = term191.
Proof. exact (@lem5482514 term144). Qed.
Lemma lem5482517 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5482518 : term164 = term165.
Proof. exact (@lem5482517 term144). Qed.
Lemma lem5482519 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5482520 : term166 = term167.
Proof. exact (MK_COMB (@lem5482519) (@lem5482518)). Qed.
Lemma lem5482521 : term192 = term193.
Proof. exact (MK_COMB (@lem5482520) (@lem5482515)). Qed.
Lemma lem5482522 : term193 = term194.
Proof. exact (@lem1981613 term164 term143 term143 term143). Qed.
Lemma lem5482524 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5482525 : term173 = term174.
Proof. exact (@lem5482524 term144 term144). Qed.
Lemma lem5482526 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482527 : term176 = term144.
Proof. exact (EQ_MP (@lem5482526) (@lem940073)). Qed.
Lemma lem5482528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482529 : term174 = term143.
Proof. exact (MK_COMB (@lem5482528) (@lem5482527)). Qed.
Lemma lem5482530 : term173 = term143.
Proof. exact (TRANS (@lem5482525) (@lem5482529)). Qed.
Lemma lem5482532 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5482533 : term192 = term197.
Proof. exact (@lem5482532 term144 term144). Qed.
Lemma lem5482534 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5482535 : term176 = term144.
Proof. exact (EQ_MP (@lem5482534) (@lem940073)). Qed.
Lemma lem5482536 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5482537 : term174 = term143.
Proof. exact (MK_COMB (@lem5482536) (@lem5482535)). Qed.
Lemma lem5482538 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5482539 : term197 = term164.
Proof. exact (MK_COMB (@lem5482538) (@lem5482537)). Qed.
Lemma lem5482540 : term192 = term164.
Proof. exact (TRANS (@lem5482533) (@lem5482539)). Qed.
Lemma lem5482541 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5482542 : term198 = term199.
Proof. exact (MK_COMB (@lem5482541) (@lem5482540)). Qed.
Lemma lem5482543 : term194 = term165.
Proof. exact (MK_COMB (@lem5482542) (@lem5482530)). Qed.
Lemma lem5482544 : term193 = term165.
Proof. exact (TRANS (@lem5482522) (@lem5482543)). Qed.
Lemma lem5482545 : term192 = term165.
Proof. exact (TRANS (@lem5482521) (@lem5482544)). Qed.
Lemma lem5482547 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5482548 : term165 = term164.
Proof. exact (@lem5482547 term164). Qed.
Lemma lem5482549 : term192 = term164.
Proof. exact (TRANS (@lem5482545) (@lem5482548)). Qed.
Lemma lem5482552 (_70606 : int) : (term200 _70606) = (term200 _70606).
Proof. exact (eq_refl (term200 _70606)). Qed.
Lemma lem5482553 (_70606 : int) : (term190 _70606) = (term201 _70606).
Proof. exact (MK_COMB (@lem5482552 _70606) (@lem5482549)). Qed.
Lemma lem5482554 (_70606 : int) : (term189 _70606) = (term201 _70606).
Proof. exact (TRANS (@lem5482512 _70606) (@lem5482553 _70606)). Qed.
Lemma lem5482555 (_70608 : int) : (term145 _70608) = (term145 _70608).
Proof. exact (eq_refl (term145 _70608)). Qed.
Lemma lem5482556 (_70608 : int) (_70606 : int) : (term188 _70608 _70606) = (term202 _70608 _70606).
Proof. exact (MK_COMB (@lem5482555 _70608) (@lem5482554 _70606)). Qed.
Lemma lem5482561 (_70606 : int) (_70608 : int) : (term202 _70608 _70606) = (term552 _70606 _70608).
Proof. exact (@lem1982757 (term239 _70606) (real_of_int _70608) term164). Qed.
Lemma lem5482562 (_70606 : int) (_70608 : int) : (term188 _70608 _70606) = (term552 _70606 _70608).
Proof. exact (TRANS (@lem5482556 _70608 _70606) (@lem5482561 _70606 _70608)). Qed.
Lemma lem5482564 (_70606 : int) (_70608 : int) : (term187 _70608 _70606) = (term552 _70606 _70608).
Proof. exact (TRANS (@lem5482511 _70608 _70606) (@lem5482562 _70606 _70608)). Qed.
Lemma lem5482565 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5482566 (_70606 : int) (_70608 : int) : (term203 _70608 _70606) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5482565) (@lem5482564 _70606 _70608)). Qed.
Lemma lem5482567 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5482568 (_70606 : int) (_70608 : int) : (term186 _70608 _70606) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5482566 _70606 _70608) (@lem5482567)). Qed.
Lemma lem5482569 (_70606 : int) (_70608 : int) : (term149 _70606 _70608) = (term594 _70606 _70608).
Proof. exact (TRANS (@lem5482499 _70608 _70606) (@lem5482568 _70606 _70608)). Qed.
Lemma lem5482570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482571 (_70608 : int) : (term501 _70608) = (term550 _70608).
Proof. exact (MK_COMB (@lem5482570) (@lem5482498 _70608)). Qed.
Lemma lem5482572 (_70606 : int) (_70608 : int) : (term524 _70606 _70608) = (term595 _70606 _70608).
Proof. exact (MK_COMB (@lem5482571 _70608) (@lem5482569 _70606 _70608)). Qed.
Lemma lem5482573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482574 (_70607 : int) (_70608 : int) : (term525 _70608 _70607) = (term596 _70607 _70608).
Proof. exact (MK_COMB (@lem5482573) (@lem5482431 _70607 _70608)). Qed.
Lemma lem5482575 (_70607 : int) (_70606 : int) (_70608 : int) : (term526 _70607 _70606 _70608) = (term597 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482574 _70607 _70608) (@lem5482572 _70606 _70608)). Qed.
Lemma lem5482576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482577 (_70607 : int) (_70606 : int) (_70608 : int) : (term527 _70607 _70608 _70606) = (term598 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482576) (@lem5482364 _70607 _70606 _70608)). Qed.
Lemma lem5482578 (_70607 : int) (_70606 : int) (_70608 : int) : (term528 _70607 _70606 _70608) = (term599 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482577 _70607 _70606 _70608) (@lem5482575 _70607 _70606 _70608)). Qed.
Lemma lem5482579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482580 (_70607 : int) (_70606 : int) : (term529 _70607 _70606) = (term600 _70607 _70606).
Proof. exact (MK_COMB (@lem5482579) (@lem5482272 _70607 _70606)). Qed.
Lemma lem5482581 (_70607 : int) (_70606 : int) (_70608 : int) : (term530 _70607 _70606 _70608) = (term601 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482580 _70607 _70606) (@lem5482578 _70607 _70606 _70608)). Qed.
Lemma lem5482582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482583 (_70607 : int) : (term531 _70607) = (term602 _70607).
Proof. exact (MK_COMB (@lem5482582) (@lem5481977 _70607)). Qed.
Lemma lem5482584 (_70607 : int) (_70606 : int) (_70608 : int) : (term532 _70607 _70606 _70608) = (term603 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482583 _70607) (@lem5482581 _70607 _70606 _70608)). Qed.
Lemma lem5482585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482586 (_70608 : int) : (term152 _70608) = (term207 _70608).
Proof. exact (MK_COMB (@lem5482585) (@lem5481846 _70608)). Qed.
Lemma lem5482587 (_70607 : int) (_70606 : int) (_70608 : int) : (term533 _70607 _70606 _70608) = (term604 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482586 _70608) (@lem5482584 _70607 _70606 _70608)). Qed.
Lemma lem5482588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482589 (_70607 : int) : (term152 _70607) = (term207 _70607).
Proof. exact (MK_COMB (@lem5482588) (@lem5481798 _70607)). Qed.
Lemma lem5482590 (_70607 : int) (_70606 : int) (_70608 : int) : (term534 _70607 _70606 _70608) = (term605 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482589 _70607) (@lem5482587 _70607 _70606 _70608)). Qed.
Lemma lem5482591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5482592 (_70606 : int) : (term152 _70606) = (term207 _70606).
Proof. exact (MK_COMB (@lem5482591) (@lem5481750 _70606)). Qed.
Lemma lem5482593 (_70607 : int) (_70606 : int) (_70608 : int) : (term535 _70607 _70606 _70608) = (term606 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482592 _70606) (@lem5482590 _70607 _70606 _70608)). Qed.
Lemma lem5482600 (_70607 : int) (_70606 : int) (_70608 : int) : (term536 _70607 _70606 _70608) = (term606 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5481702 _70607 _70606 _70608) (@lem5482593 _70607 _70606 _70608)). Qed.
Lemma lem5482617 (_70607 : int) (_70606 : int) (_70608 : int) : (term597 _70607 _70606 _70608) = (term607 _70607 _70606 _70608).
Proof. exact (@lem19158 (term270 _70608) (term205 _70607 _70608) (term594 _70606 _70608)). Qed.
Lemma lem5482632 (_70607 : int) (_70606 : int) (_70608 : int) : (term598 _70607 _70606 _70608) = (term598 _70607 _70606 _70608).
Proof. exact (eq_refl (term598 _70607 _70606 _70608)). Qed.
Lemma lem5482633 (_70607 : int) (_70606 : int) (_70608 : int) : (term599 _70607 _70606 _70608) = (term608 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482632 _70607 _70606 _70608) (@lem5482617 _70607 _70606 _70608)). Qed.
Lemma lem5482646 (_70607 : int) (_70606 : int) : (term600 _70607 _70606) = (term600 _70607 _70606).
Proof. exact (eq_refl (term600 _70607 _70606)). Qed.
Lemma lem5482647 (_70607 : int) (_70606 : int) (_70608 : int) : (term601 _70607 _70606 _70608) = (term609 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482646 _70607 _70606) (@lem5482633 _70607 _70606 _70608)). Qed.
Lemma lem5482648 (_70607 : int) (_70606 : int) (_70608 : int) : (term609 _70607 _70606 _70608) = (term610 _70607 _70606 _70608).
Proof. exact (@lem19158 (term592 _70607 _70606 _70608) (term580 _70607 _70606) (term607 _70607 _70606 _70608)). Qed.
Lemma lem5482649 (_70607 : int) (_70606 : int) (_70608 : int) : (term611 _70607 _70606 _70608) = (term612 _70607 _70606 _70608).
Proof. exact (@lem19158 (term613 _70607 _70608) (term580 _70607 _70606) (term614 _70607 _70606 _70608)). Qed.
Lemma lem5482656 (_70607 : int) (_70606 : int) (_70608 : int) : (term615 _70607 _70606 _70608) = (term616 _70607 _70606 _70608).
Proof. exact (@lem19367 ((term552 _70606 _70607) = term129) (term578 _70607 _70606) (term614 _70607 _70606 _70608)). Qed.
Lemma lem5482663 (_70606 : int) (_70607 : int) (_70608 : int) : (term617 _70606 _70607 _70608) = (term618 _70606 _70607 _70608).
Proof. exact (@lem19367 ((term552 _70606 _70607) = term129) (term578 _70607 _70606) (term613 _70607 _70608)). Qed.
Lemma lem5482664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482665 (_70606 : int) (_70607 : int) (_70608 : int) : (term619 _70606 _70607 _70608) = (term620 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482664) (@lem5482663 _70606 _70607 _70608)). Qed.
Lemma lem5482666 (_70607 : int) (_70606 : int) (_70608 : int) : (term612 _70607 _70606 _70608) = (term621 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482665 _70606 _70607 _70608) (@lem5482656 _70607 _70606 _70608)). Qed.
Lemma lem5482667 (_70607 : int) (_70606 : int) (_70608 : int) : (term611 _70607 _70606 _70608) = (term621 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482649 _70607 _70606 _70608) (@lem5482666 _70607 _70606 _70608)). Qed.
Lemma lem5482674 (_70607 : int) (_70606 : int) (_70608 : int) : (term622 _70607 _70606 _70608) = (term623 _70607 _70606 _70608).
Proof. exact (@lem19367 ((term552 _70606 _70607) = term129) (term578 _70607 _70606) (term592 _70607 _70606 _70608)). Qed.
Lemma lem5482675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482676 (_70607 : int) (_70606 : int) (_70608 : int) : (term624 _70607 _70606 _70608) = (term625 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482675) (@lem5482674 _70607 _70606 _70608)). Qed.
Lemma lem5482677 (_70607 : int) (_70606 : int) (_70608 : int) : (term610 _70607 _70606 _70608) = (term626 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482676 _70607 _70606 _70608) (@lem5482667 _70607 _70606 _70608)). Qed.
Lemma lem5482678 (_70607 : int) (_70606 : int) (_70608 : int) : (term609 _70607 _70606 _70608) = (term626 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482648 _70607 _70606 _70608) (@lem5482677 _70607 _70606 _70608)). Qed.
Lemma lem5482679 (_70607 : int) (_70606 : int) (_70608 : int) : (term601 _70607 _70606 _70608) = (term626 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482647 _70607 _70606 _70608) (@lem5482678 _70607 _70606 _70608)). Qed.
Lemma lem5482686 (_70607 : int) : (term602 _70607) = (term602 _70607).
Proof. exact (eq_refl (term602 _70607)). Qed.
Lemma lem5482687 (_70607 : int) (_70606 : int) (_70608 : int) : (term603 _70607 _70606 _70608) = (term627 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482686 _70607) (@lem5482679 _70607 _70606 _70608)). Qed.
Lemma lem5482688 (_70607 : int) (_70606 : int) (_70608 : int) : (term627 _70607 _70606 _70608) = (term628 _70607 _70606 _70608).
Proof. exact (@lem19158 (term623 _70607 _70606 _70608) (term551 _70607) (term621 _70607 _70606 _70608)). Qed.
Lemma lem5482689 (_70607 : int) (_70606 : int) (_70608 : int) : (term629 _70607 _70606 _70608) = (term630 _70607 _70606 _70608).
Proof. exact (@lem19158 (term618 _70606 _70607 _70608) (term551 _70607) (term616 _70607 _70606 _70608)). Qed.
Lemma lem5482690 (_70607 : int) (_70606 : int) (_70608 : int) : (term631 _70607 _70606 _70608) = (term632 _70607 _70606 _70608).
Proof. exact (@lem19158 (term633 _70607 _70606 _70608) (term551 _70607) (term634 _70607 _70606 _70608)). Qed.
Lemma lem5482697 (_70607 : int) (_70606 : int) (_70608 : int) : (term635 _70607 _70606 _70608) = (term636 _70607 _70606 _70608).
Proof. exact (@lem19367 (term270 _70607) (term549 _70607) (term634 _70607 _70606 _70608)). Qed.
Lemma lem5482704 (_70607 : int) (_70606 : int) (_70608 : int) : (term637 _70607 _70606 _70608) = (term638 _70607 _70606 _70608).
Proof. exact (@lem19367 (term270 _70607) (term549 _70607) (term633 _70607 _70606 _70608)). Qed.
Lemma lem5482705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482706 (_70607 : int) (_70606 : int) (_70608 : int) : (term639 _70607 _70606 _70608) = (term640 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482705) (@lem5482704 _70607 _70606 _70608)). Qed.
Lemma lem5482707 (_70607 : int) (_70606 : int) (_70608 : int) : (term632 _70607 _70606 _70608) = (term641 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482706 _70607 _70606 _70608) (@lem5482697 _70607 _70606 _70608)). Qed.
Lemma lem5482708 (_70607 : int) (_70606 : int) (_70608 : int) : (term631 _70607 _70606 _70608) = (term641 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482690 _70607 _70606 _70608) (@lem5482707 _70607 _70606 _70608)). Qed.
Lemma lem5482709 (_70606 : int) (_70607 : int) (_70608 : int) : (term642 _70606 _70607 _70608) = (term643 _70606 _70607 _70608).
Proof. exact (@lem19158 (term644 _70606 _70607 _70608) (term551 _70607) (term645 _70606 _70607 _70608)). Qed.
Lemma lem5482716 (_70606 : int) (_70607 : int) (_70608 : int) : (term646 _70606 _70607 _70608) = (term647 _70606 _70607 _70608).
Proof. exact (@lem19367 (term270 _70607) (term549 _70607) (term645 _70606 _70607 _70608)). Qed.
Lemma lem5482723 (_70606 : int) (_70607 : int) (_70608 : int) : (term648 _70606 _70607 _70608) = (term649 _70606 _70607 _70608).
Proof. exact (@lem19367 (term270 _70607) (term549 _70607) (term644 _70606 _70607 _70608)). Qed.
Lemma lem5482724 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482725 (_70606 : int) (_70607 : int) (_70608 : int) : (term650 _70606 _70607 _70608) = (term651 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482724) (@lem5482723 _70606 _70607 _70608)). Qed.
Lemma lem5482726 (_70606 : int) (_70607 : int) (_70608 : int) : (term643 _70606 _70607 _70608) = (term652 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482725 _70606 _70607 _70608) (@lem5482716 _70606 _70607 _70608)). Qed.
Lemma lem5482727 (_70606 : int) (_70607 : int) (_70608 : int) : (term642 _70606 _70607 _70608) = (term652 _70606 _70607 _70608).
Proof. exact (TRANS (@lem5482709 _70606 _70607 _70608) (@lem5482726 _70606 _70607 _70608)). Qed.
Lemma lem5482728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482729 (_70606 : int) (_70607 : int) (_70608 : int) : (term653 _70606 _70607 _70608) = (term654 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482728) (@lem5482727 _70606 _70607 _70608)). Qed.
Lemma lem5482730 (_70607 : int) (_70606 : int) (_70608 : int) : (term630 _70607 _70606 _70608) = (term655 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482729 _70606 _70607 _70608) (@lem5482708 _70607 _70606 _70608)). Qed.
Lemma lem5482731 (_70607 : int) (_70606 : int) (_70608 : int) : (term629 _70607 _70606 _70608) = (term655 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482689 _70607 _70606 _70608) (@lem5482730 _70607 _70606 _70608)). Qed.
Lemma lem5482732 (_70607 : int) (_70606 : int) (_70608 : int) : (term656 _70607 _70606 _70608) = (term657 _70607 _70606 _70608).
Proof. exact (@lem19158 (term658 _70607 _70606 _70608) (term551 _70607) (term659 _70607 _70606 _70608)). Qed.
Lemma lem5482739 (_70607 : int) (_70606 : int) (_70608 : int) : (term660 _70607 _70606 _70608) = (term661 _70607 _70606 _70608).
Proof. exact (@lem19367 (term270 _70607) (term549 _70607) (term659 _70607 _70606 _70608)). Qed.
Lemma lem5482746 (_70607 : int) (_70606 : int) (_70608 : int) : (term662 _70607 _70606 _70608) = (term663 _70607 _70606 _70608).
Proof. exact (@lem19367 (term270 _70607) (term549 _70607) (term658 _70607 _70606 _70608)). Qed.
Lemma lem5482747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482748 (_70607 : int) (_70606 : int) (_70608 : int) : (term664 _70607 _70606 _70608) = (term665 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482747) (@lem5482746 _70607 _70606 _70608)). Qed.
Lemma lem5482749 (_70607 : int) (_70606 : int) (_70608 : int) : (term657 _70607 _70606 _70608) = (term666 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482748 _70607 _70606 _70608) (@lem5482739 _70607 _70606 _70608)). Qed.
Lemma lem5482750 (_70607 : int) (_70606 : int) (_70608 : int) : (term656 _70607 _70606 _70608) = (term666 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482732 _70607 _70606 _70608) (@lem5482749 _70607 _70606 _70608)). Qed.
Lemma lem5482751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482752 (_70607 : int) (_70606 : int) (_70608 : int) : (term667 _70607 _70606 _70608) = (term668 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482751) (@lem5482750 _70607 _70606 _70608)). Qed.
Lemma lem5482753 (_70607 : int) (_70606 : int) (_70608 : int) : (term628 _70607 _70606 _70608) = (term669 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482752 _70607 _70606 _70608) (@lem5482731 _70607 _70606 _70608)). Qed.
Lemma lem5482754 (_70607 : int) (_70606 : int) (_70608 : int) : (term627 _70607 _70606 _70608) = (term669 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482688 _70607 _70606 _70608) (@lem5482753 _70607 _70606 _70608)). Qed.
Lemma lem5482755 (_70607 : int) (_70606 : int) (_70608 : int) : (term603 _70607 _70606 _70608) = (term669 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482687 _70607 _70606 _70608) (@lem5482754 _70607 _70606 _70608)). Qed.
Lemma lem5482758 (_70608 : int) : (term207 _70608) = (term207 _70608).
Proof. exact (eq_refl (term207 _70608)). Qed.
Lemma lem5482759 (_70607 : int) (_70606 : int) (_70608 : int) : (term604 _70607 _70606 _70608) = (term670 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482758 _70608) (@lem5482755 _70607 _70606 _70608)). Qed.
Lemma lem5482760 (_70607 : int) (_70606 : int) (_70608 : int) : (term670 _70607 _70606 _70608) = (term671 _70607 _70606 _70608).
Proof. exact (@lem19158 (term666 _70607 _70606 _70608) (term184 _70608) (term655 _70607 _70606 _70608)). Qed.
Lemma lem5482761 (_70607 : int) (_70606 : int) (_70608 : int) : (term672 _70607 _70606 _70608) = (term673 _70607 _70606 _70608).
Proof. exact (@lem19158 (term652 _70606 _70607 _70608) (term184 _70608) (term641 _70607 _70606 _70608)). Qed.
Lemma lem5482762 (_70607 : int) (_70606 : int) (_70608 : int) : (term674 _70607 _70606 _70608) = (term675 _70607 _70606 _70608).
Proof. exact (@lem19158 (term638 _70607 _70606 _70608) (term184 _70608) (term636 _70607 _70606 _70608)). Qed.
Lemma lem5482769 (_70607 : int) (_70606 : int) (_70608 : int) : (term676 _70607 _70606 _70608) = (term677 _70607 _70606 _70608).
Proof. exact (@lem19158 (term678 _70607 _70606 _70608) (term184 _70608) (term679 _70607 _70606 _70608)). Qed.
Lemma lem5482776 (_70607 : int) (_70606 : int) (_70608 : int) : (term680 _70607 _70606 _70608) = (term681 _70607 _70606 _70608).
Proof. exact (@lem19158 (term682 _70607 _70606 _70608) (term184 _70608) (term683 _70607 _70606 _70608)). Qed.
Lemma lem5482777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482778 (_70607 : int) (_70606 : int) (_70608 : int) : (term684 _70607 _70606 _70608) = (term685 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482777) (@lem5482776 _70607 _70606 _70608)). Qed.
Lemma lem5482779 (_70607 : int) (_70606 : int) (_70608 : int) : (term675 _70607 _70606 _70608) = (term686 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482778 _70607 _70606 _70608) (@lem5482769 _70607 _70606 _70608)). Qed.
Lemma lem5482780 (_70607 : int) (_70606 : int) (_70608 : int) : (term674 _70607 _70606 _70608) = (term686 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482762 _70607 _70606 _70608) (@lem5482779 _70607 _70606 _70608)). Qed.
Lemma lem5482781 (_70606 : int) (_70607 : int) (_70608 : int) : (term687 _70606 _70607 _70608) = (term688 _70606 _70607 _70608).
Proof. exact (@lem19158 (term649 _70606 _70607 _70608) (term184 _70608) (term647 _70606 _70607 _70608)). Qed.
Lemma lem5482788 (_70606 : int) (_70607 : int) (_70608 : int) : (term689 _70606 _70607 _70608) = (term690 _70606 _70607 _70608).
Proof. exact (@lem19158 (term691 _70606 _70607 _70608) (term184 _70608) (term692 _70606 _70607 _70608)). Qed.
Lemma lem5482795 (_70606 : int) (_70607 : int) (_70608 : int) : (term693 _70606 _70607 _70608) = (term694 _70606 _70607 _70608).
Proof. exact (@lem19158 (term695 _70606 _70607 _70608) (term184 _70608) (term696 _70606 _70607 _70608)). Qed.
Lemma lem5482796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482797 (_70606 : int) (_70607 : int) (_70608 : int) : (term697 _70606 _70607 _70608) = (term698 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482796) (@lem5482795 _70606 _70607 _70608)). Qed.
Lemma lem5482798 (_70606 : int) (_70607 : int) (_70608 : int) : (term688 _70606 _70607 _70608) = (term699 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482797 _70606 _70607 _70608) (@lem5482788 _70606 _70607 _70608)). Qed.
Lemma lem5482799 (_70606 : int) (_70607 : int) (_70608 : int) : (term687 _70606 _70607 _70608) = (term699 _70606 _70607 _70608).
Proof. exact (TRANS (@lem5482781 _70606 _70607 _70608) (@lem5482798 _70606 _70607 _70608)). Qed.
Lemma lem5482800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482801 (_70606 : int) (_70607 : int) (_70608 : int) : (term700 _70606 _70607 _70608) = (term701 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482800) (@lem5482799 _70606 _70607 _70608)). Qed.
Lemma lem5482802 (_70607 : int) (_70606 : int) (_70608 : int) : (term673 _70607 _70606 _70608) = (term702 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482801 _70606 _70607 _70608) (@lem5482780 _70607 _70606 _70608)). Qed.
Lemma lem5482803 (_70607 : int) (_70606 : int) (_70608 : int) : (term672 _70607 _70606 _70608) = (term702 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482761 _70607 _70606 _70608) (@lem5482802 _70607 _70606 _70608)). Qed.
Lemma lem5482804 (_70607 : int) (_70606 : int) (_70608 : int) : (term703 _70607 _70606 _70608) = (term704 _70607 _70606 _70608).
Proof. exact (@lem19158 (term663 _70607 _70606 _70608) (term184 _70608) (term661 _70607 _70606 _70608)). Qed.
Lemma lem5482811 (_70607 : int) (_70606 : int) (_70608 : int) : (term705 _70607 _70606 _70608) = (term706 _70607 _70606 _70608).
Proof. exact (@lem19158 (term707 _70607 _70606 _70608) (term184 _70608) (term708 _70607 _70606 _70608)). Qed.
Lemma lem5482818 (_70607 : int) (_70606 : int) (_70608 : int) : (term709 _70607 _70606 _70608) = (term710 _70607 _70606 _70608).
Proof. exact (@lem19158 (term711 _70607 _70606 _70608) (term184 _70608) (term712 _70607 _70606 _70608)). Qed.
Lemma lem5482819 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482820 (_70607 : int) (_70606 : int) (_70608 : int) : (term713 _70607 _70606 _70608) = (term714 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482819) (@lem5482818 _70607 _70606 _70608)). Qed.
Lemma lem5482821 (_70607 : int) (_70606 : int) (_70608 : int) : (term704 _70607 _70606 _70608) = (term715 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482820 _70607 _70606 _70608) (@lem5482811 _70607 _70606 _70608)). Qed.
Lemma lem5482822 (_70607 : int) (_70606 : int) (_70608 : int) : (term703 _70607 _70606 _70608) = (term715 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482804 _70607 _70606 _70608) (@lem5482821 _70607 _70606 _70608)). Qed.
Lemma lem5482823 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482824 (_70607 : int) (_70606 : int) (_70608 : int) : (term716 _70607 _70606 _70608) = (term717 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482823) (@lem5482822 _70607 _70606 _70608)). Qed.
Lemma lem5482825 (_70607 : int) (_70606 : int) (_70608 : int) : (term671 _70607 _70606 _70608) = (term718 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482824 _70607 _70606 _70608) (@lem5482803 _70607 _70606 _70608)). Qed.
Lemma lem5482826 (_70607 : int) (_70606 : int) (_70608 : int) : (term670 _70607 _70606 _70608) = (term718 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482760 _70607 _70606 _70608) (@lem5482825 _70607 _70606 _70608)). Qed.
Lemma lem5482827 (_70607 : int) (_70606 : int) (_70608 : int) : (term604 _70607 _70606 _70608) = (term718 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482759 _70607 _70606 _70608) (@lem5482826 _70607 _70606 _70608)). Qed.
Lemma lem5482830 (_70607 : int) : (term207 _70607) = (term207 _70607).
Proof. exact (eq_refl (term207 _70607)). Qed.
Lemma lem5482831 (_70607 : int) (_70606 : int) (_70608 : int) : (term605 _70607 _70606 _70608) = (term719 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482830 _70607) (@lem5482827 _70607 _70606 _70608)). Qed.
Lemma lem5482832 (_70607 : int) (_70606 : int) (_70608 : int) : (term719 _70607 _70606 _70608) = (term720 _70607 _70606 _70608).
Proof. exact (@lem19158 (term715 _70607 _70606 _70608) (term184 _70607) (term702 _70607 _70606 _70608)). Qed.
Lemma lem5482833 (_70607 : int) (_70606 : int) (_70608 : int) : (term721 _70607 _70606 _70608) = (term722 _70607 _70606 _70608).
Proof. exact (@lem19158 (term699 _70606 _70607 _70608) (term184 _70607) (term686 _70607 _70606 _70608)). Qed.
Lemma lem5482834 (_70607 : int) (_70606 : int) (_70608 : int) : (term723 _70607 _70606 _70608) = (term724 _70607 _70606 _70608).
Proof. exact (@lem19158 (term681 _70607 _70606 _70608) (term184 _70607) (term677 _70607 _70606 _70608)). Qed.
Lemma lem5482841 (_70607 : int) (_70606 : int) (_70608 : int) : (term725 _70607 _70606 _70608) = (term726 _70607 _70606 _70608).
Proof. exact (@lem19158 (term727 _70607 _70606 _70608) (term184 _70607) (term728 _70607 _70606 _70608)). Qed.
Lemma lem5482848 (_70607 : int) (_70606 : int) (_70608 : int) : (term729 _70607 _70606 _70608) = (term730 _70607 _70606 _70608).
Proof. exact (@lem19158 (term731 _70607 _70606 _70608) (term184 _70607) (term732 _70607 _70606 _70608)). Qed.
Lemma lem5482849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482850 (_70607 : int) (_70606 : int) (_70608 : int) : (term733 _70607 _70606 _70608) = (term734 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482849) (@lem5482848 _70607 _70606 _70608)). Qed.
Lemma lem5482851 (_70607 : int) (_70606 : int) (_70608 : int) : (term724 _70607 _70606 _70608) = (term735 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482850 _70607 _70606 _70608) (@lem5482841 _70607 _70606 _70608)). Qed.
Lemma lem5482852 (_70607 : int) (_70606 : int) (_70608 : int) : (term723 _70607 _70606 _70608) = (term735 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482834 _70607 _70606 _70608) (@lem5482851 _70607 _70606 _70608)). Qed.
Lemma lem5482853 (_70606 : int) (_70607 : int) (_70608 : int) : (term736 _70606 _70607 _70608) = (term737 _70606 _70607 _70608).
Proof. exact (@lem19158 (term694 _70606 _70607 _70608) (term184 _70607) (term690 _70606 _70607 _70608)). Qed.
Lemma lem5482860 (_70606 : int) (_70607 : int) (_70608 : int) : (term738 _70606 _70607 _70608) = (term739 _70606 _70607 _70608).
Proof. exact (@lem19158 (term740 _70606 _70607 _70608) (term184 _70607) (term741 _70606 _70607 _70608)). Qed.
Lemma lem5482867 (_70606 : int) (_70607 : int) (_70608 : int) : (term742 _70606 _70607 _70608) = (term743 _70606 _70607 _70608).
Proof. exact (@lem19158 (term744 _70606 _70607 _70608) (term184 _70607) (term745 _70606 _70607 _70608)). Qed.
Lemma lem5482868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482869 (_70606 : int) (_70607 : int) (_70608 : int) : (term746 _70606 _70607 _70608) = (term747 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482868) (@lem5482867 _70606 _70607 _70608)). Qed.
Lemma lem5482870 (_70606 : int) (_70607 : int) (_70608 : int) : (term737 _70606 _70607 _70608) = (term748 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482869 _70606 _70607 _70608) (@lem5482860 _70606 _70607 _70608)). Qed.
Lemma lem5482871 (_70606 : int) (_70607 : int) (_70608 : int) : (term736 _70606 _70607 _70608) = (term748 _70606 _70607 _70608).
Proof. exact (TRANS (@lem5482853 _70606 _70607 _70608) (@lem5482870 _70606 _70607 _70608)). Qed.
Lemma lem5482872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482873 (_70606 : int) (_70607 : int) (_70608 : int) : (term749 _70606 _70607 _70608) = (term750 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482872) (@lem5482871 _70606 _70607 _70608)). Qed.
Lemma lem5482874 (_70607 : int) (_70606 : int) (_70608 : int) : (term722 _70607 _70606 _70608) = (term751 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482873 _70606 _70607 _70608) (@lem5482852 _70607 _70606 _70608)). Qed.
Lemma lem5482875 (_70607 : int) (_70606 : int) (_70608 : int) : (term721 _70607 _70606 _70608) = (term751 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482833 _70607 _70606 _70608) (@lem5482874 _70607 _70606 _70608)). Qed.
Lemma lem5482876 (_70607 : int) (_70606 : int) (_70608 : int) : (term752 _70607 _70606 _70608) = (term753 _70607 _70606 _70608).
Proof. exact (@lem19158 (term710 _70607 _70606 _70608) (term184 _70607) (term706 _70607 _70606 _70608)). Qed.
Lemma lem5482883 (_70607 : int) (_70606 : int) (_70608 : int) : (term754 _70607 _70606 _70608) = (term755 _70607 _70606 _70608).
Proof. exact (@lem19158 (term756 _70607 _70606 _70608) (term184 _70607) (term757 _70607 _70606 _70608)). Qed.
Lemma lem5482890 (_70607 : int) (_70606 : int) (_70608 : int) : (term758 _70607 _70606 _70608) = (term759 _70607 _70606 _70608).
Proof. exact (@lem19158 (term760 _70607 _70606 _70608) (term184 _70607) (term761 _70607 _70606 _70608)). Qed.
Lemma lem5482891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482892 (_70607 : int) (_70606 : int) (_70608 : int) : (term762 _70607 _70606 _70608) = (term763 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482891) (@lem5482890 _70607 _70606 _70608)). Qed.
Lemma lem5482893 (_70607 : int) (_70606 : int) (_70608 : int) : (term753 _70607 _70606 _70608) = (term764 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482892 _70607 _70606 _70608) (@lem5482883 _70607 _70606 _70608)). Qed.
Lemma lem5482894 (_70607 : int) (_70606 : int) (_70608 : int) : (term752 _70607 _70606 _70608) = (term764 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482876 _70607 _70606 _70608) (@lem5482893 _70607 _70606 _70608)). Qed.
Lemma lem5482895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482896 (_70607 : int) (_70606 : int) (_70608 : int) : (term765 _70607 _70606 _70608) = (term766 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482895) (@lem5482894 _70607 _70606 _70608)). Qed.
Lemma lem5482897 (_70607 : int) (_70606 : int) (_70608 : int) : (term720 _70607 _70606 _70608) = (term767 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482896 _70607 _70606 _70608) (@lem5482875 _70607 _70606 _70608)). Qed.
Lemma lem5482898 (_70607 : int) (_70606 : int) (_70608 : int) : (term719 _70607 _70606 _70608) = (term767 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482832 _70607 _70606 _70608) (@lem5482897 _70607 _70606 _70608)). Qed.
Lemma lem5482899 (_70607 : int) (_70606 : int) (_70608 : int) : (term605 _70607 _70606 _70608) = (term767 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482831 _70607 _70606 _70608) (@lem5482898 _70607 _70606 _70608)). Qed.
Lemma lem5482902 (_70606 : int) : (term207 _70606) = (term207 _70606).
Proof. exact (eq_refl (term207 _70606)). Qed.
Lemma lem5482903 (_70607 : int) (_70606 : int) (_70608 : int) : (term606 _70607 _70606 _70608) = (term768 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482902 _70606) (@lem5482899 _70607 _70606 _70608)). Qed.
Lemma lem5482904 (_70607 : int) (_70606 : int) (_70608 : int) : (term768 _70607 _70606 _70608) = (term769 _70607 _70606 _70608).
Proof. exact (@lem19158 (term764 _70607 _70606 _70608) (term184 _70606) (term751 _70607 _70606 _70608)). Qed.
Lemma lem5482905 (_70607 : int) (_70606 : int) (_70608 : int) : (term770 _70607 _70606 _70608) = (term771 _70607 _70606 _70608).
Proof. exact (@lem19158 (term748 _70606 _70607 _70608) (term184 _70606) (term735 _70607 _70606 _70608)). Qed.
Lemma lem5482906 (_70607 : int) (_70606 : int) (_70608 : int) : (term772 _70607 _70606 _70608) = (term773 _70607 _70606 _70608).
Proof. exact (@lem19158 (term730 _70607 _70606 _70608) (term184 _70606) (term726 _70607 _70606 _70608)). Qed.
Lemma lem5482913 (_70607 : int) (_70606 : int) (_70608 : int) : (term774 _70607 _70606 _70608) = (term775 _70607 _70606 _70608).
Proof. exact (@lem19158 (term776 _70607 _70606 _70608) (term184 _70606) (term777 _70607 _70606 _70608)). Qed.
Lemma lem5482920 (_70607 : int) (_70606 : int) (_70608 : int) : (term778 _70607 _70606 _70608) = (term779 _70607 _70606 _70608).
Proof. exact (@lem19158 (term780 _70607 _70606 _70608) (term184 _70606) (term781 _70607 _70606 _70608)). Qed.
Lemma lem5482921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482922 (_70607 : int) (_70606 : int) (_70608 : int) : (term782 _70607 _70606 _70608) = (term783 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482921) (@lem5482920 _70607 _70606 _70608)). Qed.
Lemma lem5482923 (_70607 : int) (_70606 : int) (_70608 : int) : (term773 _70607 _70606 _70608) = (term784 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482922 _70607 _70606 _70608) (@lem5482913 _70607 _70606 _70608)). Qed.
Lemma lem5482924 (_70607 : int) (_70606 : int) (_70608 : int) : (term772 _70607 _70606 _70608) = (term784 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482906 _70607 _70606 _70608) (@lem5482923 _70607 _70606 _70608)). Qed.
Lemma lem5482925 (_70606 : int) (_70607 : int) (_70608 : int) : (term785 _70606 _70607 _70608) = (term786 _70606 _70607 _70608).
Proof. exact (@lem19158 (term743 _70606 _70607 _70608) (term184 _70606) (term739 _70606 _70607 _70608)). Qed.
Lemma lem5482932 (_70606 : int) (_70607 : int) (_70608 : int) : (term787 _70606 _70607 _70608) = (term788 _70606 _70607 _70608).
Proof. exact (@lem19158 (term789 _70606 _70607 _70608) (term184 _70606) (term790 _70606 _70607 _70608)). Qed.
Lemma lem5482939 (_70606 : int) (_70607 : int) (_70608 : int) : (term791 _70606 _70607 _70608) = (term792 _70606 _70607 _70608).
Proof. exact (@lem19158 (term793 _70606 _70607 _70608) (term184 _70606) (term794 _70606 _70607 _70608)). Qed.
Lemma lem5482940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482941 (_70606 : int) (_70607 : int) (_70608 : int) : (term795 _70606 _70607 _70608) = (term796 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482940) (@lem5482939 _70606 _70607 _70608)). Qed.
Lemma lem5482942 (_70606 : int) (_70607 : int) (_70608 : int) : (term786 _70606 _70607 _70608) = (term797 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482941 _70606 _70607 _70608) (@lem5482932 _70606 _70607 _70608)). Qed.
Lemma lem5482943 (_70606 : int) (_70607 : int) (_70608 : int) : (term785 _70606 _70607 _70608) = (term797 _70606 _70607 _70608).
Proof. exact (TRANS (@lem5482925 _70606 _70607 _70608) (@lem5482942 _70606 _70607 _70608)). Qed.
Lemma lem5482944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482945 (_70606 : int) (_70607 : int) (_70608 : int) : (term798 _70606 _70607 _70608) = (term799 _70606 _70607 _70608).
Proof. exact (MK_COMB (@lem5482944) (@lem5482943 _70606 _70607 _70608)). Qed.
Lemma lem5482946 (_70607 : int) (_70606 : int) (_70608 : int) : (term771 _70607 _70606 _70608) = (term800 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482945 _70606 _70607 _70608) (@lem5482924 _70607 _70606 _70608)). Qed.
Lemma lem5482947 (_70607 : int) (_70606 : int) (_70608 : int) : (term770 _70607 _70606 _70608) = (term800 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482905 _70607 _70606 _70608) (@lem5482946 _70607 _70606 _70608)). Qed.
Lemma lem5482948 (_70607 : int) (_70606 : int) (_70608 : int) : (term801 _70607 _70606 _70608) = (term802 _70607 _70606 _70608).
Proof. exact (@lem19158 (term759 _70607 _70606 _70608) (term184 _70606) (term755 _70607 _70606 _70608)). Qed.
Lemma lem5482955 (_70607 : int) (_70606 : int) (_70608 : int) : (term803 _70607 _70606 _70608) = (term804 _70607 _70606 _70608).
Proof. exact (@lem19158 (term805 _70607 _70606 _70608) (term184 _70606) (term806 _70607 _70606 _70608)). Qed.
Lemma lem5482962 (_70607 : int) (_70606 : int) (_70608 : int) : (term807 _70607 _70606 _70608) = (term808 _70607 _70606 _70608).
Proof. exact (@lem19158 (term809 _70607 _70606 _70608) (term184 _70606) (term810 _70607 _70606 _70608)). Qed.
Lemma lem5482963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482964 (_70607 : int) (_70606 : int) (_70608 : int) : (term811 _70607 _70606 _70608) = (term812 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482963) (@lem5482962 _70607 _70606 _70608)). Qed.
Lemma lem5482965 (_70607 : int) (_70606 : int) (_70608 : int) : (term802 _70607 _70606 _70608) = (term813 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482964 _70607 _70606 _70608) (@lem5482955 _70607 _70606 _70608)). Qed.
Lemma lem5482966 (_70607 : int) (_70606 : int) (_70608 : int) : (term801 _70607 _70606 _70608) = (term813 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482948 _70607 _70606 _70608) (@lem5482965 _70607 _70606 _70608)). Qed.
Lemma lem5482967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5482968 (_70607 : int) (_70606 : int) (_70608 : int) : (term814 _70607 _70606 _70608) = (term815 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482967) (@lem5482966 _70607 _70606 _70608)). Qed.
Lemma lem5482969 (_70607 : int) (_70606 : int) (_70608 : int) : (term769 _70607 _70606 _70608) = (term816 _70607 _70606 _70608).
Proof. exact (MK_COMB (@lem5482968 _70607 _70606 _70608) (@lem5482947 _70607 _70606 _70608)). Qed.
Lemma lem5482970 (_70607 : int) (_70606 : int) (_70608 : int) : (term768 _70607 _70606 _70608) = (term816 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482904 _70607 _70606 _70608) (@lem5482969 _70607 _70606 _70608)). Qed.
Lemma lem5482971 (_70607 : int) (_70606 : int) (_70608 : int) : (term606 _70607 _70606 _70608) = (term816 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482903 _70607 _70606 _70608) (@lem5482970 _70607 _70606 _70608)). Qed.
Lemma lem5482972 (_70607 : int) (_70606 : int) (_70608 : int) : (term536 _70607 _70606 _70608) = (term816 _70607 _70606 _70608).
Proof. exact (TRANS (@lem5482600 _70607 _70606 _70608) (@lem5482971 _70607 _70606 _70608)). Qed.
Lemma lem5483042 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term816 _70607 _70606 _70608) : term816 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5483043 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term813 _70607 _70606 _70608) : term813 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5483044 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term808 _70607 _70606 _70608) : term808 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5483045 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term817 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5483046 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term809 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483045 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483048 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term760 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483046 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483050 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term711 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483048 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483052 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term658 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483050 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483054 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term592 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483052 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483055 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : (term552 _70606 _70607) = term129.
Proof. exact (proj1 (@lem5483052 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483056 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term590 _70606 _70608.
Proof. exact (proj2 (@lem5483054 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483057 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term587 _70607 _70608.
Proof. exact (proj1 (@lem5483054 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483058 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (proj2 (@lem5483056 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483061 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5483062 : term210 = term211.
Proof. exact (@lem5483061 term129 term143). Qed.
Lemma lem5483064 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483065 : term143 = term191.
Proof. exact (@lem5483064 term144). Qed.
Lemma lem5483067 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483068 : term129 = term161.
Proof. exact (@lem5483067 (NUMERAL 0)). Qed.
Lemma lem5483069 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483070 : term212 = term213.
Proof. exact (MK_COMB (@lem5483069) (@lem5483068)). Qed.
Lemma lem5483071 : term211 = term214.
Proof. exact (MK_COMB (@lem5483070) (@lem5483065)). Qed.
Lemma lem5483072 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5483074 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483075 : term211 = term217.
Proof. exact (@lem5483074 (NUMERAL 0) term144). Qed.
Lemma lem5483076 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483077 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483078 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483077 h1) (fun h1 : term217 = True => @lem5483076)). Qed.
Lemma lem5483079 : term217 = True.
Proof. exact (EQ_MP (@lem5483078) (@lem5483076)). Qed.
Lemma lem5483080 : term211 = True.
Proof. exact (TRANS (@lem5483075) (@lem5483079)). Qed.
Lemma lem5483081 : True = term211.
Proof. exact (SYM (@lem5483080)). Qed.
Lemma lem5483082 : term211.
Proof. exact (EQ_MP (@lem5483081) (@lem0)). Qed.
Lemma lem5483083 : term219.
Proof. exact (@lem5483072 (@lem5483082)). Qed.
Lemma lem5483085 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483086 : term211 = term217.
Proof. exact (@lem5483085 (NUMERAL 0) term144). Qed.
Lemma lem5483087 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483088 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483089 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483088 h1) (fun h1 : term217 = True => @lem5483087)). Qed.
Lemma lem5483090 : term217 = True.
Proof. exact (EQ_MP (@lem5483089) (@lem5483087)). Qed.
Lemma lem5483091 : term211 = True.
Proof. exact (TRANS (@lem5483086) (@lem5483090)). Qed.
Lemma lem5483092 : True = term211.
Proof. exact (SYM (@lem5483091)). Qed.
Lemma lem5483093 : term211.
Proof. exact (EQ_MP (@lem5483092) (@lem0)). Qed.
Lemma lem5483094 : term214 = term220.
Proof. exact (@lem5483083 (@lem5483093)). Qed.
Lemma lem5483096 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483097 : term173 = term174.
Proof. exact (@lem5483096 term144 term144). Qed.
Lemma lem5483098 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483099 : term176 = term144.
Proof. exact (EQ_MP (@lem5483098) (@lem940073)). Qed.
Lemma lem5483100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483101 : term174 = term143.
Proof. exact (MK_COMB (@lem5483100) (@lem5483099)). Qed.
Lemma lem5483102 : term173 = term143.
Proof. exact (TRANS (@lem5483097) (@lem5483101)). Qed.
Lemma lem5483104 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483105 : term222 = term129.
Proof. exact (@lem5483104 term144). Qed.
Lemma lem5483106 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483107 : term223 = term212.
Proof. exact (MK_COMB (@lem5483106) (@lem5483105)). Qed.
Lemma lem5483108 : term220 = term211.
Proof. exact (MK_COMB (@lem5483107) (@lem5483102)). Qed.
Lemma lem5483110 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483111 : term211 = term217.
Proof. exact (@lem5483110 (NUMERAL 0) term144). Qed.
Lemma lem5483112 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483113 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483114 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483113 h1) (fun h1 : term217 = True => @lem5483112)). Qed.
Lemma lem5483115 : term217 = True.
Proof. exact (EQ_MP (@lem5483114) (@lem5483112)). Qed.
Lemma lem5483116 : term211 = True.
Proof. exact (TRANS (@lem5483111) (@lem5483115)). Qed.
Lemma lem5483117 : term220 = True.
Proof. exact (TRANS (@lem5483108) (@lem5483116)). Qed.
Lemma lem5483118 : term214 = True.
Proof. exact (TRANS (@lem5483094) (@lem5483117)). Qed.
Lemma lem5483119 : term211 = True.
Proof. exact (TRANS (@lem5483071) (@lem5483118)). Qed.
Lemma lem5483120 : term210 = True.
Proof. exact (TRANS (@lem5483062) (@lem5483119)). Qed.
Lemma lem5483121 : True = term210.
Proof. exact (SYM (@lem5483120)). Qed.
Lemma lem5483122 : term210.
Proof. exact (EQ_MP (@lem5483121) (@lem0)). Qed.
Lemma lem5483123 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term818 _70607 _70608.
Proof. exact (conj (@lem5483122) (@lem5483057 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483125 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5483126 (_70607 : int) (_70608 : int) : term819 _70607 _70608.
Proof. exact (@lem5483125 term143 (term584 _70607 _70608)). Qed.
Lemma lem5483127 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term820 _70607 _70608.
Proof. exact (@lem5483126 _70607 _70608 (@lem5483123 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483128 (_70607 : int) (_70608 : int) : (term821 _70607 _70608) = (term584 _70607 _70608).
Proof. exact (@lem1982733 (term584 _70607 _70608)). Qed.
Lemma lem5483129 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5483130 (_70607 : int) (_70608 : int) : (term822 _70607 _70608) = (term586 _70607 _70608).
Proof. exact (MK_COMB (@lem5483129) (@lem5483128 _70607 _70608)). Qed.
Lemma lem5483131 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483132 (_70607 : int) (_70608 : int) : (term820 _70607 _70608) = (term587 _70607 _70608).
Proof. exact (MK_COMB (@lem5483130 _70607 _70608) (@lem5483131)). Qed.
Lemma lem5483133 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term587 _70607 _70608.
Proof. exact (EQ_MP (@lem5483132 _70607 _70608) (@lem5483127 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483135 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5483136 (_70606 : int) (_70607 : int) : term823 _70606 _70607.
Proof. exact (@lem5483135 (term552 _70606 _70607)). Qed.
Lemma lem5483137 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term824 _70606 _70607.
Proof. exact (@lem5483136 _70606 _70607 (@lem5483055 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483138 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term825 _70606 _70607.
Proof. exact (@lem5483137 _70607 _70606 _70608 h1 term143). Qed.
Lemma lem5483139 (_70606 : int) (_70607 : int) : (term825 _70606 _70607) = ((term826 _70606 _70607) = term129).
Proof. exact (eq_refl (term825 _70606 _70607)). Qed.
Lemma lem5483140 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : (term826 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5483139 _70606 _70607) (@lem5483138 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483141 (_70606 : int) (_70607 : int) : (term826 _70606 _70607) = (term552 _70606 _70607).
Proof. exact (@lem1982733 (term552 _70606 _70607)). Qed.
Lemma lem5483142 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5483143 (_70606 : int) (_70607 : int) : (term827 _70606 _70607) = (term554 _70606 _70607).
Proof. exact (MK_COMB (@lem5483142) (@lem5483141 _70606 _70607)). Qed.
Lemma lem5483144 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483145 (_70606 : int) (_70607 : int) : ((term826 _70606 _70607) = term129) = ((term552 _70606 _70607) = term129).
Proof. exact (MK_COMB (@lem5483143 _70606 _70607) (@lem5483144)). Qed.
Lemma lem5483146 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : (term552 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5483145 _70606 _70607) (@lem5483140 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483147 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term828 _70606 _70607 _70608.
Proof. exact (conj (@lem5483146 _70607 _70606 _70608 h1) (@lem5483133 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483149 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5483150 (_70606 : int) (_70607 : int) (_70608 : int) : term829 _70606 _70607 _70608.
Proof. exact (@lem5483149 (term552 _70606 _70607) (term584 _70607 _70608)). Qed.
Lemma lem5483151 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term830 _70606 _70607 _70608.
Proof. exact (@lem5483150 _70606 _70607 _70608 (@lem5483147 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483152 (_70606 : int) (_70607 : int) (_70608 : int) : (term831 _70606 _70607 _70608) = (term832 _70606 _70607 _70608).
Proof. exact (@lem1982755 (term239 _70606) (term546 _70607) (term584 _70607 _70608)). Qed.
Lemma lem5483153 (_70607 : int) (_70608 : int) : (term833 _70607 _70608) = (term834 _70607 _70608).
Proof. exact (@lem1982753 (real_of_int _70607) (term239 _70607) term164 (real_of_int _70608)). Qed.
Lemma lem5483154 (_70607 : int) : (term835 _70607) = (term247 _70607).
Proof. exact (@lem1982715 term164 (real_of_int _70607)). Qed.
Lemma lem5483156 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483157 : term143 = term191.
Proof. exact (@lem5483156 term144). Qed.
Lemma lem5483159 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5483160 : term164 = term165.
Proof. exact (@lem5483159 term144). Qed.
Lemma lem5483161 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483162 : term248 = term249.
Proof. exact (MK_COMB (@lem5483161) (@lem5483160)). Qed.
Lemma lem5483163 : term250 = term251.
Proof. exact (MK_COMB (@lem5483162) (@lem5483157)). Qed.
Lemma lem5483164 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5483166 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483167 : term211 = term217.
Proof. exact (@lem5483166 (NUMERAL 0) term144). Qed.
Lemma lem5483168 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483169 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483170 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483169 h1) (fun h1 : term217 = True => @lem5483168)). Qed.
Lemma lem5483171 : term217 = True.
Proof. exact (EQ_MP (@lem5483170) (@lem5483168)). Qed.
Lemma lem5483172 : term211 = True.
Proof. exact (TRANS (@lem5483167) (@lem5483171)). Qed.
Lemma lem5483173 : True = term211.
Proof. exact (SYM (@lem5483172)). Qed.
Lemma lem5483174 : term211.
Proof. exact (EQ_MP (@lem5483173) (@lem0)). Qed.
Lemma lem5483175 : term253.
Proof. exact (@lem5483164 (@lem5483174)). Qed.
Lemma lem5483177 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483178 : term211 = term217.
Proof. exact (@lem5483177 (NUMERAL 0) term144). Qed.
Lemma lem5483179 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483180 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483181 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483180 h1) (fun h1 : term217 = True => @lem5483179)). Qed.
Lemma lem5483182 : term217 = True.
Proof. exact (EQ_MP (@lem5483181) (@lem5483179)). Qed.
Lemma lem5483183 : term211 = True.
Proof. exact (TRANS (@lem5483178) (@lem5483182)). Qed.
Lemma lem5483184 : True = term211.
Proof. exact (SYM (@lem5483183)). Qed.
Lemma lem5483185 : term211.
Proof. exact (EQ_MP (@lem5483184) (@lem0)). Qed.
Lemma lem5483186 : term254.
Proof. exact (@lem5483175 (@lem5483185)). Qed.
Lemma lem5483188 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483189 : term211 = term217.
Proof. exact (@lem5483188 (NUMERAL 0) term144). Qed.
Lemma lem5483190 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483191 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483192 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483191 h1) (fun h1 : term217 = True => @lem5483190)). Qed.
Lemma lem5483193 : term217 = True.
Proof. exact (EQ_MP (@lem5483192) (@lem5483190)). Qed.
Lemma lem5483194 : term211 = True.
Proof. exact (TRANS (@lem5483189) (@lem5483193)). Qed.
Lemma lem5483195 : True = term211.
Proof. exact (SYM (@lem5483194)). Qed.
Lemma lem5483196 : term211.
Proof. exact (EQ_MP (@lem5483195) (@lem0)). Qed.
Lemma lem5483197 : term255.
Proof. exact (@lem5483186 (@lem5483196)). Qed.
Lemma lem5483199 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483200 : term173 = term174.
Proof. exact (@lem5483199 term144 term144). Qed.
Lemma lem5483201 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483202 : term176 = term144.
Proof. exact (EQ_MP (@lem5483201) (@lem940073)). Qed.
Lemma lem5483203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483204 : term174 = term143.
Proof. exact (MK_COMB (@lem5483203) (@lem5483202)). Qed.
Lemma lem5483205 : term173 = term143.
Proof. exact (TRANS (@lem5483200) (@lem5483204)). Qed.
Lemma lem5483207 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5483208 : term192 = term197.
Proof. exact (@lem5483207 term144 term144). Qed.
Lemma lem5483209 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483210 : term176 = term144.
Proof. exact (EQ_MP (@lem5483209) (@lem940073)). Qed.
Lemma lem5483211 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483212 : term174 = term143.
Proof. exact (MK_COMB (@lem5483211) (@lem5483210)). Qed.
Lemma lem5483213 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5483214 : term197 = term164.
Proof. exact (MK_COMB (@lem5483213) (@lem5483212)). Qed.
Lemma lem5483215 : term192 = term164.
Proof. exact (TRANS (@lem5483208) (@lem5483214)). Qed.
Lemma lem5483216 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483217 : term256 = term248.
Proof. exact (MK_COMB (@lem5483216) (@lem5483215)). Qed.
Lemma lem5483218 : term257 = term250.
Proof. exact (MK_COMB (@lem5483217) (@lem5483205)). Qed.
Lemma lem5483220 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5483221 : term250 = term129.
Proof. exact (@lem5483220 term144). Qed.
Lemma lem5483222 : term257 = term129.
Proof. exact (TRANS (@lem5483218) (@lem5483221)). Qed.
Lemma lem5483223 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483224 : term259 = term260.
Proof. exact (MK_COMB (@lem5483223) (@lem5483222)). Qed.
Lemma lem5483225 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5483226 : term261 = term222.
Proof. exact (MK_COMB (@lem5483224) (@lem5483225)). Qed.
Lemma lem5483228 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483229 : term222 = term129.
Proof. exact (@lem5483228 term144). Qed.
Lemma lem5483230 : term261 = term129.
Proof. exact (TRANS (@lem5483226) (@lem5483229)). Qed.
Lemma lem5483232 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483233 : term173 = term174.
Proof. exact (@lem5483232 term144 term144). Qed.
Lemma lem5483234 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483235 : term176 = term144.
Proof. exact (EQ_MP (@lem5483234) (@lem940073)). Qed.
Lemma lem5483236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483237 : term174 = term143.
Proof. exact (MK_COMB (@lem5483236) (@lem5483235)). Qed.
Lemma lem5483238 : term173 = term143.
Proof. exact (TRANS (@lem5483233) (@lem5483237)). Qed.
Lemma lem5483239 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5483240 : term262 = term222.
Proof. exact (MK_COMB (@lem5483239) (@lem5483238)). Qed.
Lemma lem5483242 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483243 : term222 = term129.
Proof. exact (@lem5483242 term144). Qed.
Lemma lem5483244 : term262 = term129.
Proof. exact (TRANS (@lem5483240) (@lem5483243)). Qed.
Lemma lem5483245 : term129 = term262.
Proof. exact (SYM (@lem5483244)). Qed.
Lemma lem5483246 : term261 = term262.
Proof. exact (TRANS (@lem5483230) (@lem5483245)). Qed.
Lemma lem5483247 : term251 = term161.
Proof. exact (@lem5483197 (@lem5483246)). Qed.
Lemma lem5483248 : term250 = term161.
Proof. exact (TRANS (@lem5483163) (@lem5483247)). Qed.
Lemma lem5483250 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5483251 : term161 = term129.
Proof. exact (@lem5483250 term129). Qed.
Lemma lem5483252 : term250 = term129.
Proof. exact (TRANS (@lem5483248) (@lem5483251)). Qed.
Lemma lem5483253 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483254 : term263 = term260.
Proof. exact (MK_COMB (@lem5483253) (@lem5483252)). Qed.
Lemma lem5483255 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5483256 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5483254) (@lem5483255 _70607)). Qed.
Lemma lem5483257 (_70607 : int) : (term835 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5483154 _70607) (@lem5483256 _70607)). Qed.
Lemma lem5483258 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5483259 (_70607 : int) : (term835 _70607) = term129.
Proof. exact (TRANS (@lem5483257 _70607) (@lem5483258 _70607)). Qed.
Lemma lem5483260 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483261 (_70607 : int) : (term836 _70607) = term266.
Proof. exact (MK_COMB (@lem5483260) (@lem5483259 _70607)). Qed.
Lemma lem5483262 (_70608 : int) : (term837 _70608) = (term546 _70608).
Proof. exact (@lem1982761 (real_of_int _70608) term164). Qed.
Lemma lem5483263 (_70607 : int) (_70608 : int) : (term834 _70607 _70608) = (term838 _70608).
Proof. exact (MK_COMB (@lem5483261 _70607) (@lem5483262 _70608)). Qed.
Lemma lem5483264 (_70607 : int) (_70608 : int) : (term833 _70607 _70608) = (term838 _70608).
Proof. exact (TRANS (@lem5483153 _70607 _70608) (@lem5483263 _70607 _70608)). Qed.
Lemma lem5483265 (_70608 : int) : (term838 _70608) = (term546 _70608).
Proof. exact (@lem1982721 (term546 _70608)). Qed.
Lemma lem5483266 (_70607 : int) (_70608 : int) : (term833 _70607 _70608) = (term546 _70608).
Proof. exact (TRANS (@lem5483264 _70607 _70608) (@lem5483265 _70608)). Qed.
Lemma lem5483267 (_70606 : int) : (term200 _70606) = (term200 _70606).
Proof. exact (eq_refl (term200 _70606)). Qed.
Lemma lem5483268 (_70607 : int) (_70606 : int) (_70608 : int) : (term832 _70606 _70607 _70608) = (term552 _70606 _70608).
Proof. exact (MK_COMB (@lem5483267 _70606) (@lem5483266 _70607 _70608)). Qed.
Lemma lem5483269 (_70607 : int) (_70606 : int) (_70608 : int) : (term831 _70606 _70607 _70608) = (term552 _70606 _70608).
Proof. exact (TRANS (@lem5483152 _70606 _70607 _70608) (@lem5483268 _70607 _70606 _70608)). Qed.
Lemma lem5483270 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5483271 (_70607 : int) (_70606 : int) (_70608 : int) : (term839 _70606 _70607 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5483270) (@lem5483269 _70607 _70606 _70608)). Qed.
Lemma lem5483272 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483273 (_70607 : int) (_70606 : int) (_70608 : int) : (term830 _70606 _70607 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5483271 _70607 _70606 _70608) (@lem5483272)). Qed.
Lemma lem5483274 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5483273 _70607 _70606 _70608) (@lem5483151 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483276 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5483277 : term210 = term211.
Proof. exact (@lem5483276 term129 term143). Qed.
Lemma lem5483279 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483280 : term143 = term191.
Proof. exact (@lem5483279 term144). Qed.
Lemma lem5483282 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483283 : term129 = term161.
Proof. exact (@lem5483282 (NUMERAL 0)). Qed.
Lemma lem5483284 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483285 : term212 = term213.
Proof. exact (MK_COMB (@lem5483284) (@lem5483283)). Qed.
Lemma lem5483286 : term211 = term214.
Proof. exact (MK_COMB (@lem5483285) (@lem5483280)). Qed.
Lemma lem5483287 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5483289 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483290 : term211 = term217.
Proof. exact (@lem5483289 (NUMERAL 0) term144). Qed.
Lemma lem5483291 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483292 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483293 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483292 h1) (fun h1 : term217 = True => @lem5483291)). Qed.
Lemma lem5483294 : term217 = True.
Proof. exact (EQ_MP (@lem5483293) (@lem5483291)). Qed.
Lemma lem5483295 : term211 = True.
Proof. exact (TRANS (@lem5483290) (@lem5483294)). Qed.
Lemma lem5483296 : True = term211.
Proof. exact (SYM (@lem5483295)). Qed.
Lemma lem5483297 : term211.
Proof. exact (EQ_MP (@lem5483296) (@lem0)). Qed.
Lemma lem5483298 : term219.
Proof. exact (@lem5483287 (@lem5483297)). Qed.
Lemma lem5483300 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483301 : term211 = term217.
Proof. exact (@lem5483300 (NUMERAL 0) term144). Qed.
Lemma lem5483302 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483303 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483304 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483303 h1) (fun h1 : term217 = True => @lem5483302)). Qed.
Lemma lem5483305 : term217 = True.
Proof. exact (EQ_MP (@lem5483304) (@lem5483302)). Qed.
Lemma lem5483306 : term211 = True.
Proof. exact (TRANS (@lem5483301) (@lem5483305)). Qed.
Lemma lem5483307 : True = term211.
Proof. exact (SYM (@lem5483306)). Qed.
Lemma lem5483308 : term211.
Proof. exact (EQ_MP (@lem5483307) (@lem0)). Qed.
Lemma lem5483309 : term214 = term220.
Proof. exact (@lem5483298 (@lem5483308)). Qed.
Lemma lem5483311 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483312 : term173 = term174.
Proof. exact (@lem5483311 term144 term144). Qed.
Lemma lem5483313 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483314 : term176 = term144.
Proof. exact (EQ_MP (@lem5483313) (@lem940073)). Qed.
Lemma lem5483315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483316 : term174 = term143.
Proof. exact (MK_COMB (@lem5483315) (@lem5483314)). Qed.
Lemma lem5483317 : term173 = term143.
Proof. exact (TRANS (@lem5483312) (@lem5483316)). Qed.
Lemma lem5483319 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483320 : term222 = term129.
Proof. exact (@lem5483319 term144). Qed.
Lemma lem5483321 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483322 : term223 = term212.
Proof. exact (MK_COMB (@lem5483321) (@lem5483320)). Qed.
Lemma lem5483323 : term220 = term211.
Proof. exact (MK_COMB (@lem5483322) (@lem5483317)). Qed.
Lemma lem5483325 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483326 : term211 = term217.
Proof. exact (@lem5483325 (NUMERAL 0) term144). Qed.
Lemma lem5483327 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483328 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483329 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483328 h1) (fun h1 : term217 = True => @lem5483327)). Qed.
Lemma lem5483330 : term217 = True.
Proof. exact (EQ_MP (@lem5483329) (@lem5483327)). Qed.
Lemma lem5483331 : term211 = True.
Proof. exact (TRANS (@lem5483326) (@lem5483330)). Qed.
Lemma lem5483332 : term220 = True.
Proof. exact (TRANS (@lem5483323) (@lem5483331)). Qed.
Lemma lem5483333 : term214 = True.
Proof. exact (TRANS (@lem5483309) (@lem5483332)). Qed.
Lemma lem5483334 : term211 = True.
Proof. exact (TRANS (@lem5483286) (@lem5483333)). Qed.
Lemma lem5483335 : term210 = True.
Proof. exact (TRANS (@lem5483277) (@lem5483334)). Qed.
Lemma lem5483336 : True = term210.
Proof. exact (SYM (@lem5483335)). Qed.
Lemma lem5483337 : term210.
Proof. exact (EQ_MP (@lem5483336) (@lem0)). Qed.
Lemma lem5483338 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term840 _70606 _70608.
Proof. exact (conj (@lem5483337) (@lem5483274 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483340 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5483341 (_70606 : int) (_70608 : int) : term841 _70606 _70608.
Proof. exact (@lem5483340 term143 (term552 _70606 _70608)). Qed.
Lemma lem5483342 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term842 _70606 _70608.
Proof. exact (@lem5483341 _70606 _70608 (@lem5483338 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483343 (_70606 : int) (_70608 : int) : (term826 _70606 _70608) = (term552 _70606 _70608).
Proof. exact (@lem1982733 (term552 _70606 _70608)). Qed.
Lemma lem5483344 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5483345 (_70606 : int) (_70608 : int) : (term843 _70606 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5483344) (@lem5483343 _70606 _70608)). Qed.
Lemma lem5483346 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483347 (_70606 : int) (_70608 : int) : (term842 _70606 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5483345 _70606 _70608) (@lem5483346)). Qed.
Lemma lem5483348 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5483347 _70606 _70608) (@lem5483342 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483350 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5483351 : term210 = term211.
Proof. exact (@lem5483350 term129 term143). Qed.
Lemma lem5483353 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483354 : term143 = term191.
Proof. exact (@lem5483353 term144). Qed.
Lemma lem5483356 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483357 : term129 = term161.
Proof. exact (@lem5483356 (NUMERAL 0)). Qed.
Lemma lem5483358 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483359 : term212 = term213.
Proof. exact (MK_COMB (@lem5483358) (@lem5483357)). Qed.
Lemma lem5483360 : term211 = term214.
Proof. exact (MK_COMB (@lem5483359) (@lem5483354)). Qed.
Lemma lem5483361 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5483363 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483364 : term211 = term217.
Proof. exact (@lem5483363 (NUMERAL 0) term144). Qed.
Lemma lem5483365 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483366 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483367 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483366 h1) (fun h1 : term217 = True => @lem5483365)). Qed.
Lemma lem5483368 : term217 = True.
Proof. exact (EQ_MP (@lem5483367) (@lem5483365)). Qed.
Lemma lem5483369 : term211 = True.
Proof. exact (TRANS (@lem5483364) (@lem5483368)). Qed.
Lemma lem5483370 : True = term211.
Proof. exact (SYM (@lem5483369)). Qed.
Lemma lem5483371 : term211.
Proof. exact (EQ_MP (@lem5483370) (@lem0)). Qed.
Lemma lem5483372 : term219.
Proof. exact (@lem5483361 (@lem5483371)). Qed.
Lemma lem5483374 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483375 : term211 = term217.
Proof. exact (@lem5483374 (NUMERAL 0) term144). Qed.
Lemma lem5483376 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483377 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483378 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483377 h1) (fun h1 : term217 = True => @lem5483376)). Qed.
Lemma lem5483379 : term217 = True.
Proof. exact (EQ_MP (@lem5483378) (@lem5483376)). Qed.
Lemma lem5483380 : term211 = True.
Proof. exact (TRANS (@lem5483375) (@lem5483379)). Qed.
Lemma lem5483381 : True = term211.
Proof. exact (SYM (@lem5483380)). Qed.
Lemma lem5483382 : term211.
Proof. exact (EQ_MP (@lem5483381) (@lem0)). Qed.
Lemma lem5483383 : term214 = term220.
Proof. exact (@lem5483372 (@lem5483382)). Qed.
Lemma lem5483385 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483386 : term173 = term174.
Proof. exact (@lem5483385 term144 term144). Qed.
Lemma lem5483387 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483388 : term176 = term144.
Proof. exact (EQ_MP (@lem5483387) (@lem940073)). Qed.
Lemma lem5483389 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483390 : term174 = term143.
Proof. exact (MK_COMB (@lem5483389) (@lem5483388)). Qed.
Lemma lem5483391 : term173 = term143.
Proof. exact (TRANS (@lem5483386) (@lem5483390)). Qed.
Lemma lem5483393 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483394 : term222 = term129.
Proof. exact (@lem5483393 term144). Qed.
Lemma lem5483395 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483396 : term223 = term212.
Proof. exact (MK_COMB (@lem5483395) (@lem5483394)). Qed.
Lemma lem5483397 : term220 = term211.
Proof. exact (MK_COMB (@lem5483396) (@lem5483391)). Qed.
Lemma lem5483399 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483400 : term211 = term217.
Proof. exact (@lem5483399 (NUMERAL 0) term144). Qed.
Lemma lem5483401 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483402 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483403 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483402 h1) (fun h1 : term217 = True => @lem5483401)). Qed.
Lemma lem5483404 : term217 = True.
Proof. exact (EQ_MP (@lem5483403) (@lem5483401)). Qed.
Lemma lem5483405 : term211 = True.
Proof. exact (TRANS (@lem5483400) (@lem5483404)). Qed.
Lemma lem5483406 : term220 = True.
Proof. exact (TRANS (@lem5483397) (@lem5483405)). Qed.
Lemma lem5483407 : term214 = True.
Proof. exact (TRANS (@lem5483383) (@lem5483406)). Qed.
Lemma lem5483408 : term211 = True.
Proof. exact (TRANS (@lem5483360) (@lem5483407)). Qed.
Lemma lem5483409 : term210 = True.
Proof. exact (TRANS (@lem5483351) (@lem5483408)). Qed.
Lemma lem5483410 : True = term210.
Proof. exact (SYM (@lem5483409)). Qed.
Lemma lem5483411 : term210.
Proof. exact (EQ_MP (@lem5483410) (@lem0)). Qed.
Lemma lem5483412 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term844 _70606 _70608.
Proof. exact (conj (@lem5483411) (@lem5483058 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483414 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5483415 (_70606 : int) (_70608 : int) : term845 _70606 _70608.
Proof. exact (@lem5483414 term143 (term583 _70606 _70608)). Qed.
Lemma lem5483416 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term846 _70606 _70608.
Proof. exact (@lem5483415 _70606 _70608 (@lem5483412 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483417 (_70606 : int) (_70608 : int) : (term847 _70606 _70608) = (term583 _70606 _70608).
Proof. exact (@lem1982733 (term583 _70606 _70608)). Qed.
Lemma lem5483418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5483419 (_70606 : int) (_70608 : int) : (term848 _70606 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5483418) (@lem5483417 _70606 _70608)). Qed.
Lemma lem5483420 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483421 (_70606 : int) (_70608 : int) : (term846 _70606 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5483419 _70606 _70608) (@lem5483420)). Qed.
Lemma lem5483422 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (EQ_MP (@lem5483421 _70606 _70608) (@lem5483416 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483423 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term849 _70606 _70608.
Proof. exact (conj (@lem5483422 _70607 _70606 _70608 h1) (@lem5483348 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483425 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5483426 (_70606 : int) (_70608 : int) : term850 _70606 _70608.
Proof. exact (@lem5483425 (term583 _70606 _70608) (term552 _70606 _70608)). Qed.
Lemma lem5483427 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term851 _70606 _70608.
Proof. exact (@lem5483426 _70606 _70608 (@lem5483423 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483428 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = (term853 _70606 _70608).
Proof. exact (@lem1982753 (real_of_int _70606) (term239 _70606) (term239 _70608) (term546 _70608)). Qed.
Lemma lem5483429 (_70606 : int) : (term835 _70606) = (term247 _70606).
Proof. exact (@lem1982715 term164 (real_of_int _70606)). Qed.
Lemma lem5483431 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483432 : term143 = term191.
Proof. exact (@lem5483431 term144). Qed.
Lemma lem5483434 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5483435 : term164 = term165.
Proof. exact (@lem5483434 term144). Qed.
Lemma lem5483436 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483437 : term248 = term249.
Proof. exact (MK_COMB (@lem5483436) (@lem5483435)). Qed.
Lemma lem5483438 : term250 = term251.
Proof. exact (MK_COMB (@lem5483437) (@lem5483432)). Qed.
Lemma lem5483439 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5483441 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483442 : term211 = term217.
Proof. exact (@lem5483441 (NUMERAL 0) term144). Qed.
Lemma lem5483443 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483444 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483445 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483444 h1) (fun h1 : term217 = True => @lem5483443)). Qed.
Lemma lem5483446 : term217 = True.
Proof. exact (EQ_MP (@lem5483445) (@lem5483443)). Qed.
Lemma lem5483447 : term211 = True.
Proof. exact (TRANS (@lem5483442) (@lem5483446)). Qed.
Lemma lem5483448 : True = term211.
Proof. exact (SYM (@lem5483447)). Qed.
Lemma lem5483449 : term211.
Proof. exact (EQ_MP (@lem5483448) (@lem0)). Qed.
Lemma lem5483450 : term253.
Proof. exact (@lem5483439 (@lem5483449)). Qed.
Lemma lem5483452 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483453 : term211 = term217.
Proof. exact (@lem5483452 (NUMERAL 0) term144). Qed.
Lemma lem5483454 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483455 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483456 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483455 h1) (fun h1 : term217 = True => @lem5483454)). Qed.
Lemma lem5483457 : term217 = True.
Proof. exact (EQ_MP (@lem5483456) (@lem5483454)). Qed.
Lemma lem5483458 : term211 = True.
Proof. exact (TRANS (@lem5483453) (@lem5483457)). Qed.
Lemma lem5483459 : True = term211.
Proof. exact (SYM (@lem5483458)). Qed.
Lemma lem5483460 : term211.
Proof. exact (EQ_MP (@lem5483459) (@lem0)). Qed.
Lemma lem5483461 : term254.
Proof. exact (@lem5483450 (@lem5483460)). Qed.
Lemma lem5483463 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483464 : term211 = term217.
Proof. exact (@lem5483463 (NUMERAL 0) term144). Qed.
Lemma lem5483465 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483466 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483467 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483466 h1) (fun h1 : term217 = True => @lem5483465)). Qed.
Lemma lem5483468 : term217 = True.
Proof. exact (EQ_MP (@lem5483467) (@lem5483465)). Qed.
Lemma lem5483469 : term211 = True.
Proof. exact (TRANS (@lem5483464) (@lem5483468)). Qed.
Lemma lem5483470 : True = term211.
Proof. exact (SYM (@lem5483469)). Qed.
Lemma lem5483471 : term211.
Proof. exact (EQ_MP (@lem5483470) (@lem0)). Qed.
Lemma lem5483472 : term255.
Proof. exact (@lem5483461 (@lem5483471)). Qed.
Lemma lem5483474 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483475 : term173 = term174.
Proof. exact (@lem5483474 term144 term144). Qed.
Lemma lem5483476 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483477 : term176 = term144.
Proof. exact (EQ_MP (@lem5483476) (@lem940073)). Qed.
Lemma lem5483478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483479 : term174 = term143.
Proof. exact (MK_COMB (@lem5483478) (@lem5483477)). Qed.
Lemma lem5483480 : term173 = term143.
Proof. exact (TRANS (@lem5483475) (@lem5483479)). Qed.
Lemma lem5483482 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5483483 : term192 = term197.
Proof. exact (@lem5483482 term144 term144). Qed.
Lemma lem5483484 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483485 : term176 = term144.
Proof. exact (EQ_MP (@lem5483484) (@lem940073)). Qed.
Lemma lem5483486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483487 : term174 = term143.
Proof. exact (MK_COMB (@lem5483486) (@lem5483485)). Qed.
Lemma lem5483488 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5483489 : term197 = term164.
Proof. exact (MK_COMB (@lem5483488) (@lem5483487)). Qed.
Lemma lem5483490 : term192 = term164.
Proof. exact (TRANS (@lem5483483) (@lem5483489)). Qed.
Lemma lem5483491 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483492 : term256 = term248.
Proof. exact (MK_COMB (@lem5483491) (@lem5483490)). Qed.
Lemma lem5483493 : term257 = term250.
Proof. exact (MK_COMB (@lem5483492) (@lem5483480)). Qed.
Lemma lem5483495 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5483496 : term250 = term129.
Proof. exact (@lem5483495 term144). Qed.
Lemma lem5483497 : term257 = term129.
Proof. exact (TRANS (@lem5483493) (@lem5483496)). Qed.
Lemma lem5483498 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483499 : term259 = term260.
Proof. exact (MK_COMB (@lem5483498) (@lem5483497)). Qed.
Lemma lem5483500 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5483501 : term261 = term222.
Proof. exact (MK_COMB (@lem5483499) (@lem5483500)). Qed.
Lemma lem5483503 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483504 : term222 = term129.
Proof. exact (@lem5483503 term144). Qed.
Lemma lem5483505 : term261 = term129.
Proof. exact (TRANS (@lem5483501) (@lem5483504)). Qed.
Lemma lem5483507 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483508 : term173 = term174.
Proof. exact (@lem5483507 term144 term144). Qed.
Lemma lem5483509 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483510 : term176 = term144.
Proof. exact (EQ_MP (@lem5483509) (@lem940073)). Qed.
Lemma lem5483511 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483512 : term174 = term143.
Proof. exact (MK_COMB (@lem5483511) (@lem5483510)). Qed.
Lemma lem5483513 : term173 = term143.
Proof. exact (TRANS (@lem5483508) (@lem5483512)). Qed.
Lemma lem5483514 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5483515 : term262 = term222.
Proof. exact (MK_COMB (@lem5483514) (@lem5483513)). Qed.
Lemma lem5483517 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483518 : term222 = term129.
Proof. exact (@lem5483517 term144). Qed.
Lemma lem5483519 : term262 = term129.
Proof. exact (TRANS (@lem5483515) (@lem5483518)). Qed.
Lemma lem5483520 : term129 = term262.
Proof. exact (SYM (@lem5483519)). Qed.
Lemma lem5483521 : term261 = term262.
Proof. exact (TRANS (@lem5483505) (@lem5483520)). Qed.
Lemma lem5483522 : term251 = term161.
Proof. exact (@lem5483472 (@lem5483521)). Qed.
Lemma lem5483523 : term250 = term161.
Proof. exact (TRANS (@lem5483438) (@lem5483522)). Qed.
Lemma lem5483525 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5483526 : term161 = term129.
Proof. exact (@lem5483525 term129). Qed.
Lemma lem5483527 : term250 = term129.
Proof. exact (TRANS (@lem5483523) (@lem5483526)). Qed.
Lemma lem5483528 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483529 : term263 = term260.
Proof. exact (MK_COMB (@lem5483528) (@lem5483527)). Qed.
Lemma lem5483530 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5483531 (_70606 : int) : (term247 _70606) = (term264 _70606).
Proof. exact (MK_COMB (@lem5483529) (@lem5483530 _70606)). Qed.
Lemma lem5483532 (_70606 : int) : (term835 _70606) = (term264 _70606).
Proof. exact (TRANS (@lem5483429 _70606) (@lem5483531 _70606)). Qed.
Lemma lem5483533 (_70606 : int) : (term264 _70606) = term129.
Proof. exact (@lem1982719 (real_of_int _70606)). Qed.
Lemma lem5483534 (_70606 : int) : (term835 _70606) = term129.
Proof. exact (TRANS (@lem5483532 _70606) (@lem5483533 _70606)). Qed.
Lemma lem5483535 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483536 (_70606 : int) : (term836 _70606) = term266.
Proof. exact (MK_COMB (@lem5483535) (@lem5483534 _70606)). Qed.
Lemma lem5483537 (_70608 : int) : (term854 _70608) = (term281 _70608).
Proof. exact (@lem1982763 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5483538 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5483540 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483541 : term143 = term191.
Proof. exact (@lem5483540 term144). Qed.
Lemma lem5483543 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5483544 : term164 = term165.
Proof. exact (@lem5483543 term144). Qed.
Lemma lem5483545 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483546 : term248 = term249.
Proof. exact (MK_COMB (@lem5483545) (@lem5483544)). Qed.
Lemma lem5483547 : term250 = term251.
Proof. exact (MK_COMB (@lem5483546) (@lem5483541)). Qed.
Lemma lem5483548 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5483550 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483551 : term211 = term217.
Proof. exact (@lem5483550 (NUMERAL 0) term144). Qed.
Lemma lem5483552 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483553 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483554 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483553 h1) (fun h1 : term217 = True => @lem5483552)). Qed.
Lemma lem5483555 : term217 = True.
Proof. exact (EQ_MP (@lem5483554) (@lem5483552)). Qed.
Lemma lem5483556 : term211 = True.
Proof. exact (TRANS (@lem5483551) (@lem5483555)). Qed.
Lemma lem5483557 : True = term211.
Proof. exact (SYM (@lem5483556)). Qed.
Lemma lem5483558 : term211.
Proof. exact (EQ_MP (@lem5483557) (@lem0)). Qed.
Lemma lem5483559 : term253.
Proof. exact (@lem5483548 (@lem5483558)). Qed.
Lemma lem5483561 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483562 : term211 = term217.
Proof. exact (@lem5483561 (NUMERAL 0) term144). Qed.
Lemma lem5483563 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483564 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483565 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483564 h1) (fun h1 : term217 = True => @lem5483563)). Qed.
Lemma lem5483566 : term217 = True.
Proof. exact (EQ_MP (@lem5483565) (@lem5483563)). Qed.
Lemma lem5483567 : term211 = True.
Proof. exact (TRANS (@lem5483562) (@lem5483566)). Qed.
Lemma lem5483568 : True = term211.
Proof. exact (SYM (@lem5483567)). Qed.
Lemma lem5483569 : term211.
Proof. exact (EQ_MP (@lem5483568) (@lem0)). Qed.
Lemma lem5483570 : term254.
Proof. exact (@lem5483559 (@lem5483569)). Qed.
Lemma lem5483572 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483573 : term211 = term217.
Proof. exact (@lem5483572 (NUMERAL 0) term144). Qed.
Lemma lem5483574 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483575 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483576 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483575 h1) (fun h1 : term217 = True => @lem5483574)). Qed.
Lemma lem5483577 : term217 = True.
Proof. exact (EQ_MP (@lem5483576) (@lem5483574)). Qed.
Lemma lem5483578 : term211 = True.
Proof. exact (TRANS (@lem5483573) (@lem5483577)). Qed.
Lemma lem5483579 : True = term211.
Proof. exact (SYM (@lem5483578)). Qed.
Lemma lem5483580 : term211.
Proof. exact (EQ_MP (@lem5483579) (@lem0)). Qed.
Lemma lem5483581 : term255.
Proof. exact (@lem5483570 (@lem5483580)). Qed.
Lemma lem5483583 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483584 : term173 = term174.
Proof. exact (@lem5483583 term144 term144). Qed.
Lemma lem5483585 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483586 : term176 = term144.
Proof. exact (EQ_MP (@lem5483585) (@lem940073)). Qed.
Lemma lem5483587 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483588 : term174 = term143.
Proof. exact (MK_COMB (@lem5483587) (@lem5483586)). Qed.
Lemma lem5483589 : term173 = term143.
Proof. exact (TRANS (@lem5483584) (@lem5483588)). Qed.
Lemma lem5483591 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5483592 : term192 = term197.
Proof. exact (@lem5483591 term144 term144). Qed.
Lemma lem5483593 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483594 : term176 = term144.
Proof. exact (EQ_MP (@lem5483593) (@lem940073)). Qed.
Lemma lem5483595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483596 : term174 = term143.
Proof. exact (MK_COMB (@lem5483595) (@lem5483594)). Qed.
Lemma lem5483597 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5483598 : term197 = term164.
Proof. exact (MK_COMB (@lem5483597) (@lem5483596)). Qed.
Lemma lem5483599 : term192 = term164.
Proof. exact (TRANS (@lem5483592) (@lem5483598)). Qed.
Lemma lem5483600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483601 : term256 = term248.
Proof. exact (MK_COMB (@lem5483600) (@lem5483599)). Qed.
Lemma lem5483602 : term257 = term250.
Proof. exact (MK_COMB (@lem5483601) (@lem5483589)). Qed.
Lemma lem5483604 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5483605 : term250 = term129.
Proof. exact (@lem5483604 term144). Qed.
Lemma lem5483606 : term257 = term129.
Proof. exact (TRANS (@lem5483602) (@lem5483605)). Qed.
Lemma lem5483607 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483608 : term259 = term260.
Proof. exact (MK_COMB (@lem5483607) (@lem5483606)). Qed.
Lemma lem5483609 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5483610 : term261 = term222.
Proof. exact (MK_COMB (@lem5483608) (@lem5483609)). Qed.
Lemma lem5483612 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483613 : term222 = term129.
Proof. exact (@lem5483612 term144). Qed.
Lemma lem5483614 : term261 = term129.
Proof. exact (TRANS (@lem5483610) (@lem5483613)). Qed.
Lemma lem5483616 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483617 : term173 = term174.
Proof. exact (@lem5483616 term144 term144). Qed.
Lemma lem5483618 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483619 : term176 = term144.
Proof. exact (EQ_MP (@lem5483618) (@lem940073)). Qed.
Lemma lem5483620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483621 : term174 = term143.
Proof. exact (MK_COMB (@lem5483620) (@lem5483619)). Qed.
Lemma lem5483622 : term173 = term143.
Proof. exact (TRANS (@lem5483617) (@lem5483621)). Qed.
Lemma lem5483623 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5483624 : term262 = term222.
Proof. exact (MK_COMB (@lem5483623) (@lem5483622)). Qed.
Lemma lem5483626 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483627 : term222 = term129.
Proof. exact (@lem5483626 term144). Qed.
Lemma lem5483628 : term262 = term129.
Proof. exact (TRANS (@lem5483624) (@lem5483627)). Qed.
Lemma lem5483629 : term129 = term262.
Proof. exact (SYM (@lem5483628)). Qed.
Lemma lem5483630 : term261 = term262.
Proof. exact (TRANS (@lem5483614) (@lem5483629)). Qed.
Lemma lem5483631 : term251 = term161.
Proof. exact (@lem5483581 (@lem5483630)). Qed.
Lemma lem5483632 : term250 = term161.
Proof. exact (TRANS (@lem5483547) (@lem5483631)). Qed.
Lemma lem5483634 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5483635 : term161 = term129.
Proof. exact (@lem5483634 term129). Qed.
Lemma lem5483636 : term250 = term129.
Proof. exact (TRANS (@lem5483632) (@lem5483635)). Qed.
Lemma lem5483637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483638 : term263 = term260.
Proof. exact (MK_COMB (@lem5483637) (@lem5483636)). Qed.
Lemma lem5483639 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5483640 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5483638) (@lem5483639 _70608)). Qed.
Lemma lem5483641 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5483538 _70608) (@lem5483640 _70608)). Qed.
Lemma lem5483642 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5483643 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5483641 _70608) (@lem5483642 _70608)). Qed.
Lemma lem5483644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483645 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5483644) (@lem5483643 _70608)). Qed.
Lemma lem5483646 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5483647 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5483645 _70608) (@lem5483646)). Qed.
Lemma lem5483648 (_70608 : int) : (term854 _70608) = term282.
Proof. exact (TRANS (@lem5483537 _70608) (@lem5483647 _70608)). Qed.
Lemma lem5483649 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5483650 (_70608 : int) : (term854 _70608) = term164.
Proof. exact (TRANS (@lem5483648 _70608) (@lem5483649)). Qed.
Lemma lem5483651 (_70606 : int) (_70608 : int) : (term853 _70606 _70608) = term282.
Proof. exact (MK_COMB (@lem5483536 _70606) (@lem5483650 _70608)). Qed.
Lemma lem5483652 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term282.
Proof. exact (TRANS (@lem5483428 _70606 _70608) (@lem5483651 _70606 _70608)). Qed.
Lemma lem5483653 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5483654 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term164.
Proof. exact (TRANS (@lem5483652 _70606 _70608) (@lem5483653)). Qed.
Lemma lem5483655 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5483656 (_70606 : int) (_70608 : int) : (term855 _70606 _70608) = term284.
Proof. exact (MK_COMB (@lem5483655) (@lem5483654 _70606 _70608)). Qed.
Lemma lem5483657 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483658 (_70606 : int) (_70608 : int) : (term851 _70606 _70608) = term285.
Proof. exact (MK_COMB (@lem5483656 _70606 _70608) (@lem5483657)). Qed.
Lemma lem5483659 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : term285.
Proof. exact (EQ_MP (@lem5483658 _70606 _70608) (@lem5483427 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483661 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5483662 : term285 = term286.
Proof. exact (@lem5483661 term129 term164). Qed.
Lemma lem5483664 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5483665 : term164 = term165.
Proof. exact (@lem5483664 term144). Qed.
Lemma lem5483667 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483668 : term129 = term161.
Proof. exact (@lem5483667 (NUMERAL 0)). Qed.
Lemma lem5483669 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5483670 : term131 = term287.
Proof. exact (MK_COMB (@lem5483669) (@lem5483668)). Qed.
Lemma lem5483671 : term286 = term288.
Proof. exact (MK_COMB (@lem5483670) (@lem5483665)). Qed.
Lemma lem5483672 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5483674 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483675 : term211 = term217.
Proof. exact (@lem5483674 (NUMERAL 0) term144). Qed.
Lemma lem5483676 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483677 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483678 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483677 h1) (fun h1 : term217 = True => @lem5483676)). Qed.
Lemma lem5483679 : term217 = True.
Proof. exact (EQ_MP (@lem5483678) (@lem5483676)). Qed.
Lemma lem5483680 : term211 = True.
Proof. exact (TRANS (@lem5483675) (@lem5483679)). Qed.
Lemma lem5483681 : True = term211.
Proof. exact (SYM (@lem5483680)). Qed.
Lemma lem5483682 : term211.
Proof. exact (EQ_MP (@lem5483681) (@lem0)). Qed.
Lemma lem5483683 : term290.
Proof. exact (@lem5483672 (@lem5483682)). Qed.
Lemma lem5483685 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483686 : term211 = term217.
Proof. exact (@lem5483685 (NUMERAL 0) term144). Qed.
Lemma lem5483687 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483688 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483689 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483688 h1) (fun h1 : term217 = True => @lem5483687)). Qed.
Lemma lem5483690 : term217 = True.
Proof. exact (EQ_MP (@lem5483689) (@lem5483687)). Qed.
Lemma lem5483691 : term211 = True.
Proof. exact (TRANS (@lem5483686) (@lem5483690)). Qed.
Lemma lem5483692 : True = term211.
Proof. exact (SYM (@lem5483691)). Qed.
Lemma lem5483693 : term211.
Proof. exact (EQ_MP (@lem5483692) (@lem0)). Qed.
Lemma lem5483694 : term288 = term291.
Proof. exact (@lem5483683 (@lem5483693)). Qed.
Lemma lem5483696 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5483697 : term192 = term197.
Proof. exact (@lem5483696 term144 term144). Qed.
Lemma lem5483698 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483699 : term176 = term144.
Proof. exact (EQ_MP (@lem5483698) (@lem940073)). Qed.
Lemma lem5483700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483701 : term174 = term143.
Proof. exact (MK_COMB (@lem5483700) (@lem5483699)). Qed.
Lemma lem5483702 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5483703 : term197 = term164.
Proof. exact (MK_COMB (@lem5483702) (@lem5483701)). Qed.
Lemma lem5483704 : term192 = term164.
Proof. exact (TRANS (@lem5483697) (@lem5483703)). Qed.
Lemma lem5483706 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483707 : term222 = term129.
Proof. exact (@lem5483706 term144). Qed.
Lemma lem5483708 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5483709 : term292 = term131.
Proof. exact (MK_COMB (@lem5483708) (@lem5483707)). Qed.
Lemma lem5483710 : term291 = term286.
Proof. exact (MK_COMB (@lem5483709) (@lem5483704)). Qed.
Lemma lem5483712 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5483713 : term286 = term295.
Proof. exact (@lem5483712 (NUMERAL 0) term144). Qed.
Lemma lem5483714 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483715 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5483716 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483715 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5483714)). Qed.
Lemma lem5483717 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5483716) (@lem5483714)). Qed.
Lemma lem5483718 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5483719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5483720 : term296 = (and True).
Proof. exact (MK_COMB (@lem5483719) (@lem5483718)). Qed.
Lemma lem5483721 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5483720) (@lem5483717)). Qed.
Lemma lem5483723 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5483724 : term295 = False.
Proof. exact (TRANS (@lem5483721) (@lem5483723)). Qed.
Lemma lem5483725 : term286 = False.
Proof. exact (TRANS (@lem5483713) (@lem5483724)). Qed.
Lemma lem5483726 : term291 = False.
Proof. exact (TRANS (@lem5483710) (@lem5483725)). Qed.
Lemma lem5483727 : term288 = False.
Proof. exact (TRANS (@lem5483694) (@lem5483726)). Qed.
Lemma lem5483728 : term286 = False.
Proof. exact (TRANS (@lem5483671) (@lem5483727)). Qed.
Lemma lem5483729 : term285 = False.
Proof. exact (TRANS (@lem5483662) (@lem5483728)). Qed.
Lemma lem5483730 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term817 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5483729) (@lem5483659 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483731 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term856 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5483732 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term810 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483731 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483734 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term761 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483732 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483736 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term712 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483734 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483738 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term658 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483736 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483740 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term592 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5483738 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483741 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : (term552 _70606 _70607) = term129.
Proof. exact (proj1 (@lem5483738 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483742 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term590 _70606 _70608.
Proof. exact (proj2 (@lem5483740 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483743 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term587 _70607 _70608.
Proof. exact (proj1 (@lem5483740 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483744 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (proj2 (@lem5483742 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483747 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5483748 : term210 = term211.
Proof. exact (@lem5483747 term129 term143). Qed.
Lemma lem5483750 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483751 : term143 = term191.
Proof. exact (@lem5483750 term144). Qed.
Lemma lem5483753 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483754 : term129 = term161.
Proof. exact (@lem5483753 (NUMERAL 0)). Qed.
Lemma lem5483755 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483756 : term212 = term213.
Proof. exact (MK_COMB (@lem5483755) (@lem5483754)). Qed.
Lemma lem5483757 : term211 = term214.
Proof. exact (MK_COMB (@lem5483756) (@lem5483751)). Qed.
Lemma lem5483758 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5483760 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483761 : term211 = term217.
Proof. exact (@lem5483760 (NUMERAL 0) term144). Qed.
Lemma lem5483762 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483763 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483764 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483763 h1) (fun h1 : term217 = True => @lem5483762)). Qed.
Lemma lem5483765 : term217 = True.
Proof. exact (EQ_MP (@lem5483764) (@lem5483762)). Qed.
Lemma lem5483766 : term211 = True.
Proof. exact (TRANS (@lem5483761) (@lem5483765)). Qed.
Lemma lem5483767 : True = term211.
Proof. exact (SYM (@lem5483766)). Qed.
Lemma lem5483768 : term211.
Proof. exact (EQ_MP (@lem5483767) (@lem0)). Qed.
Lemma lem5483769 : term219.
Proof. exact (@lem5483758 (@lem5483768)). Qed.
Lemma lem5483771 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483772 : term211 = term217.
Proof. exact (@lem5483771 (NUMERAL 0) term144). Qed.
Lemma lem5483773 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483774 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483775 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483774 h1) (fun h1 : term217 = True => @lem5483773)). Qed.
Lemma lem5483776 : term217 = True.
Proof. exact (EQ_MP (@lem5483775) (@lem5483773)). Qed.
Lemma lem5483777 : term211 = True.
Proof. exact (TRANS (@lem5483772) (@lem5483776)). Qed.
Lemma lem5483778 : True = term211.
Proof. exact (SYM (@lem5483777)). Qed.
Lemma lem5483779 : term211.
Proof. exact (EQ_MP (@lem5483778) (@lem0)). Qed.
Lemma lem5483780 : term214 = term220.
Proof. exact (@lem5483769 (@lem5483779)). Qed.
Lemma lem5483782 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483783 : term173 = term174.
Proof. exact (@lem5483782 term144 term144). Qed.
Lemma lem5483784 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483785 : term176 = term144.
Proof. exact (EQ_MP (@lem5483784) (@lem940073)). Qed.
Lemma lem5483786 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483787 : term174 = term143.
Proof. exact (MK_COMB (@lem5483786) (@lem5483785)). Qed.
Lemma lem5483788 : term173 = term143.
Proof. exact (TRANS (@lem5483783) (@lem5483787)). Qed.
Lemma lem5483790 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483791 : term222 = term129.
Proof. exact (@lem5483790 term144). Qed.
Lemma lem5483792 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483793 : term223 = term212.
Proof. exact (MK_COMB (@lem5483792) (@lem5483791)). Qed.
Lemma lem5483794 : term220 = term211.
Proof. exact (MK_COMB (@lem5483793) (@lem5483788)). Qed.
Lemma lem5483796 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483797 : term211 = term217.
Proof. exact (@lem5483796 (NUMERAL 0) term144). Qed.
Lemma lem5483798 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483799 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483800 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483799 h1) (fun h1 : term217 = True => @lem5483798)). Qed.
Lemma lem5483801 : term217 = True.
Proof. exact (EQ_MP (@lem5483800) (@lem5483798)). Qed.
Lemma lem5483802 : term211 = True.
Proof. exact (TRANS (@lem5483797) (@lem5483801)). Qed.
Lemma lem5483803 : term220 = True.
Proof. exact (TRANS (@lem5483794) (@lem5483802)). Qed.
Lemma lem5483804 : term214 = True.
Proof. exact (TRANS (@lem5483780) (@lem5483803)). Qed.
Lemma lem5483805 : term211 = True.
Proof. exact (TRANS (@lem5483757) (@lem5483804)). Qed.
Lemma lem5483806 : term210 = True.
Proof. exact (TRANS (@lem5483748) (@lem5483805)). Qed.
Lemma lem5483807 : True = term210.
Proof. exact (SYM (@lem5483806)). Qed.
Lemma lem5483808 : term210.
Proof. exact (EQ_MP (@lem5483807) (@lem0)). Qed.
Lemma lem5483809 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term818 _70607 _70608.
Proof. exact (conj (@lem5483808) (@lem5483743 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483811 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5483812 (_70607 : int) (_70608 : int) : term819 _70607 _70608.
Proof. exact (@lem5483811 term143 (term584 _70607 _70608)). Qed.
Lemma lem5483813 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term820 _70607 _70608.
Proof. exact (@lem5483812 _70607 _70608 (@lem5483809 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483814 (_70607 : int) (_70608 : int) : (term821 _70607 _70608) = (term584 _70607 _70608).
Proof. exact (@lem1982733 (term584 _70607 _70608)). Qed.
Lemma lem5483815 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5483816 (_70607 : int) (_70608 : int) : (term822 _70607 _70608) = (term586 _70607 _70608).
Proof. exact (MK_COMB (@lem5483815) (@lem5483814 _70607 _70608)). Qed.
Lemma lem5483817 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483818 (_70607 : int) (_70608 : int) : (term820 _70607 _70608) = (term587 _70607 _70608).
Proof. exact (MK_COMB (@lem5483816 _70607 _70608) (@lem5483817)). Qed.
Lemma lem5483819 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term587 _70607 _70608.
Proof. exact (EQ_MP (@lem5483818 _70607 _70608) (@lem5483813 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483821 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5483822 (_70606 : int) (_70607 : int) : term823 _70606 _70607.
Proof. exact (@lem5483821 (term552 _70606 _70607)). Qed.
Lemma lem5483823 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term824 _70606 _70607.
Proof. exact (@lem5483822 _70606 _70607 (@lem5483741 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483824 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term825 _70606 _70607.
Proof. exact (@lem5483823 _70607 _70606 _70608 h1 term143). Qed.
Lemma lem5483825 (_70606 : int) (_70607 : int) : (term825 _70606 _70607) = ((term826 _70606 _70607) = term129).
Proof. exact (eq_refl (term825 _70606 _70607)). Qed.
Lemma lem5483826 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : (term826 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5483825 _70606 _70607) (@lem5483824 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483827 (_70606 : int) (_70607 : int) : (term826 _70606 _70607) = (term552 _70606 _70607).
Proof. exact (@lem1982733 (term552 _70606 _70607)). Qed.
Lemma lem5483828 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5483829 (_70606 : int) (_70607 : int) : (term827 _70606 _70607) = (term554 _70606 _70607).
Proof. exact (MK_COMB (@lem5483828) (@lem5483827 _70606 _70607)). Qed.
Lemma lem5483830 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483831 (_70606 : int) (_70607 : int) : ((term826 _70606 _70607) = term129) = ((term552 _70606 _70607) = term129).
Proof. exact (MK_COMB (@lem5483829 _70606 _70607) (@lem5483830)). Qed.
Lemma lem5483832 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : (term552 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5483831 _70606 _70607) (@lem5483826 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483833 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term828 _70606 _70607 _70608.
Proof. exact (conj (@lem5483832 _70607 _70606 _70608 h1) (@lem5483819 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483835 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5483836 (_70606 : int) (_70607 : int) (_70608 : int) : term829 _70606 _70607 _70608.
Proof. exact (@lem5483835 (term552 _70606 _70607) (term584 _70607 _70608)). Qed.
Lemma lem5483837 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term830 _70606 _70607 _70608.
Proof. exact (@lem5483836 _70606 _70607 _70608 (@lem5483833 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483838 (_70606 : int) (_70607 : int) (_70608 : int) : (term831 _70606 _70607 _70608) = (term832 _70606 _70607 _70608).
Proof. exact (@lem1982755 (term239 _70606) (term546 _70607) (term584 _70607 _70608)). Qed.
Lemma lem5483839 (_70607 : int) (_70608 : int) : (term833 _70607 _70608) = (term834 _70607 _70608).
Proof. exact (@lem1982753 (real_of_int _70607) (term239 _70607) term164 (real_of_int _70608)). Qed.
Lemma lem5483840 (_70607 : int) : (term835 _70607) = (term247 _70607).
Proof. exact (@lem1982715 term164 (real_of_int _70607)). Qed.
Lemma lem5483842 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483843 : term143 = term191.
Proof. exact (@lem5483842 term144). Qed.
Lemma lem5483845 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5483846 : term164 = term165.
Proof. exact (@lem5483845 term144). Qed.
Lemma lem5483847 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483848 : term248 = term249.
Proof. exact (MK_COMB (@lem5483847) (@lem5483846)). Qed.
Lemma lem5483849 : term250 = term251.
Proof. exact (MK_COMB (@lem5483848) (@lem5483843)). Qed.
Lemma lem5483850 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5483852 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483853 : term211 = term217.
Proof. exact (@lem5483852 (NUMERAL 0) term144). Qed.
Lemma lem5483854 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483855 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483856 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483855 h1) (fun h1 : term217 = True => @lem5483854)). Qed.
Lemma lem5483857 : term217 = True.
Proof. exact (EQ_MP (@lem5483856) (@lem5483854)). Qed.
Lemma lem5483858 : term211 = True.
Proof. exact (TRANS (@lem5483853) (@lem5483857)). Qed.
Lemma lem5483859 : True = term211.
Proof. exact (SYM (@lem5483858)). Qed.
Lemma lem5483860 : term211.
Proof. exact (EQ_MP (@lem5483859) (@lem0)). Qed.
Lemma lem5483861 : term253.
Proof. exact (@lem5483850 (@lem5483860)). Qed.
Lemma lem5483863 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483864 : term211 = term217.
Proof. exact (@lem5483863 (NUMERAL 0) term144). Qed.
Lemma lem5483865 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483866 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483867 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483866 h1) (fun h1 : term217 = True => @lem5483865)). Qed.
Lemma lem5483868 : term217 = True.
Proof. exact (EQ_MP (@lem5483867) (@lem5483865)). Qed.
Lemma lem5483869 : term211 = True.
Proof. exact (TRANS (@lem5483864) (@lem5483868)). Qed.
Lemma lem5483870 : True = term211.
Proof. exact (SYM (@lem5483869)). Qed.
Lemma lem5483871 : term211.
Proof. exact (EQ_MP (@lem5483870) (@lem0)). Qed.
Lemma lem5483872 : term254.
Proof. exact (@lem5483861 (@lem5483871)). Qed.
Lemma lem5483874 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483875 : term211 = term217.
Proof. exact (@lem5483874 (NUMERAL 0) term144). Qed.
Lemma lem5483876 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483877 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483878 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483877 h1) (fun h1 : term217 = True => @lem5483876)). Qed.
Lemma lem5483879 : term217 = True.
Proof. exact (EQ_MP (@lem5483878) (@lem5483876)). Qed.
Lemma lem5483880 : term211 = True.
Proof. exact (TRANS (@lem5483875) (@lem5483879)). Qed.
Lemma lem5483881 : True = term211.
Proof. exact (SYM (@lem5483880)). Qed.
Lemma lem5483882 : term211.
Proof. exact (EQ_MP (@lem5483881) (@lem0)). Qed.
Lemma lem5483883 : term255.
Proof. exact (@lem5483872 (@lem5483882)). Qed.
Lemma lem5483885 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483886 : term173 = term174.
Proof. exact (@lem5483885 term144 term144). Qed.
Lemma lem5483887 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483888 : term176 = term144.
Proof. exact (EQ_MP (@lem5483887) (@lem940073)). Qed.
Lemma lem5483889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483890 : term174 = term143.
Proof. exact (MK_COMB (@lem5483889) (@lem5483888)). Qed.
Lemma lem5483891 : term173 = term143.
Proof. exact (TRANS (@lem5483886) (@lem5483890)). Qed.
Lemma lem5483893 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5483894 : term192 = term197.
Proof. exact (@lem5483893 term144 term144). Qed.
Lemma lem5483895 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483896 : term176 = term144.
Proof. exact (EQ_MP (@lem5483895) (@lem940073)). Qed.
Lemma lem5483897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483898 : term174 = term143.
Proof. exact (MK_COMB (@lem5483897) (@lem5483896)). Qed.
Lemma lem5483899 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5483900 : term197 = term164.
Proof. exact (MK_COMB (@lem5483899) (@lem5483898)). Qed.
Lemma lem5483901 : term192 = term164.
Proof. exact (TRANS (@lem5483894) (@lem5483900)). Qed.
Lemma lem5483902 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483903 : term256 = term248.
Proof. exact (MK_COMB (@lem5483902) (@lem5483901)). Qed.
Lemma lem5483904 : term257 = term250.
Proof. exact (MK_COMB (@lem5483903) (@lem5483891)). Qed.
Lemma lem5483906 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5483907 : term250 = term129.
Proof. exact (@lem5483906 term144). Qed.
Lemma lem5483908 : term257 = term129.
Proof. exact (TRANS (@lem5483904) (@lem5483907)). Qed.
Lemma lem5483909 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483910 : term259 = term260.
Proof. exact (MK_COMB (@lem5483909) (@lem5483908)). Qed.
Lemma lem5483911 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5483912 : term261 = term222.
Proof. exact (MK_COMB (@lem5483910) (@lem5483911)). Qed.
Lemma lem5483914 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483915 : term222 = term129.
Proof. exact (@lem5483914 term144). Qed.
Lemma lem5483916 : term261 = term129.
Proof. exact (TRANS (@lem5483912) (@lem5483915)). Qed.
Lemma lem5483918 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483919 : term173 = term174.
Proof. exact (@lem5483918 term144 term144). Qed.
Lemma lem5483920 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5483921 : term176 = term144.
Proof. exact (EQ_MP (@lem5483920) (@lem940073)). Qed.
Lemma lem5483922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5483923 : term174 = term143.
Proof. exact (MK_COMB (@lem5483922) (@lem5483921)). Qed.
Lemma lem5483924 : term173 = term143.
Proof. exact (TRANS (@lem5483919) (@lem5483923)). Qed.
Lemma lem5483925 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5483926 : term262 = term222.
Proof. exact (MK_COMB (@lem5483925) (@lem5483924)). Qed.
Lemma lem5483928 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5483929 : term222 = term129.
Proof. exact (@lem5483928 term144). Qed.
Lemma lem5483930 : term262 = term129.
Proof. exact (TRANS (@lem5483926) (@lem5483929)). Qed.
Lemma lem5483931 : term129 = term262.
Proof. exact (SYM (@lem5483930)). Qed.
Lemma lem5483932 : term261 = term262.
Proof. exact (TRANS (@lem5483916) (@lem5483931)). Qed.
Lemma lem5483933 : term251 = term161.
Proof. exact (@lem5483883 (@lem5483932)). Qed.
Lemma lem5483934 : term250 = term161.
Proof. exact (TRANS (@lem5483849) (@lem5483933)). Qed.
Lemma lem5483936 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5483937 : term161 = term129.
Proof. exact (@lem5483936 term129). Qed.
Lemma lem5483938 : term250 = term129.
Proof. exact (TRANS (@lem5483934) (@lem5483937)). Qed.
Lemma lem5483939 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5483940 : term263 = term260.
Proof. exact (MK_COMB (@lem5483939) (@lem5483938)). Qed.
Lemma lem5483941 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5483942 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5483940) (@lem5483941 _70607)). Qed.
Lemma lem5483943 (_70607 : int) : (term835 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5483840 _70607) (@lem5483942 _70607)). Qed.
Lemma lem5483944 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5483945 (_70607 : int) : (term835 _70607) = term129.
Proof. exact (TRANS (@lem5483943 _70607) (@lem5483944 _70607)). Qed.
Lemma lem5483946 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5483947 (_70607 : int) : (term836 _70607) = term266.
Proof. exact (MK_COMB (@lem5483946) (@lem5483945 _70607)). Qed.
Lemma lem5483948 (_70608 : int) : (term837 _70608) = (term546 _70608).
Proof. exact (@lem1982761 (real_of_int _70608) term164). Qed.
Lemma lem5483949 (_70607 : int) (_70608 : int) : (term834 _70607 _70608) = (term838 _70608).
Proof. exact (MK_COMB (@lem5483947 _70607) (@lem5483948 _70608)). Qed.
Lemma lem5483950 (_70607 : int) (_70608 : int) : (term833 _70607 _70608) = (term838 _70608).
Proof. exact (TRANS (@lem5483839 _70607 _70608) (@lem5483949 _70607 _70608)). Qed.
Lemma lem5483951 (_70608 : int) : (term838 _70608) = (term546 _70608).
Proof. exact (@lem1982721 (term546 _70608)). Qed.
Lemma lem5483952 (_70607 : int) (_70608 : int) : (term833 _70607 _70608) = (term546 _70608).
Proof. exact (TRANS (@lem5483950 _70607 _70608) (@lem5483951 _70608)). Qed.
Lemma lem5483953 (_70606 : int) : (term200 _70606) = (term200 _70606).
Proof. exact (eq_refl (term200 _70606)). Qed.
Lemma lem5483954 (_70607 : int) (_70606 : int) (_70608 : int) : (term832 _70606 _70607 _70608) = (term552 _70606 _70608).
Proof. exact (MK_COMB (@lem5483953 _70606) (@lem5483952 _70607 _70608)). Qed.
Lemma lem5483955 (_70607 : int) (_70606 : int) (_70608 : int) : (term831 _70606 _70607 _70608) = (term552 _70606 _70608).
Proof. exact (TRANS (@lem5483838 _70606 _70607 _70608) (@lem5483954 _70607 _70606 _70608)). Qed.
Lemma lem5483956 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5483957 (_70607 : int) (_70606 : int) (_70608 : int) : (term839 _70606 _70607 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5483956) (@lem5483955 _70607 _70606 _70608)). Qed.
Lemma lem5483958 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5483959 (_70607 : int) (_70606 : int) (_70608 : int) : (term830 _70606 _70607 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5483957 _70607 _70606 _70608) (@lem5483958)). Qed.
Lemma lem5483960 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5483959 _70607 _70606 _70608) (@lem5483837 _70607 _70606 _70608 h1)). Qed.
Lemma lem5483962 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5483963 : term210 = term211.
Proof. exact (@lem5483962 term129 term143). Qed.
Lemma lem5483965 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483966 : term143 = term191.
Proof. exact (@lem5483965 term144). Qed.
Lemma lem5483968 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5483969 : term129 = term161.
Proof. exact (@lem5483968 (NUMERAL 0)). Qed.
Lemma lem5483970 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5483971 : term212 = term213.
Proof. exact (MK_COMB (@lem5483970) (@lem5483969)). Qed.
Lemma lem5483972 : term211 = term214.
Proof. exact (MK_COMB (@lem5483971) (@lem5483966)). Qed.
Lemma lem5483973 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5483975 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483976 : term211 = term217.
Proof. exact (@lem5483975 (NUMERAL 0) term144). Qed.
Lemma lem5483977 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483978 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483979 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483978 h1) (fun h1 : term217 = True => @lem5483977)). Qed.
Lemma lem5483980 : term217 = True.
Proof. exact (EQ_MP (@lem5483979) (@lem5483977)). Qed.
Lemma lem5483981 : term211 = True.
Proof. exact (TRANS (@lem5483976) (@lem5483980)). Qed.
Lemma lem5483982 : True = term211.
Proof. exact (SYM (@lem5483981)). Qed.
Lemma lem5483983 : term211.
Proof. exact (EQ_MP (@lem5483982) (@lem0)). Qed.
Lemma lem5483984 : term219.
Proof. exact (@lem5483973 (@lem5483983)). Qed.
Lemma lem5483986 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5483987 : term211 = term217.
Proof. exact (@lem5483986 (NUMERAL 0) term144). Qed.
Lemma lem5483988 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5483989 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5483990 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5483989 h1) (fun h1 : term217 = True => @lem5483988)). Qed.
Lemma lem5483991 : term217 = True.
Proof. exact (EQ_MP (@lem5483990) (@lem5483988)). Qed.
Lemma lem5483992 : term211 = True.
Proof. exact (TRANS (@lem5483987) (@lem5483991)). Qed.
Lemma lem5483993 : True = term211.
Proof. exact (SYM (@lem5483992)). Qed.
Lemma lem5483994 : term211.
Proof. exact (EQ_MP (@lem5483993) (@lem0)). Qed.
Lemma lem5483995 : term214 = term220.
Proof. exact (@lem5483984 (@lem5483994)). Qed.
Lemma lem5483997 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5483998 : term173 = term174.
Proof. exact (@lem5483997 term144 term144). Qed.
Lemma lem5483999 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484000 : term176 = term144.
Proof. exact (EQ_MP (@lem5483999) (@lem940073)). Qed.
Lemma lem5484001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484002 : term174 = term143.
Proof. exact (MK_COMB (@lem5484001) (@lem5484000)). Qed.
Lemma lem5484003 : term173 = term143.
Proof. exact (TRANS (@lem5483998) (@lem5484002)). Qed.
Lemma lem5484005 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484006 : term222 = term129.
Proof. exact (@lem5484005 term144). Qed.
Lemma lem5484007 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484008 : term223 = term212.
Proof. exact (MK_COMB (@lem5484007) (@lem5484006)). Qed.
Lemma lem5484009 : term220 = term211.
Proof. exact (MK_COMB (@lem5484008) (@lem5484003)). Qed.
Lemma lem5484011 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484012 : term211 = term217.
Proof. exact (@lem5484011 (NUMERAL 0) term144). Qed.
Lemma lem5484013 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484014 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484015 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484014 h1) (fun h1 : term217 = True => @lem5484013)). Qed.
Lemma lem5484016 : term217 = True.
Proof. exact (EQ_MP (@lem5484015) (@lem5484013)). Qed.
Lemma lem5484017 : term211 = True.
Proof. exact (TRANS (@lem5484012) (@lem5484016)). Qed.
Lemma lem5484018 : term220 = True.
Proof. exact (TRANS (@lem5484009) (@lem5484017)). Qed.
Lemma lem5484019 : term214 = True.
Proof. exact (TRANS (@lem5483995) (@lem5484018)). Qed.
Lemma lem5484020 : term211 = True.
Proof. exact (TRANS (@lem5483972) (@lem5484019)). Qed.
Lemma lem5484021 : term210 = True.
Proof. exact (TRANS (@lem5483963) (@lem5484020)). Qed.
Lemma lem5484022 : True = term210.
Proof. exact (SYM (@lem5484021)). Qed.
Lemma lem5484023 : term210.
Proof. exact (EQ_MP (@lem5484022) (@lem0)). Qed.
Lemma lem5484024 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term840 _70606 _70608.
Proof. exact (conj (@lem5484023) (@lem5483960 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484026 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5484027 (_70606 : int) (_70608 : int) : term841 _70606 _70608.
Proof. exact (@lem5484026 term143 (term552 _70606 _70608)). Qed.
Lemma lem5484028 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term842 _70606 _70608.
Proof. exact (@lem5484027 _70606 _70608 (@lem5484024 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484029 (_70606 : int) (_70608 : int) : (term826 _70606 _70608) = (term552 _70606 _70608).
Proof. exact (@lem1982733 (term552 _70606 _70608)). Qed.
Lemma lem5484030 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484031 (_70606 : int) (_70608 : int) : (term843 _70606 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5484030) (@lem5484029 _70606 _70608)). Qed.
Lemma lem5484032 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484033 (_70606 : int) (_70608 : int) : (term842 _70606 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5484031 _70606 _70608) (@lem5484032)). Qed.
Lemma lem5484034 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5484033 _70606 _70608) (@lem5484028 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484036 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5484037 : term210 = term211.
Proof. exact (@lem5484036 term129 term143). Qed.
Lemma lem5484039 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484040 : term143 = term191.
Proof. exact (@lem5484039 term144). Qed.
Lemma lem5484042 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484043 : term129 = term161.
Proof. exact (@lem5484042 (NUMERAL 0)). Qed.
Lemma lem5484044 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484045 : term212 = term213.
Proof. exact (MK_COMB (@lem5484044) (@lem5484043)). Qed.
Lemma lem5484046 : term211 = term214.
Proof. exact (MK_COMB (@lem5484045) (@lem5484040)). Qed.
Lemma lem5484047 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5484049 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484050 : term211 = term217.
Proof. exact (@lem5484049 (NUMERAL 0) term144). Qed.
Lemma lem5484051 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484052 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484053 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484052 h1) (fun h1 : term217 = True => @lem5484051)). Qed.
Lemma lem5484054 : term217 = True.
Proof. exact (EQ_MP (@lem5484053) (@lem5484051)). Qed.
Lemma lem5484055 : term211 = True.
Proof. exact (TRANS (@lem5484050) (@lem5484054)). Qed.
Lemma lem5484056 : True = term211.
Proof. exact (SYM (@lem5484055)). Qed.
Lemma lem5484057 : term211.
Proof. exact (EQ_MP (@lem5484056) (@lem0)). Qed.
Lemma lem5484058 : term219.
Proof. exact (@lem5484047 (@lem5484057)). Qed.
Lemma lem5484060 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484061 : term211 = term217.
Proof. exact (@lem5484060 (NUMERAL 0) term144). Qed.
Lemma lem5484062 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484063 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484064 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484063 h1) (fun h1 : term217 = True => @lem5484062)). Qed.
Lemma lem5484065 : term217 = True.
Proof. exact (EQ_MP (@lem5484064) (@lem5484062)). Qed.
Lemma lem5484066 : term211 = True.
Proof. exact (TRANS (@lem5484061) (@lem5484065)). Qed.
Lemma lem5484067 : True = term211.
Proof. exact (SYM (@lem5484066)). Qed.
Lemma lem5484068 : term211.
Proof. exact (EQ_MP (@lem5484067) (@lem0)). Qed.
Lemma lem5484069 : term214 = term220.
Proof. exact (@lem5484058 (@lem5484068)). Qed.
Lemma lem5484071 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484072 : term173 = term174.
Proof. exact (@lem5484071 term144 term144). Qed.
Lemma lem5484073 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484074 : term176 = term144.
Proof. exact (EQ_MP (@lem5484073) (@lem940073)). Qed.
Lemma lem5484075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484076 : term174 = term143.
Proof. exact (MK_COMB (@lem5484075) (@lem5484074)). Qed.
Lemma lem5484077 : term173 = term143.
Proof. exact (TRANS (@lem5484072) (@lem5484076)). Qed.
Lemma lem5484079 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484080 : term222 = term129.
Proof. exact (@lem5484079 term144). Qed.
Lemma lem5484081 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484082 : term223 = term212.
Proof. exact (MK_COMB (@lem5484081) (@lem5484080)). Qed.
Lemma lem5484083 : term220 = term211.
Proof. exact (MK_COMB (@lem5484082) (@lem5484077)). Qed.
Lemma lem5484085 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484086 : term211 = term217.
Proof. exact (@lem5484085 (NUMERAL 0) term144). Qed.
Lemma lem5484087 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484088 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484089 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484088 h1) (fun h1 : term217 = True => @lem5484087)). Qed.
Lemma lem5484090 : term217 = True.
Proof. exact (EQ_MP (@lem5484089) (@lem5484087)). Qed.
Lemma lem5484091 : term211 = True.
Proof. exact (TRANS (@lem5484086) (@lem5484090)). Qed.
Lemma lem5484092 : term220 = True.
Proof. exact (TRANS (@lem5484083) (@lem5484091)). Qed.
Lemma lem5484093 : term214 = True.
Proof. exact (TRANS (@lem5484069) (@lem5484092)). Qed.
Lemma lem5484094 : term211 = True.
Proof. exact (TRANS (@lem5484046) (@lem5484093)). Qed.
Lemma lem5484095 : term210 = True.
Proof. exact (TRANS (@lem5484037) (@lem5484094)). Qed.
Lemma lem5484096 : True = term210.
Proof. exact (SYM (@lem5484095)). Qed.
Lemma lem5484097 : term210.
Proof. exact (EQ_MP (@lem5484096) (@lem0)). Qed.
Lemma lem5484098 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term844 _70606 _70608.
Proof. exact (conj (@lem5484097) (@lem5483744 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484100 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5484101 (_70606 : int) (_70608 : int) : term845 _70606 _70608.
Proof. exact (@lem5484100 term143 (term583 _70606 _70608)). Qed.
Lemma lem5484102 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term846 _70606 _70608.
Proof. exact (@lem5484101 _70606 _70608 (@lem5484098 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484103 (_70606 : int) (_70608 : int) : (term847 _70606 _70608) = (term583 _70606 _70608).
Proof. exact (@lem1982733 (term583 _70606 _70608)). Qed.
Lemma lem5484104 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484105 (_70606 : int) (_70608 : int) : (term848 _70606 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5484104) (@lem5484103 _70606 _70608)). Qed.
Lemma lem5484106 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484107 (_70606 : int) (_70608 : int) : (term846 _70606 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5484105 _70606 _70608) (@lem5484106)). Qed.
Lemma lem5484108 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (EQ_MP (@lem5484107 _70606 _70608) (@lem5484102 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484109 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term849 _70606 _70608.
Proof. exact (conj (@lem5484108 _70607 _70606 _70608 h1) (@lem5484034 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484111 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5484112 (_70606 : int) (_70608 : int) : term850 _70606 _70608.
Proof. exact (@lem5484111 (term583 _70606 _70608) (term552 _70606 _70608)). Qed.
Lemma lem5484113 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term851 _70606 _70608.
Proof. exact (@lem5484112 _70606 _70608 (@lem5484109 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484114 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = (term853 _70606 _70608).
Proof. exact (@lem1982753 (real_of_int _70606) (term239 _70606) (term239 _70608) (term546 _70608)). Qed.
Lemma lem5484115 (_70606 : int) : (term835 _70606) = (term247 _70606).
Proof. exact (@lem1982715 term164 (real_of_int _70606)). Qed.
Lemma lem5484117 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484118 : term143 = term191.
Proof. exact (@lem5484117 term144). Qed.
Lemma lem5484120 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5484121 : term164 = term165.
Proof. exact (@lem5484120 term144). Qed.
Lemma lem5484122 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484123 : term248 = term249.
Proof. exact (MK_COMB (@lem5484122) (@lem5484121)). Qed.
Lemma lem5484124 : term250 = term251.
Proof. exact (MK_COMB (@lem5484123) (@lem5484118)). Qed.
Lemma lem5484125 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5484127 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484128 : term211 = term217.
Proof. exact (@lem5484127 (NUMERAL 0) term144). Qed.
Lemma lem5484129 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484130 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484131 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484130 h1) (fun h1 : term217 = True => @lem5484129)). Qed.
Lemma lem5484132 : term217 = True.
Proof. exact (EQ_MP (@lem5484131) (@lem5484129)). Qed.
Lemma lem5484133 : term211 = True.
Proof. exact (TRANS (@lem5484128) (@lem5484132)). Qed.
Lemma lem5484134 : True = term211.
Proof. exact (SYM (@lem5484133)). Qed.
Lemma lem5484135 : term211.
Proof. exact (EQ_MP (@lem5484134) (@lem0)). Qed.
Lemma lem5484136 : term253.
Proof. exact (@lem5484125 (@lem5484135)). Qed.
Lemma lem5484138 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484139 : term211 = term217.
Proof. exact (@lem5484138 (NUMERAL 0) term144). Qed.
Lemma lem5484140 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484141 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484142 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484141 h1) (fun h1 : term217 = True => @lem5484140)). Qed.
Lemma lem5484143 : term217 = True.
Proof. exact (EQ_MP (@lem5484142) (@lem5484140)). Qed.
Lemma lem5484144 : term211 = True.
Proof. exact (TRANS (@lem5484139) (@lem5484143)). Qed.
Lemma lem5484145 : True = term211.
Proof. exact (SYM (@lem5484144)). Qed.
Lemma lem5484146 : term211.
Proof. exact (EQ_MP (@lem5484145) (@lem0)). Qed.
Lemma lem5484147 : term254.
Proof. exact (@lem5484136 (@lem5484146)). Qed.
Lemma lem5484149 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484150 : term211 = term217.
Proof. exact (@lem5484149 (NUMERAL 0) term144). Qed.
Lemma lem5484151 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484152 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484153 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484152 h1) (fun h1 : term217 = True => @lem5484151)). Qed.
Lemma lem5484154 : term217 = True.
Proof. exact (EQ_MP (@lem5484153) (@lem5484151)). Qed.
Lemma lem5484155 : term211 = True.
Proof. exact (TRANS (@lem5484150) (@lem5484154)). Qed.
Lemma lem5484156 : True = term211.
Proof. exact (SYM (@lem5484155)). Qed.
Lemma lem5484157 : term211.
Proof. exact (EQ_MP (@lem5484156) (@lem0)). Qed.
Lemma lem5484158 : term255.
Proof. exact (@lem5484147 (@lem5484157)). Qed.
Lemma lem5484160 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484161 : term173 = term174.
Proof. exact (@lem5484160 term144 term144). Qed.
Lemma lem5484162 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484163 : term176 = term144.
Proof. exact (EQ_MP (@lem5484162) (@lem940073)). Qed.
Lemma lem5484164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484165 : term174 = term143.
Proof. exact (MK_COMB (@lem5484164) (@lem5484163)). Qed.
Lemma lem5484166 : term173 = term143.
Proof. exact (TRANS (@lem5484161) (@lem5484165)). Qed.
Lemma lem5484168 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5484169 : term192 = term197.
Proof. exact (@lem5484168 term144 term144). Qed.
Lemma lem5484170 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484171 : term176 = term144.
Proof. exact (EQ_MP (@lem5484170) (@lem940073)). Qed.
Lemma lem5484172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484173 : term174 = term143.
Proof. exact (MK_COMB (@lem5484172) (@lem5484171)). Qed.
Lemma lem5484174 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5484175 : term197 = term164.
Proof. exact (MK_COMB (@lem5484174) (@lem5484173)). Qed.
Lemma lem5484176 : term192 = term164.
Proof. exact (TRANS (@lem5484169) (@lem5484175)). Qed.
Lemma lem5484177 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484178 : term256 = term248.
Proof. exact (MK_COMB (@lem5484177) (@lem5484176)). Qed.
Lemma lem5484179 : term257 = term250.
Proof. exact (MK_COMB (@lem5484178) (@lem5484166)). Qed.
Lemma lem5484181 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5484182 : term250 = term129.
Proof. exact (@lem5484181 term144). Qed.
Lemma lem5484183 : term257 = term129.
Proof. exact (TRANS (@lem5484179) (@lem5484182)). Qed.
Lemma lem5484184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5484185 : term259 = term260.
Proof. exact (MK_COMB (@lem5484184) (@lem5484183)). Qed.
Lemma lem5484186 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5484187 : term261 = term222.
Proof. exact (MK_COMB (@lem5484185) (@lem5484186)). Qed.
Lemma lem5484189 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484190 : term222 = term129.
Proof. exact (@lem5484189 term144). Qed.
Lemma lem5484191 : term261 = term129.
Proof. exact (TRANS (@lem5484187) (@lem5484190)). Qed.
Lemma lem5484193 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484194 : term173 = term174.
Proof. exact (@lem5484193 term144 term144). Qed.
Lemma lem5484195 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484196 : term176 = term144.
Proof. exact (EQ_MP (@lem5484195) (@lem940073)). Qed.
Lemma lem5484197 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484198 : term174 = term143.
Proof. exact (MK_COMB (@lem5484197) (@lem5484196)). Qed.
Lemma lem5484199 : term173 = term143.
Proof. exact (TRANS (@lem5484194) (@lem5484198)). Qed.
Lemma lem5484200 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5484201 : term262 = term222.
Proof. exact (MK_COMB (@lem5484200) (@lem5484199)). Qed.
Lemma lem5484203 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484204 : term222 = term129.
Proof. exact (@lem5484203 term144). Qed.
Lemma lem5484205 : term262 = term129.
Proof. exact (TRANS (@lem5484201) (@lem5484204)). Qed.
Lemma lem5484206 : term129 = term262.
Proof. exact (SYM (@lem5484205)). Qed.
Lemma lem5484207 : term261 = term262.
Proof. exact (TRANS (@lem5484191) (@lem5484206)). Qed.
Lemma lem5484208 : term251 = term161.
Proof. exact (@lem5484158 (@lem5484207)). Qed.
Lemma lem5484209 : term250 = term161.
Proof. exact (TRANS (@lem5484124) (@lem5484208)). Qed.
Lemma lem5484211 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5484212 : term161 = term129.
Proof. exact (@lem5484211 term129). Qed.
Lemma lem5484213 : term250 = term129.
Proof. exact (TRANS (@lem5484209) (@lem5484212)). Qed.
Lemma lem5484214 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5484215 : term263 = term260.
Proof. exact (MK_COMB (@lem5484214) (@lem5484213)). Qed.
Lemma lem5484216 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5484217 (_70606 : int) : (term247 _70606) = (term264 _70606).
Proof. exact (MK_COMB (@lem5484215) (@lem5484216 _70606)). Qed.
Lemma lem5484218 (_70606 : int) : (term835 _70606) = (term264 _70606).
Proof. exact (TRANS (@lem5484115 _70606) (@lem5484217 _70606)). Qed.
Lemma lem5484219 (_70606 : int) : (term264 _70606) = term129.
Proof. exact (@lem1982719 (real_of_int _70606)). Qed.
Lemma lem5484220 (_70606 : int) : (term835 _70606) = term129.
Proof. exact (TRANS (@lem5484218 _70606) (@lem5484219 _70606)). Qed.
Lemma lem5484221 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484222 (_70606 : int) : (term836 _70606) = term266.
Proof. exact (MK_COMB (@lem5484221) (@lem5484220 _70606)). Qed.
Lemma lem5484223 (_70608 : int) : (term854 _70608) = (term281 _70608).
Proof. exact (@lem1982763 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5484224 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5484226 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484227 : term143 = term191.
Proof. exact (@lem5484226 term144). Qed.
Lemma lem5484229 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5484230 : term164 = term165.
Proof. exact (@lem5484229 term144). Qed.
Lemma lem5484231 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484232 : term248 = term249.
Proof. exact (MK_COMB (@lem5484231) (@lem5484230)). Qed.
Lemma lem5484233 : term250 = term251.
Proof. exact (MK_COMB (@lem5484232) (@lem5484227)). Qed.
Lemma lem5484234 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5484236 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484237 : term211 = term217.
Proof. exact (@lem5484236 (NUMERAL 0) term144). Qed.
Lemma lem5484238 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484239 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484240 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484239 h1) (fun h1 : term217 = True => @lem5484238)). Qed.
Lemma lem5484241 : term217 = True.
Proof. exact (EQ_MP (@lem5484240) (@lem5484238)). Qed.
Lemma lem5484242 : term211 = True.
Proof. exact (TRANS (@lem5484237) (@lem5484241)). Qed.
Lemma lem5484243 : True = term211.
Proof. exact (SYM (@lem5484242)). Qed.
Lemma lem5484244 : term211.
Proof. exact (EQ_MP (@lem5484243) (@lem0)). Qed.
Lemma lem5484245 : term253.
Proof. exact (@lem5484234 (@lem5484244)). Qed.
Lemma lem5484247 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484248 : term211 = term217.
Proof. exact (@lem5484247 (NUMERAL 0) term144). Qed.
Lemma lem5484249 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484250 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484251 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484250 h1) (fun h1 : term217 = True => @lem5484249)). Qed.
Lemma lem5484252 : term217 = True.
Proof. exact (EQ_MP (@lem5484251) (@lem5484249)). Qed.
Lemma lem5484253 : term211 = True.
Proof. exact (TRANS (@lem5484248) (@lem5484252)). Qed.
Lemma lem5484254 : True = term211.
Proof. exact (SYM (@lem5484253)). Qed.
Lemma lem5484255 : term211.
Proof. exact (EQ_MP (@lem5484254) (@lem0)). Qed.
Lemma lem5484256 : term254.
Proof. exact (@lem5484245 (@lem5484255)). Qed.
Lemma lem5484258 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484259 : term211 = term217.
Proof. exact (@lem5484258 (NUMERAL 0) term144). Qed.
Lemma lem5484260 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484261 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484262 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484261 h1) (fun h1 : term217 = True => @lem5484260)). Qed.
Lemma lem5484263 : term217 = True.
Proof. exact (EQ_MP (@lem5484262) (@lem5484260)). Qed.
Lemma lem5484264 : term211 = True.
Proof. exact (TRANS (@lem5484259) (@lem5484263)). Qed.
Lemma lem5484265 : True = term211.
Proof. exact (SYM (@lem5484264)). Qed.
Lemma lem5484266 : term211.
Proof. exact (EQ_MP (@lem5484265) (@lem0)). Qed.
Lemma lem5484267 : term255.
Proof. exact (@lem5484256 (@lem5484266)). Qed.
Lemma lem5484269 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484270 : term173 = term174.
Proof. exact (@lem5484269 term144 term144). Qed.
Lemma lem5484271 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484272 : term176 = term144.
Proof. exact (EQ_MP (@lem5484271) (@lem940073)). Qed.
Lemma lem5484273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484274 : term174 = term143.
Proof. exact (MK_COMB (@lem5484273) (@lem5484272)). Qed.
Lemma lem5484275 : term173 = term143.
Proof. exact (TRANS (@lem5484270) (@lem5484274)). Qed.
Lemma lem5484277 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5484278 : term192 = term197.
Proof. exact (@lem5484277 term144 term144). Qed.
Lemma lem5484279 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484280 : term176 = term144.
Proof. exact (EQ_MP (@lem5484279) (@lem940073)). Qed.
Lemma lem5484281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484282 : term174 = term143.
Proof. exact (MK_COMB (@lem5484281) (@lem5484280)). Qed.
Lemma lem5484283 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5484284 : term197 = term164.
Proof. exact (MK_COMB (@lem5484283) (@lem5484282)). Qed.
Lemma lem5484285 : term192 = term164.
Proof. exact (TRANS (@lem5484278) (@lem5484284)). Qed.
Lemma lem5484286 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484287 : term256 = term248.
Proof. exact (MK_COMB (@lem5484286) (@lem5484285)). Qed.
Lemma lem5484288 : term257 = term250.
Proof. exact (MK_COMB (@lem5484287) (@lem5484275)). Qed.
Lemma lem5484290 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5484291 : term250 = term129.
Proof. exact (@lem5484290 term144). Qed.
Lemma lem5484292 : term257 = term129.
Proof. exact (TRANS (@lem5484288) (@lem5484291)). Qed.
Lemma lem5484293 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5484294 : term259 = term260.
Proof. exact (MK_COMB (@lem5484293) (@lem5484292)). Qed.
Lemma lem5484295 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5484296 : term261 = term222.
Proof. exact (MK_COMB (@lem5484294) (@lem5484295)). Qed.
Lemma lem5484298 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484299 : term222 = term129.
Proof. exact (@lem5484298 term144). Qed.
Lemma lem5484300 : term261 = term129.
Proof. exact (TRANS (@lem5484296) (@lem5484299)). Qed.
Lemma lem5484302 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484303 : term173 = term174.
Proof. exact (@lem5484302 term144 term144). Qed.
Lemma lem5484304 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484305 : term176 = term144.
Proof. exact (EQ_MP (@lem5484304) (@lem940073)). Qed.
Lemma lem5484306 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484307 : term174 = term143.
Proof. exact (MK_COMB (@lem5484306) (@lem5484305)). Qed.
Lemma lem5484308 : term173 = term143.
Proof. exact (TRANS (@lem5484303) (@lem5484307)). Qed.
Lemma lem5484309 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5484310 : term262 = term222.
Proof. exact (MK_COMB (@lem5484309) (@lem5484308)). Qed.
Lemma lem5484312 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484313 : term222 = term129.
Proof. exact (@lem5484312 term144). Qed.
Lemma lem5484314 : term262 = term129.
Proof. exact (TRANS (@lem5484310) (@lem5484313)). Qed.
Lemma lem5484315 : term129 = term262.
Proof. exact (SYM (@lem5484314)). Qed.
Lemma lem5484316 : term261 = term262.
Proof. exact (TRANS (@lem5484300) (@lem5484315)). Qed.
Lemma lem5484317 : term251 = term161.
Proof. exact (@lem5484267 (@lem5484316)). Qed.
Lemma lem5484318 : term250 = term161.
Proof. exact (TRANS (@lem5484233) (@lem5484317)). Qed.
Lemma lem5484320 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5484321 : term161 = term129.
Proof. exact (@lem5484320 term129). Qed.
Lemma lem5484322 : term250 = term129.
Proof. exact (TRANS (@lem5484318) (@lem5484321)). Qed.
Lemma lem5484323 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5484324 : term263 = term260.
Proof. exact (MK_COMB (@lem5484323) (@lem5484322)). Qed.
Lemma lem5484325 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5484326 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5484324) (@lem5484325 _70608)). Qed.
Lemma lem5484327 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5484224 _70608) (@lem5484326 _70608)). Qed.
Lemma lem5484328 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5484329 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5484327 _70608) (@lem5484328 _70608)). Qed.
Lemma lem5484330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484331 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5484330) (@lem5484329 _70608)). Qed.
Lemma lem5484332 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5484333 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5484331 _70608) (@lem5484332)). Qed.
Lemma lem5484334 (_70608 : int) : (term854 _70608) = term282.
Proof. exact (TRANS (@lem5484223 _70608) (@lem5484333 _70608)). Qed.
Lemma lem5484335 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5484336 (_70608 : int) : (term854 _70608) = term164.
Proof. exact (TRANS (@lem5484334 _70608) (@lem5484335)). Qed.
Lemma lem5484337 (_70606 : int) (_70608 : int) : (term853 _70606 _70608) = term282.
Proof. exact (MK_COMB (@lem5484222 _70606) (@lem5484336 _70608)). Qed.
Lemma lem5484338 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term282.
Proof. exact (TRANS (@lem5484114 _70606 _70608) (@lem5484337 _70606 _70608)). Qed.
Lemma lem5484339 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5484340 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term164.
Proof. exact (TRANS (@lem5484338 _70606 _70608) (@lem5484339)). Qed.
Lemma lem5484341 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484342 (_70606 : int) (_70608 : int) : (term855 _70606 _70608) = term284.
Proof. exact (MK_COMB (@lem5484341) (@lem5484340 _70606 _70608)). Qed.
Lemma lem5484343 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484344 (_70606 : int) (_70608 : int) : (term851 _70606 _70608) = term285.
Proof. exact (MK_COMB (@lem5484342 _70606 _70608) (@lem5484343)). Qed.
Lemma lem5484345 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : term285.
Proof. exact (EQ_MP (@lem5484344 _70606 _70608) (@lem5484113 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484347 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5484348 : term285 = term286.
Proof. exact (@lem5484347 term129 term164). Qed.
Lemma lem5484350 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5484351 : term164 = term165.
Proof. exact (@lem5484350 term144). Qed.
Lemma lem5484353 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484354 : term129 = term161.
Proof. exact (@lem5484353 (NUMERAL 0)). Qed.
Lemma lem5484355 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5484356 : term131 = term287.
Proof. exact (MK_COMB (@lem5484355) (@lem5484354)). Qed.
Lemma lem5484357 : term286 = term288.
Proof. exact (MK_COMB (@lem5484356) (@lem5484351)). Qed.
Lemma lem5484358 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5484360 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484361 : term211 = term217.
Proof. exact (@lem5484360 (NUMERAL 0) term144). Qed.
Lemma lem5484362 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484363 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484364 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484363 h1) (fun h1 : term217 = True => @lem5484362)). Qed.
Lemma lem5484365 : term217 = True.
Proof. exact (EQ_MP (@lem5484364) (@lem5484362)). Qed.
Lemma lem5484366 : term211 = True.
Proof. exact (TRANS (@lem5484361) (@lem5484365)). Qed.
Lemma lem5484367 : True = term211.
Proof. exact (SYM (@lem5484366)). Qed.
Lemma lem5484368 : term211.
Proof. exact (EQ_MP (@lem5484367) (@lem0)). Qed.
Lemma lem5484369 : term290.
Proof. exact (@lem5484358 (@lem5484368)). Qed.
Lemma lem5484371 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484372 : term211 = term217.
Proof. exact (@lem5484371 (NUMERAL 0) term144). Qed.
Lemma lem5484373 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484374 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484375 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484374 h1) (fun h1 : term217 = True => @lem5484373)). Qed.
Lemma lem5484376 : term217 = True.
Proof. exact (EQ_MP (@lem5484375) (@lem5484373)). Qed.
Lemma lem5484377 : term211 = True.
Proof. exact (TRANS (@lem5484372) (@lem5484376)). Qed.
Lemma lem5484378 : True = term211.
Proof. exact (SYM (@lem5484377)). Qed.
Lemma lem5484379 : term211.
Proof. exact (EQ_MP (@lem5484378) (@lem0)). Qed.
Lemma lem5484380 : term288 = term291.
Proof. exact (@lem5484369 (@lem5484379)). Qed.
Lemma lem5484382 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5484383 : term192 = term197.
Proof. exact (@lem5484382 term144 term144). Qed.
Lemma lem5484384 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484385 : term176 = term144.
Proof. exact (EQ_MP (@lem5484384) (@lem940073)). Qed.
Lemma lem5484386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484387 : term174 = term143.
Proof. exact (MK_COMB (@lem5484386) (@lem5484385)). Qed.
Lemma lem5484388 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5484389 : term197 = term164.
Proof. exact (MK_COMB (@lem5484388) (@lem5484387)). Qed.
Lemma lem5484390 : term192 = term164.
Proof. exact (TRANS (@lem5484383) (@lem5484389)). Qed.
Lemma lem5484392 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484393 : term222 = term129.
Proof. exact (@lem5484392 term144). Qed.
Lemma lem5484394 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5484395 : term292 = term131.
Proof. exact (MK_COMB (@lem5484394) (@lem5484393)). Qed.
Lemma lem5484396 : term291 = term286.
Proof. exact (MK_COMB (@lem5484395) (@lem5484390)). Qed.
Lemma lem5484398 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5484399 : term286 = term295.
Proof. exact (@lem5484398 (NUMERAL 0) term144). Qed.
Lemma lem5484400 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484401 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5484402 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484401 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5484400)). Qed.
Lemma lem5484403 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5484402) (@lem5484400)). Qed.
Lemma lem5484404 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5484405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5484406 : term296 = (and True).
Proof. exact (MK_COMB (@lem5484405) (@lem5484404)). Qed.
Lemma lem5484407 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5484406) (@lem5484403)). Qed.
Lemma lem5484409 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5484410 : term295 = False.
Proof. exact (TRANS (@lem5484407) (@lem5484409)). Qed.
Lemma lem5484411 : term286 = False.
Proof. exact (TRANS (@lem5484399) (@lem5484410)). Qed.
Lemma lem5484412 : term291 = False.
Proof. exact (TRANS (@lem5484396) (@lem5484411)). Qed.
Lemma lem5484413 : term288 = False.
Proof. exact (TRANS (@lem5484380) (@lem5484412)). Qed.
Lemma lem5484414 : term286 = False.
Proof. exact (TRANS (@lem5484357) (@lem5484413)). Qed.
Lemma lem5484415 : term285 = False.
Proof. exact (TRANS (@lem5484348) (@lem5484414)). Qed.
Lemma lem5484416 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term856 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5484415) (@lem5484345 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484417 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term808 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5483044 _70607 _70606 _70608 h1) (fun h0 : term817 _70607 _70606 _70608 => @lem5483730 _70607 _70606 _70608 h0) (fun h0 : term856 _70607 _70606 _70608 => @lem5484416 _70607 _70606 _70608 h0)). Qed.
Lemma lem5484418 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term804 _70607 _70606 _70608) : term804 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5484419 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term857 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5484420 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term805 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484419 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484422 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term756 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484420 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484423 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term184 _70607.
Proof. exact (proj1 (@lem5484420 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484424 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term707 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484422 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484427 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term270 _70607.
Proof. exact (proj1 (@lem5484424 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484437 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5484438 : term210 = term211.
Proof. exact (@lem5484437 term129 term143). Qed.
Lemma lem5484440 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484441 : term143 = term191.
Proof. exact (@lem5484440 term144). Qed.
Lemma lem5484443 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484444 : term129 = term161.
Proof. exact (@lem5484443 (NUMERAL 0)). Qed.
Lemma lem5484445 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484446 : term212 = term213.
Proof. exact (MK_COMB (@lem5484445) (@lem5484444)). Qed.
Lemma lem5484447 : term211 = term214.
Proof. exact (MK_COMB (@lem5484446) (@lem5484441)). Qed.
Lemma lem5484448 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5484450 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484451 : term211 = term217.
Proof. exact (@lem5484450 (NUMERAL 0) term144). Qed.
Lemma lem5484452 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484453 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484454 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484453 h1) (fun h1 : term217 = True => @lem5484452)). Qed.
Lemma lem5484455 : term217 = True.
Proof. exact (EQ_MP (@lem5484454) (@lem5484452)). Qed.
Lemma lem5484456 : term211 = True.
Proof. exact (TRANS (@lem5484451) (@lem5484455)). Qed.
Lemma lem5484457 : True = term211.
Proof. exact (SYM (@lem5484456)). Qed.
Lemma lem5484458 : term211.
Proof. exact (EQ_MP (@lem5484457) (@lem0)). Qed.
Lemma lem5484459 : term219.
Proof. exact (@lem5484448 (@lem5484458)). Qed.
Lemma lem5484461 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484462 : term211 = term217.
Proof. exact (@lem5484461 (NUMERAL 0) term144). Qed.
Lemma lem5484463 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484464 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484465 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484464 h1) (fun h1 : term217 = True => @lem5484463)). Qed.
Lemma lem5484466 : term217 = True.
Proof. exact (EQ_MP (@lem5484465) (@lem5484463)). Qed.
Lemma lem5484467 : term211 = True.
Proof. exact (TRANS (@lem5484462) (@lem5484466)). Qed.
Lemma lem5484468 : True = term211.
Proof. exact (SYM (@lem5484467)). Qed.
Lemma lem5484469 : term211.
Proof. exact (EQ_MP (@lem5484468) (@lem0)). Qed.
Lemma lem5484470 : term214 = term220.
Proof. exact (@lem5484459 (@lem5484469)). Qed.
Lemma lem5484472 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484473 : term173 = term174.
Proof. exact (@lem5484472 term144 term144). Qed.
Lemma lem5484474 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484475 : term176 = term144.
Proof. exact (EQ_MP (@lem5484474) (@lem940073)). Qed.
Lemma lem5484476 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484477 : term174 = term143.
Proof. exact (MK_COMB (@lem5484476) (@lem5484475)). Qed.
Lemma lem5484478 : term173 = term143.
Proof. exact (TRANS (@lem5484473) (@lem5484477)). Qed.
Lemma lem5484480 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484481 : term222 = term129.
Proof. exact (@lem5484480 term144). Qed.
Lemma lem5484482 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484483 : term223 = term212.
Proof. exact (MK_COMB (@lem5484482) (@lem5484481)). Qed.
Lemma lem5484484 : term220 = term211.
Proof. exact (MK_COMB (@lem5484483) (@lem5484478)). Qed.
Lemma lem5484486 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484487 : term211 = term217.
Proof. exact (@lem5484486 (NUMERAL 0) term144). Qed.
Lemma lem5484488 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484489 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484490 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484489 h1) (fun h1 : term217 = True => @lem5484488)). Qed.
Lemma lem5484491 : term217 = True.
Proof. exact (EQ_MP (@lem5484490) (@lem5484488)). Qed.
Lemma lem5484492 : term211 = True.
Proof. exact (TRANS (@lem5484487) (@lem5484491)). Qed.
Lemma lem5484493 : term220 = True.
Proof. exact (TRANS (@lem5484484) (@lem5484492)). Qed.
Lemma lem5484494 : term214 = True.
Proof. exact (TRANS (@lem5484470) (@lem5484493)). Qed.
Lemma lem5484495 : term211 = True.
Proof. exact (TRANS (@lem5484447) (@lem5484494)). Qed.
Lemma lem5484496 : term210 = True.
Proof. exact (TRANS (@lem5484438) (@lem5484495)). Qed.
Lemma lem5484497 : True = term210.
Proof. exact (SYM (@lem5484496)). Qed.
Lemma lem5484498 : term210.
Proof. exact (EQ_MP (@lem5484497) (@lem0)). Qed.
Lemma lem5484499 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term224 _70607.
Proof. exact (conj (@lem5484498) (@lem5484423 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484501 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5484502 (_70607 : int) : term226 _70607.
Proof. exact (@lem5484501 term143 (real_of_int _70607)). Qed.
Lemma lem5484503 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term227 _70607.
Proof. exact (@lem5484502 _70607 (@lem5484499 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484504 (_70607 : int) : (term228 _70607) = (real_of_int _70607).
Proof. exact (@lem1982733 (real_of_int _70607)). Qed.
Lemma lem5484505 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484506 (_70607 : int) : (term229 _70607) = (term183 _70607).
Proof. exact (MK_COMB (@lem5484505) (@lem5484504 _70607)). Qed.
Lemma lem5484507 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484508 (_70607 : int) : (term227 _70607) = (term184 _70607).
Proof. exact (MK_COMB (@lem5484506 _70607) (@lem5484507)). Qed.
Lemma lem5484509 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term184 _70607.
Proof. exact (EQ_MP (@lem5484508 _70607) (@lem5484503 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484511 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5484512 : term210 = term211.
Proof. exact (@lem5484511 term129 term143). Qed.
Lemma lem5484514 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484515 : term143 = term191.
Proof. exact (@lem5484514 term144). Qed.
Lemma lem5484517 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484518 : term129 = term161.
Proof. exact (@lem5484517 (NUMERAL 0)). Qed.
Lemma lem5484519 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484520 : term212 = term213.
Proof. exact (MK_COMB (@lem5484519) (@lem5484518)). Qed.
Lemma lem5484521 : term211 = term214.
Proof. exact (MK_COMB (@lem5484520) (@lem5484515)). Qed.
Lemma lem5484522 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5484524 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484525 : term211 = term217.
Proof. exact (@lem5484524 (NUMERAL 0) term144). Qed.
Lemma lem5484526 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484527 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484528 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484527 h1) (fun h1 : term217 = True => @lem5484526)). Qed.
Lemma lem5484529 : term217 = True.
Proof. exact (EQ_MP (@lem5484528) (@lem5484526)). Qed.
Lemma lem5484530 : term211 = True.
Proof. exact (TRANS (@lem5484525) (@lem5484529)). Qed.
Lemma lem5484531 : True = term211.
Proof. exact (SYM (@lem5484530)). Qed.
Lemma lem5484532 : term211.
Proof. exact (EQ_MP (@lem5484531) (@lem0)). Qed.
Lemma lem5484533 : term219.
Proof. exact (@lem5484522 (@lem5484532)). Qed.
Lemma lem5484535 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484536 : term211 = term217.
Proof. exact (@lem5484535 (NUMERAL 0) term144). Qed.
Lemma lem5484537 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484538 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484539 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484538 h1) (fun h1 : term217 = True => @lem5484537)). Qed.
Lemma lem5484540 : term217 = True.
Proof. exact (EQ_MP (@lem5484539) (@lem5484537)). Qed.
Lemma lem5484541 : term211 = True.
Proof. exact (TRANS (@lem5484536) (@lem5484540)). Qed.
Lemma lem5484542 : True = term211.
Proof. exact (SYM (@lem5484541)). Qed.
Lemma lem5484543 : term211.
Proof. exact (EQ_MP (@lem5484542) (@lem0)). Qed.
Lemma lem5484544 : term214 = term220.
Proof. exact (@lem5484533 (@lem5484543)). Qed.
Lemma lem5484546 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484547 : term173 = term174.
Proof. exact (@lem5484546 term144 term144). Qed.
Lemma lem5484548 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484549 : term176 = term144.
Proof. exact (EQ_MP (@lem5484548) (@lem940073)). Qed.
Lemma lem5484550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484551 : term174 = term143.
Proof. exact (MK_COMB (@lem5484550) (@lem5484549)). Qed.
Lemma lem5484552 : term173 = term143.
Proof. exact (TRANS (@lem5484547) (@lem5484551)). Qed.
Lemma lem5484554 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484555 : term222 = term129.
Proof. exact (@lem5484554 term144). Qed.
Lemma lem5484556 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484557 : term223 = term212.
Proof. exact (MK_COMB (@lem5484556) (@lem5484555)). Qed.
Lemma lem5484558 : term220 = term211.
Proof. exact (MK_COMB (@lem5484557) (@lem5484552)). Qed.
Lemma lem5484560 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484561 : term211 = term217.
Proof. exact (@lem5484560 (NUMERAL 0) term144). Qed.
Lemma lem5484562 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484563 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484564 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484563 h1) (fun h1 : term217 = True => @lem5484562)). Qed.
Lemma lem5484565 : term217 = True.
Proof. exact (EQ_MP (@lem5484564) (@lem5484562)). Qed.
Lemma lem5484566 : term211 = True.
Proof. exact (TRANS (@lem5484561) (@lem5484565)). Qed.
Lemma lem5484567 : term220 = True.
Proof. exact (TRANS (@lem5484558) (@lem5484566)). Qed.
Lemma lem5484568 : term214 = True.
Proof. exact (TRANS (@lem5484544) (@lem5484567)). Qed.
Lemma lem5484569 : term211 = True.
Proof. exact (TRANS (@lem5484521) (@lem5484568)). Qed.
Lemma lem5484570 : term210 = True.
Proof. exact (TRANS (@lem5484512) (@lem5484569)). Qed.
Lemma lem5484571 : True = term210.
Proof. exact (SYM (@lem5484570)). Qed.
Lemma lem5484572 : term210.
Proof. exact (EQ_MP (@lem5484571) (@lem0)). Qed.
Lemma lem5484573 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term271 _70607.
Proof. exact (conj (@lem5484572) (@lem5484427 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484575 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5484576 (_70607 : int) : term272 _70607.
Proof. exact (@lem5484575 term143 (term201 _70607)). Qed.
Lemma lem5484577 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term273 _70607.
Proof. exact (@lem5484576 _70607 (@lem5484573 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484578 (_70607 : int) : (term274 _70607) = (term201 _70607).
Proof. exact (@lem1982733 (term201 _70607)). Qed.
Lemma lem5484579 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484580 (_70607 : int) : (term275 _70607) = (term269 _70607).
Proof. exact (MK_COMB (@lem5484579) (@lem5484578 _70607)). Qed.
Lemma lem5484581 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484582 (_70607 : int) : (term273 _70607) = (term270 _70607).
Proof. exact (MK_COMB (@lem5484580 _70607) (@lem5484581)). Qed.
Lemma lem5484583 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term270 _70607.
Proof. exact (EQ_MP (@lem5484582 _70607) (@lem5484577 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484584 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term276 _70607.
Proof. exact (conj (@lem5484583 _70607 _70606 _70608 h1) (@lem5484509 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484586 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5484587 (_70607 : int) : term278 _70607.
Proof. exact (@lem5484586 (term201 _70607) (real_of_int _70607)). Qed.
Lemma lem5484588 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term279 _70607.
Proof. exact (@lem5484587 _70607 (@lem5484584 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484589 (_70607 : int) : (term280 _70607) = (term281 _70607).
Proof. exact (@lem1982759 (term239 _70607) (real_of_int _70607) term164). Qed.
Lemma lem5484590 (_70607 : int) : (term246 _70607) = (term247 _70607).
Proof. exact (@lem1982713 term164 (real_of_int _70607)). Qed.
Lemma lem5484592 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484593 : term143 = term191.
Proof. exact (@lem5484592 term144). Qed.
Lemma lem5484595 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5484596 : term164 = term165.
Proof. exact (@lem5484595 term144). Qed.
Lemma lem5484597 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484598 : term248 = term249.
Proof. exact (MK_COMB (@lem5484597) (@lem5484596)). Qed.
Lemma lem5484599 : term250 = term251.
Proof. exact (MK_COMB (@lem5484598) (@lem5484593)). Qed.
Lemma lem5484600 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5484602 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484603 : term211 = term217.
Proof. exact (@lem5484602 (NUMERAL 0) term144). Qed.
Lemma lem5484604 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484605 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484606 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484605 h1) (fun h1 : term217 = True => @lem5484604)). Qed.
Lemma lem5484607 : term217 = True.
Proof. exact (EQ_MP (@lem5484606) (@lem5484604)). Qed.
Lemma lem5484608 : term211 = True.
Proof. exact (TRANS (@lem5484603) (@lem5484607)). Qed.
Lemma lem5484609 : True = term211.
Proof. exact (SYM (@lem5484608)). Qed.
Lemma lem5484610 : term211.
Proof. exact (EQ_MP (@lem5484609) (@lem0)). Qed.
Lemma lem5484611 : term253.
Proof. exact (@lem5484600 (@lem5484610)). Qed.
Lemma lem5484613 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484614 : term211 = term217.
Proof. exact (@lem5484613 (NUMERAL 0) term144). Qed.
Lemma lem5484615 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484616 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484617 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484616 h1) (fun h1 : term217 = True => @lem5484615)). Qed.
Lemma lem5484618 : term217 = True.
Proof. exact (EQ_MP (@lem5484617) (@lem5484615)). Qed.
Lemma lem5484619 : term211 = True.
Proof. exact (TRANS (@lem5484614) (@lem5484618)). Qed.
Lemma lem5484620 : True = term211.
Proof. exact (SYM (@lem5484619)). Qed.
Lemma lem5484621 : term211.
Proof. exact (EQ_MP (@lem5484620) (@lem0)). Qed.
Lemma lem5484622 : term254.
Proof. exact (@lem5484611 (@lem5484621)). Qed.
Lemma lem5484624 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484625 : term211 = term217.
Proof. exact (@lem5484624 (NUMERAL 0) term144). Qed.
Lemma lem5484626 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484627 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484628 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484627 h1) (fun h1 : term217 = True => @lem5484626)). Qed.
Lemma lem5484629 : term217 = True.
Proof. exact (EQ_MP (@lem5484628) (@lem5484626)). Qed.
Lemma lem5484630 : term211 = True.
Proof. exact (TRANS (@lem5484625) (@lem5484629)). Qed.
Lemma lem5484631 : True = term211.
Proof. exact (SYM (@lem5484630)). Qed.
Lemma lem5484632 : term211.
Proof. exact (EQ_MP (@lem5484631) (@lem0)). Qed.
Lemma lem5484633 : term255.
Proof. exact (@lem5484622 (@lem5484632)). Qed.
Lemma lem5484635 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484636 : term173 = term174.
Proof. exact (@lem5484635 term144 term144). Qed.
Lemma lem5484637 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484638 : term176 = term144.
Proof. exact (EQ_MP (@lem5484637) (@lem940073)). Qed.
Lemma lem5484639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484640 : term174 = term143.
Proof. exact (MK_COMB (@lem5484639) (@lem5484638)). Qed.
Lemma lem5484641 : term173 = term143.
Proof. exact (TRANS (@lem5484636) (@lem5484640)). Qed.
Lemma lem5484643 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5484644 : term192 = term197.
Proof. exact (@lem5484643 term144 term144). Qed.
Lemma lem5484645 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484646 : term176 = term144.
Proof. exact (EQ_MP (@lem5484645) (@lem940073)). Qed.
Lemma lem5484647 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484648 : term174 = term143.
Proof. exact (MK_COMB (@lem5484647) (@lem5484646)). Qed.
Lemma lem5484649 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5484650 : term197 = term164.
Proof. exact (MK_COMB (@lem5484649) (@lem5484648)). Qed.
Lemma lem5484651 : term192 = term164.
Proof. exact (TRANS (@lem5484644) (@lem5484650)). Qed.
Lemma lem5484652 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484653 : term256 = term248.
Proof. exact (MK_COMB (@lem5484652) (@lem5484651)). Qed.
Lemma lem5484654 : term257 = term250.
Proof. exact (MK_COMB (@lem5484653) (@lem5484641)). Qed.
Lemma lem5484656 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5484657 : term250 = term129.
Proof. exact (@lem5484656 term144). Qed.
Lemma lem5484658 : term257 = term129.
Proof. exact (TRANS (@lem5484654) (@lem5484657)). Qed.
Lemma lem5484659 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5484660 : term259 = term260.
Proof. exact (MK_COMB (@lem5484659) (@lem5484658)). Qed.
Lemma lem5484661 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5484662 : term261 = term222.
Proof. exact (MK_COMB (@lem5484660) (@lem5484661)). Qed.
Lemma lem5484664 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484665 : term222 = term129.
Proof. exact (@lem5484664 term144). Qed.
Lemma lem5484666 : term261 = term129.
Proof. exact (TRANS (@lem5484662) (@lem5484665)). Qed.
Lemma lem5484668 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484669 : term173 = term174.
Proof. exact (@lem5484668 term144 term144). Qed.
Lemma lem5484670 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484671 : term176 = term144.
Proof. exact (EQ_MP (@lem5484670) (@lem940073)). Qed.
Lemma lem5484672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484673 : term174 = term143.
Proof. exact (MK_COMB (@lem5484672) (@lem5484671)). Qed.
Lemma lem5484674 : term173 = term143.
Proof. exact (TRANS (@lem5484669) (@lem5484673)). Qed.
Lemma lem5484675 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5484676 : term262 = term222.
Proof. exact (MK_COMB (@lem5484675) (@lem5484674)). Qed.
Lemma lem5484678 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484679 : term222 = term129.
Proof. exact (@lem5484678 term144). Qed.
Lemma lem5484680 : term262 = term129.
Proof. exact (TRANS (@lem5484676) (@lem5484679)). Qed.
Lemma lem5484681 : term129 = term262.
Proof. exact (SYM (@lem5484680)). Qed.
Lemma lem5484682 : term261 = term262.
Proof. exact (TRANS (@lem5484666) (@lem5484681)). Qed.
Lemma lem5484683 : term251 = term161.
Proof. exact (@lem5484633 (@lem5484682)). Qed.
Lemma lem5484684 : term250 = term161.
Proof. exact (TRANS (@lem5484599) (@lem5484683)). Qed.
Lemma lem5484686 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5484687 : term161 = term129.
Proof. exact (@lem5484686 term129). Qed.
Lemma lem5484688 : term250 = term129.
Proof. exact (TRANS (@lem5484684) (@lem5484687)). Qed.
Lemma lem5484689 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5484690 : term263 = term260.
Proof. exact (MK_COMB (@lem5484689) (@lem5484688)). Qed.
Lemma lem5484691 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5484692 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5484690) (@lem5484691 _70607)). Qed.
Lemma lem5484693 (_70607 : int) : (term246 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5484590 _70607) (@lem5484692 _70607)). Qed.
Lemma lem5484694 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5484695 (_70607 : int) : (term246 _70607) = term129.
Proof. exact (TRANS (@lem5484693 _70607) (@lem5484694 _70607)). Qed.
Lemma lem5484696 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5484697 (_70607 : int) : (term265 _70607) = term266.
Proof. exact (MK_COMB (@lem5484696) (@lem5484695 _70607)). Qed.
Lemma lem5484698 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5484699 (_70607 : int) : (term281 _70607) = term282.
Proof. exact (MK_COMB (@lem5484697 _70607) (@lem5484698)). Qed.
Lemma lem5484700 (_70607 : int) : (term280 _70607) = term282.
Proof. exact (TRANS (@lem5484589 _70607) (@lem5484699 _70607)). Qed.
Lemma lem5484701 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5484702 (_70607 : int) : (term280 _70607) = term164.
Proof. exact (TRANS (@lem5484700 _70607) (@lem5484701)). Qed.
Lemma lem5484703 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484704 (_70607 : int) : (term283 _70607) = term284.
Proof. exact (MK_COMB (@lem5484703) (@lem5484702 _70607)). Qed.
Lemma lem5484705 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484706 (_70607 : int) : (term279 _70607) = term285.
Proof. exact (MK_COMB (@lem5484704 _70607) (@lem5484705)). Qed.
Lemma lem5484707 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : term285.
Proof. exact (EQ_MP (@lem5484706 _70607) (@lem5484588 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484709 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5484710 : term285 = term286.
Proof. exact (@lem5484709 term129 term164). Qed.
Lemma lem5484712 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5484713 : term164 = term165.
Proof. exact (@lem5484712 term144). Qed.
Lemma lem5484715 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484716 : term129 = term161.
Proof. exact (@lem5484715 (NUMERAL 0)). Qed.
Lemma lem5484717 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5484718 : term131 = term287.
Proof. exact (MK_COMB (@lem5484717) (@lem5484716)). Qed.
Lemma lem5484719 : term286 = term288.
Proof. exact (MK_COMB (@lem5484718) (@lem5484713)). Qed.
Lemma lem5484720 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5484722 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484723 : term211 = term217.
Proof. exact (@lem5484722 (NUMERAL 0) term144). Qed.
Lemma lem5484724 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484725 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484726 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484725 h1) (fun h1 : term217 = True => @lem5484724)). Qed.
Lemma lem5484727 : term217 = True.
Proof. exact (EQ_MP (@lem5484726) (@lem5484724)). Qed.
Lemma lem5484728 : term211 = True.
Proof. exact (TRANS (@lem5484723) (@lem5484727)). Qed.
Lemma lem5484729 : True = term211.
Proof. exact (SYM (@lem5484728)). Qed.
Lemma lem5484730 : term211.
Proof. exact (EQ_MP (@lem5484729) (@lem0)). Qed.
Lemma lem5484731 : term290.
Proof. exact (@lem5484720 (@lem5484730)). Qed.
Lemma lem5484733 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484734 : term211 = term217.
Proof. exact (@lem5484733 (NUMERAL 0) term144). Qed.
Lemma lem5484735 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484736 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484737 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484736 h1) (fun h1 : term217 = True => @lem5484735)). Qed.
Lemma lem5484738 : term217 = True.
Proof. exact (EQ_MP (@lem5484737) (@lem5484735)). Qed.
Lemma lem5484739 : term211 = True.
Proof. exact (TRANS (@lem5484734) (@lem5484738)). Qed.
Lemma lem5484740 : True = term211.
Proof. exact (SYM (@lem5484739)). Qed.
Lemma lem5484741 : term211.
Proof. exact (EQ_MP (@lem5484740) (@lem0)). Qed.
Lemma lem5484742 : term288 = term291.
Proof. exact (@lem5484731 (@lem5484741)). Qed.
Lemma lem5484744 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5484745 : term192 = term197.
Proof. exact (@lem5484744 term144 term144). Qed.
Lemma lem5484746 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484747 : term176 = term144.
Proof. exact (EQ_MP (@lem5484746) (@lem940073)). Qed.
Lemma lem5484748 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484749 : term174 = term143.
Proof. exact (MK_COMB (@lem5484748) (@lem5484747)). Qed.
Lemma lem5484750 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5484751 : term197 = term164.
Proof. exact (MK_COMB (@lem5484750) (@lem5484749)). Qed.
Lemma lem5484752 : term192 = term164.
Proof. exact (TRANS (@lem5484745) (@lem5484751)). Qed.
Lemma lem5484754 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484755 : term222 = term129.
Proof. exact (@lem5484754 term144). Qed.
Lemma lem5484756 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5484757 : term292 = term131.
Proof. exact (MK_COMB (@lem5484756) (@lem5484755)). Qed.
Lemma lem5484758 : term291 = term286.
Proof. exact (MK_COMB (@lem5484757) (@lem5484752)). Qed.
Lemma lem5484760 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5484761 : term286 = term295.
Proof. exact (@lem5484760 (NUMERAL 0) term144). Qed.
Lemma lem5484762 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484763 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5484764 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484763 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5484762)). Qed.
Lemma lem5484765 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5484764) (@lem5484762)). Qed.
Lemma lem5484766 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5484767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5484768 : term296 = (and True).
Proof. exact (MK_COMB (@lem5484767) (@lem5484766)). Qed.
Lemma lem5484769 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5484768) (@lem5484765)). Qed.
Lemma lem5484771 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5484772 : term295 = False.
Proof. exact (TRANS (@lem5484769) (@lem5484771)). Qed.
Lemma lem5484773 : term286 = False.
Proof. exact (TRANS (@lem5484761) (@lem5484772)). Qed.
Lemma lem5484774 : term291 = False.
Proof. exact (TRANS (@lem5484758) (@lem5484773)). Qed.
Lemma lem5484775 : term288 = False.
Proof. exact (TRANS (@lem5484742) (@lem5484774)). Qed.
Lemma lem5484776 : term286 = False.
Proof. exact (TRANS (@lem5484719) (@lem5484775)). Qed.
Lemma lem5484777 : term285 = False.
Proof. exact (TRANS (@lem5484710) (@lem5484776)). Qed.
Lemma lem5484778 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term857 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5484777) (@lem5484707 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484779 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term858 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5484780 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term806 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484779 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484782 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term757 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484780 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484784 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term708 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484782 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484786 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term659 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484784 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484787 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term549 _70607.
Proof. exact (proj1 (@lem5484784 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484788 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term592 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5484786 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484789 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term578 _70607 _70606.
Proof. exact (proj1 (@lem5484786 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484790 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : (real_of_int _70606) = term129.
Proof. exact (proj2 (@lem5484789 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484792 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term590 _70606 _70608.
Proof. exact (proj2 (@lem5484788 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484793 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term587 _70607 _70608.
Proof. exact (proj1 (@lem5484788 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484794 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (proj2 (@lem5484792 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484797 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5484798 : term210 = term211.
Proof. exact (@lem5484797 term129 term143). Qed.
Lemma lem5484800 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484801 : term143 = term191.
Proof. exact (@lem5484800 term144). Qed.
Lemma lem5484803 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484804 : term129 = term161.
Proof. exact (@lem5484803 (NUMERAL 0)). Qed.
Lemma lem5484805 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484806 : term212 = term213.
Proof. exact (MK_COMB (@lem5484805) (@lem5484804)). Qed.
Lemma lem5484807 : term211 = term214.
Proof. exact (MK_COMB (@lem5484806) (@lem5484801)). Qed.
Lemma lem5484808 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5484810 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484811 : term211 = term217.
Proof. exact (@lem5484810 (NUMERAL 0) term144). Qed.
Lemma lem5484812 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484813 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484814 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484813 h1) (fun h1 : term217 = True => @lem5484812)). Qed.
Lemma lem5484815 : term217 = True.
Proof. exact (EQ_MP (@lem5484814) (@lem5484812)). Qed.
Lemma lem5484816 : term211 = True.
Proof. exact (TRANS (@lem5484811) (@lem5484815)). Qed.
Lemma lem5484817 : True = term211.
Proof. exact (SYM (@lem5484816)). Qed.
Lemma lem5484818 : term211.
Proof. exact (EQ_MP (@lem5484817) (@lem0)). Qed.
Lemma lem5484819 : term219.
Proof. exact (@lem5484808 (@lem5484818)). Qed.
Lemma lem5484821 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484822 : term211 = term217.
Proof. exact (@lem5484821 (NUMERAL 0) term144). Qed.
Lemma lem5484823 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484824 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484825 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484824 h1) (fun h1 : term217 = True => @lem5484823)). Qed.
Lemma lem5484826 : term217 = True.
Proof. exact (EQ_MP (@lem5484825) (@lem5484823)). Qed.
Lemma lem5484827 : term211 = True.
Proof. exact (TRANS (@lem5484822) (@lem5484826)). Qed.
Lemma lem5484828 : True = term211.
Proof. exact (SYM (@lem5484827)). Qed.
Lemma lem5484829 : term211.
Proof. exact (EQ_MP (@lem5484828) (@lem0)). Qed.
Lemma lem5484830 : term214 = term220.
Proof. exact (@lem5484819 (@lem5484829)). Qed.
Lemma lem5484832 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484833 : term173 = term174.
Proof. exact (@lem5484832 term144 term144). Qed.
Lemma lem5484834 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484835 : term176 = term144.
Proof. exact (EQ_MP (@lem5484834) (@lem940073)). Qed.
Lemma lem5484836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484837 : term174 = term143.
Proof. exact (MK_COMB (@lem5484836) (@lem5484835)). Qed.
Lemma lem5484838 : term173 = term143.
Proof. exact (TRANS (@lem5484833) (@lem5484837)). Qed.
Lemma lem5484840 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484841 : term222 = term129.
Proof. exact (@lem5484840 term144). Qed.
Lemma lem5484842 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484843 : term223 = term212.
Proof. exact (MK_COMB (@lem5484842) (@lem5484841)). Qed.
Lemma lem5484844 : term220 = term211.
Proof. exact (MK_COMB (@lem5484843) (@lem5484838)). Qed.
Lemma lem5484846 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484847 : term211 = term217.
Proof. exact (@lem5484846 (NUMERAL 0) term144). Qed.
Lemma lem5484848 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484849 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484850 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484849 h1) (fun h1 : term217 = True => @lem5484848)). Qed.
Lemma lem5484851 : term217 = True.
Proof. exact (EQ_MP (@lem5484850) (@lem5484848)). Qed.
Lemma lem5484852 : term211 = True.
Proof. exact (TRANS (@lem5484847) (@lem5484851)). Qed.
Lemma lem5484853 : term220 = True.
Proof. exact (TRANS (@lem5484844) (@lem5484852)). Qed.
Lemma lem5484854 : term214 = True.
Proof. exact (TRANS (@lem5484830) (@lem5484853)). Qed.
Lemma lem5484855 : term211 = True.
Proof. exact (TRANS (@lem5484807) (@lem5484854)). Qed.
Lemma lem5484856 : term210 = True.
Proof. exact (TRANS (@lem5484798) (@lem5484855)). Qed.
Lemma lem5484857 : True = term210.
Proof. exact (SYM (@lem5484856)). Qed.
Lemma lem5484858 : term210.
Proof. exact (EQ_MP (@lem5484857) (@lem0)). Qed.
Lemma lem5484859 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term859 _70607.
Proof. exact (conj (@lem5484858) (@lem5484787 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484861 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5484862 (_70607 : int) : term860 _70607.
Proof. exact (@lem5484861 term143 (term546 _70607)). Qed.
Lemma lem5484863 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term861 _70607.
Proof. exact (@lem5484862 _70607 (@lem5484859 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484864 (_70607 : int) : (term862 _70607) = (term546 _70607).
Proof. exact (@lem1982733 (term546 _70607)). Qed.
Lemma lem5484865 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484866 (_70607 : int) : (term863 _70607) = (term548 _70607).
Proof. exact (MK_COMB (@lem5484865) (@lem5484864 _70607)). Qed.
Lemma lem5484867 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484868 (_70607 : int) : (term861 _70607) = (term549 _70607).
Proof. exact (MK_COMB (@lem5484866 _70607) (@lem5484867)). Qed.
Lemma lem5484869 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term549 _70607.
Proof. exact (EQ_MP (@lem5484868 _70607) (@lem5484863 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484871 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5484872 : term210 = term211.
Proof. exact (@lem5484871 term129 term143). Qed.
Lemma lem5484874 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484875 : term143 = term191.
Proof. exact (@lem5484874 term144). Qed.
Lemma lem5484877 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484878 : term129 = term161.
Proof. exact (@lem5484877 (NUMERAL 0)). Qed.
Lemma lem5484879 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484880 : term212 = term213.
Proof. exact (MK_COMB (@lem5484879) (@lem5484878)). Qed.
Lemma lem5484881 : term211 = term214.
Proof. exact (MK_COMB (@lem5484880) (@lem5484875)). Qed.
Lemma lem5484882 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5484884 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484885 : term211 = term217.
Proof. exact (@lem5484884 (NUMERAL 0) term144). Qed.
Lemma lem5484886 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484887 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484888 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484887 h1) (fun h1 : term217 = True => @lem5484886)). Qed.
Lemma lem5484889 : term217 = True.
Proof. exact (EQ_MP (@lem5484888) (@lem5484886)). Qed.
Lemma lem5484890 : term211 = True.
Proof. exact (TRANS (@lem5484885) (@lem5484889)). Qed.
Lemma lem5484891 : True = term211.
Proof. exact (SYM (@lem5484890)). Qed.
Lemma lem5484892 : term211.
Proof. exact (EQ_MP (@lem5484891) (@lem0)). Qed.
Lemma lem5484893 : term219.
Proof. exact (@lem5484882 (@lem5484892)). Qed.
Lemma lem5484895 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484896 : term211 = term217.
Proof. exact (@lem5484895 (NUMERAL 0) term144). Qed.
Lemma lem5484897 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484898 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484899 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484898 h1) (fun h1 : term217 = True => @lem5484897)). Qed.
Lemma lem5484900 : term217 = True.
Proof. exact (EQ_MP (@lem5484899) (@lem5484897)). Qed.
Lemma lem5484901 : term211 = True.
Proof. exact (TRANS (@lem5484896) (@lem5484900)). Qed.
Lemma lem5484902 : True = term211.
Proof. exact (SYM (@lem5484901)). Qed.
Lemma lem5484903 : term211.
Proof. exact (EQ_MP (@lem5484902) (@lem0)). Qed.
Lemma lem5484904 : term214 = term220.
Proof. exact (@lem5484893 (@lem5484903)). Qed.
Lemma lem5484906 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484907 : term173 = term174.
Proof. exact (@lem5484906 term144 term144). Qed.
Lemma lem5484908 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484909 : term176 = term144.
Proof. exact (EQ_MP (@lem5484908) (@lem940073)). Qed.
Lemma lem5484910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484911 : term174 = term143.
Proof. exact (MK_COMB (@lem5484910) (@lem5484909)). Qed.
Lemma lem5484912 : term173 = term143.
Proof. exact (TRANS (@lem5484907) (@lem5484911)). Qed.
Lemma lem5484914 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484915 : term222 = term129.
Proof. exact (@lem5484914 term144). Qed.
Lemma lem5484916 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484917 : term223 = term212.
Proof. exact (MK_COMB (@lem5484916) (@lem5484915)). Qed.
Lemma lem5484918 : term220 = term211.
Proof. exact (MK_COMB (@lem5484917) (@lem5484912)). Qed.
Lemma lem5484920 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484921 : term211 = term217.
Proof. exact (@lem5484920 (NUMERAL 0) term144). Qed.
Lemma lem5484922 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484923 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484924 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484923 h1) (fun h1 : term217 = True => @lem5484922)). Qed.
Lemma lem5484925 : term217 = True.
Proof. exact (EQ_MP (@lem5484924) (@lem5484922)). Qed.
Lemma lem5484926 : term211 = True.
Proof. exact (TRANS (@lem5484921) (@lem5484925)). Qed.
Lemma lem5484927 : term220 = True.
Proof. exact (TRANS (@lem5484918) (@lem5484926)). Qed.
Lemma lem5484928 : term214 = True.
Proof. exact (TRANS (@lem5484904) (@lem5484927)). Qed.
Lemma lem5484929 : term211 = True.
Proof. exact (TRANS (@lem5484881) (@lem5484928)). Qed.
Lemma lem5484930 : term210 = True.
Proof. exact (TRANS (@lem5484872) (@lem5484929)). Qed.
Lemma lem5484931 : True = term210.
Proof. exact (SYM (@lem5484930)). Qed.
Lemma lem5484932 : term210.
Proof. exact (EQ_MP (@lem5484931) (@lem0)). Qed.
Lemma lem5484933 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term818 _70607 _70608.
Proof. exact (conj (@lem5484932) (@lem5484793 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484935 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5484936 (_70607 : int) (_70608 : int) : term819 _70607 _70608.
Proof. exact (@lem5484935 term143 (term584 _70607 _70608)). Qed.
Lemma lem5484937 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term820 _70607 _70608.
Proof. exact (@lem5484936 _70607 _70608 (@lem5484933 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484938 (_70607 : int) (_70608 : int) : (term821 _70607 _70608) = (term584 _70607 _70608).
Proof. exact (@lem1982733 (term584 _70607 _70608)). Qed.
Lemma lem5484939 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5484940 (_70607 : int) (_70608 : int) : (term822 _70607 _70608) = (term586 _70607 _70608).
Proof. exact (MK_COMB (@lem5484939) (@lem5484938 _70607 _70608)). Qed.
Lemma lem5484941 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5484942 (_70607 : int) (_70608 : int) : (term820 _70607 _70608) = (term587 _70607 _70608).
Proof. exact (MK_COMB (@lem5484940 _70607 _70608) (@lem5484941)). Qed.
Lemma lem5484943 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term587 _70607 _70608.
Proof. exact (EQ_MP (@lem5484942 _70607 _70608) (@lem5484937 _70607 _70606 _70608 h1)). Qed.
Lemma lem5484945 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5484946 : term210 = term211.
Proof. exact (@lem5484945 term129 term143). Qed.
Lemma lem5484948 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484949 : term143 = term191.
Proof. exact (@lem5484948 term144). Qed.
Lemma lem5484951 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5484952 : term129 = term161.
Proof. exact (@lem5484951 (NUMERAL 0)). Qed.
Lemma lem5484953 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484954 : term212 = term213.
Proof. exact (MK_COMB (@lem5484953) (@lem5484952)). Qed.
Lemma lem5484955 : term211 = term214.
Proof. exact (MK_COMB (@lem5484954) (@lem5484949)). Qed.
Lemma lem5484956 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5484958 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484959 : term211 = term217.
Proof. exact (@lem5484958 (NUMERAL 0) term144). Qed.
Lemma lem5484960 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484961 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484962 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484961 h1) (fun h1 : term217 = True => @lem5484960)). Qed.
Lemma lem5484963 : term217 = True.
Proof. exact (EQ_MP (@lem5484962) (@lem5484960)). Qed.
Lemma lem5484964 : term211 = True.
Proof. exact (TRANS (@lem5484959) (@lem5484963)). Qed.
Lemma lem5484965 : True = term211.
Proof. exact (SYM (@lem5484964)). Qed.
Lemma lem5484966 : term211.
Proof. exact (EQ_MP (@lem5484965) (@lem0)). Qed.
Lemma lem5484967 : term219.
Proof. exact (@lem5484956 (@lem5484966)). Qed.
Lemma lem5484969 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484970 : term211 = term217.
Proof. exact (@lem5484969 (NUMERAL 0) term144). Qed.
Lemma lem5484971 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484972 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484973 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484972 h1) (fun h1 : term217 = True => @lem5484971)). Qed.
Lemma lem5484974 : term217 = True.
Proof. exact (EQ_MP (@lem5484973) (@lem5484971)). Qed.
Lemma lem5484975 : term211 = True.
Proof. exact (TRANS (@lem5484970) (@lem5484974)). Qed.
Lemma lem5484976 : True = term211.
Proof. exact (SYM (@lem5484975)). Qed.
Lemma lem5484977 : term211.
Proof. exact (EQ_MP (@lem5484976) (@lem0)). Qed.
Lemma lem5484978 : term214 = term220.
Proof. exact (@lem5484967 (@lem5484977)). Qed.
Lemma lem5484980 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5484981 : term173 = term174.
Proof. exact (@lem5484980 term144 term144). Qed.
Lemma lem5484982 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5484983 : term176 = term144.
Proof. exact (EQ_MP (@lem5484982) (@lem940073)). Qed.
Lemma lem5484984 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5484985 : term174 = term143.
Proof. exact (MK_COMB (@lem5484984) (@lem5484983)). Qed.
Lemma lem5484986 : term173 = term143.
Proof. exact (TRANS (@lem5484981) (@lem5484985)). Qed.
Lemma lem5484988 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5484989 : term222 = term129.
Proof. exact (@lem5484988 term144). Qed.
Lemma lem5484990 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5484991 : term223 = term212.
Proof. exact (MK_COMB (@lem5484990) (@lem5484989)). Qed.
Lemma lem5484992 : term220 = term211.
Proof. exact (MK_COMB (@lem5484991) (@lem5484986)). Qed.
Lemma lem5484994 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5484995 : term211 = term217.
Proof. exact (@lem5484994 (NUMERAL 0) term144). Qed.
Lemma lem5484996 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5484997 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5484998 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5484997 h1) (fun h1 : term217 = True => @lem5484996)). Qed.
Lemma lem5484999 : term217 = True.
Proof. exact (EQ_MP (@lem5484998) (@lem5484996)). Qed.
Lemma lem5485000 : term211 = True.
Proof. exact (TRANS (@lem5484995) (@lem5484999)). Qed.
Lemma lem5485001 : term220 = True.
Proof. exact (TRANS (@lem5484992) (@lem5485000)). Qed.
Lemma lem5485002 : term214 = True.
Proof. exact (TRANS (@lem5484978) (@lem5485001)). Qed.
Lemma lem5485003 : term211 = True.
Proof. exact (TRANS (@lem5484955) (@lem5485002)). Qed.
Lemma lem5485004 : term210 = True.
Proof. exact (TRANS (@lem5484946) (@lem5485003)). Qed.
Lemma lem5485005 : True = term210.
Proof. exact (SYM (@lem5485004)). Qed.
Lemma lem5485006 : term210.
Proof. exact (EQ_MP (@lem5485005) (@lem0)). Qed.
Lemma lem5485007 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term844 _70606 _70608.
Proof. exact (conj (@lem5485006) (@lem5484794 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485009 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5485010 (_70606 : int) (_70608 : int) : term845 _70606 _70608.
Proof. exact (@lem5485009 term143 (term583 _70606 _70608)). Qed.
Lemma lem5485011 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term846 _70606 _70608.
Proof. exact (@lem5485010 _70606 _70608 (@lem5485007 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485012 (_70606 : int) (_70608 : int) : (term847 _70606 _70608) = (term583 _70606 _70608).
Proof. exact (@lem1982733 (term583 _70606 _70608)). Qed.
Lemma lem5485013 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485014 (_70606 : int) (_70608 : int) : (term848 _70606 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5485013) (@lem5485012 _70606 _70608)). Qed.
Lemma lem5485015 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485016 (_70606 : int) (_70608 : int) : (term846 _70606 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5485014 _70606 _70608) (@lem5485015)). Qed.
Lemma lem5485017 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (EQ_MP (@lem5485016 _70606 _70608) (@lem5485011 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485019 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5485020 (_70606 : int) : term236 _70606.
Proof. exact (@lem5485019 (real_of_int _70606)). Qed.
Lemma lem5485021 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term237 _70606.
Proof. exact (@lem5485020 _70606 (@lem5484790 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485022 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term238 _70606.
Proof. exact (@lem5485021 _70607 _70606 _70608 h1 term164). Qed.
Lemma lem5485023 (_70606 : int) : (term238 _70606) = ((term239 _70606) = term129).
Proof. exact (eq_refl (term238 _70606)). Qed.
Lemma lem5485030 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : (term239 _70606) = term129.
Proof. exact (EQ_MP (@lem5485023 _70606) (@lem5485022 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485031 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term864 _70606 _70608.
Proof. exact (conj (@lem5485030 _70607 _70606 _70608 h1) (@lem5485017 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485033 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5485034 (_70606 : int) (_70608 : int) : term865 _70606 _70608.
Proof. exact (@lem5485033 (term239 _70606) (term583 _70606 _70608)). Qed.
Lemma lem5485035 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term866 _70606 _70608.
Proof. exact (@lem5485034 _70606 _70608 (@lem5485031 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485036 (_70606 : int) (_70608 : int) : (term867 _70606 _70608) = (term868 _70606 _70608).
Proof. exact (@lem1982763 (term239 _70606) (real_of_int _70606) (term239 _70608)). Qed.
Lemma lem5485037 (_70606 : int) : (term246 _70606) = (term247 _70606).
Proof. exact (@lem1982713 term164 (real_of_int _70606)). Qed.
Lemma lem5485039 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485040 : term143 = term191.
Proof. exact (@lem5485039 term144). Qed.
Lemma lem5485042 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5485043 : term164 = term165.
Proof. exact (@lem5485042 term144). Qed.
Lemma lem5485044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485045 : term248 = term249.
Proof. exact (MK_COMB (@lem5485044) (@lem5485043)). Qed.
Lemma lem5485046 : term250 = term251.
Proof. exact (MK_COMB (@lem5485045) (@lem5485040)). Qed.
Lemma lem5485047 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5485049 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485050 : term211 = term217.
Proof. exact (@lem5485049 (NUMERAL 0) term144). Qed.
Lemma lem5485051 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485052 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485053 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485052 h1) (fun h1 : term217 = True => @lem5485051)). Qed.
Lemma lem5485054 : term217 = True.
Proof. exact (EQ_MP (@lem5485053) (@lem5485051)). Qed.
Lemma lem5485055 : term211 = True.
Proof. exact (TRANS (@lem5485050) (@lem5485054)). Qed.
Lemma lem5485056 : True = term211.
Proof. exact (SYM (@lem5485055)). Qed.
Lemma lem5485057 : term211.
Proof. exact (EQ_MP (@lem5485056) (@lem0)). Qed.
Lemma lem5485058 : term253.
Proof. exact (@lem5485047 (@lem5485057)). Qed.
Lemma lem5485060 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485061 : term211 = term217.
Proof. exact (@lem5485060 (NUMERAL 0) term144). Qed.
Lemma lem5485062 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485063 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485064 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485063 h1) (fun h1 : term217 = True => @lem5485062)). Qed.
Lemma lem5485065 : term217 = True.
Proof. exact (EQ_MP (@lem5485064) (@lem5485062)). Qed.
Lemma lem5485066 : term211 = True.
Proof. exact (TRANS (@lem5485061) (@lem5485065)). Qed.
Lemma lem5485067 : True = term211.
Proof. exact (SYM (@lem5485066)). Qed.
Lemma lem5485068 : term211.
Proof. exact (EQ_MP (@lem5485067) (@lem0)). Qed.
Lemma lem5485069 : term254.
Proof. exact (@lem5485058 (@lem5485068)). Qed.
Lemma lem5485071 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485072 : term211 = term217.
Proof. exact (@lem5485071 (NUMERAL 0) term144). Qed.
Lemma lem5485073 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485074 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485075 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485074 h1) (fun h1 : term217 = True => @lem5485073)). Qed.
Lemma lem5485076 : term217 = True.
Proof. exact (EQ_MP (@lem5485075) (@lem5485073)). Qed.
Lemma lem5485077 : term211 = True.
Proof. exact (TRANS (@lem5485072) (@lem5485076)). Qed.
Lemma lem5485078 : True = term211.
Proof. exact (SYM (@lem5485077)). Qed.
Lemma lem5485079 : term211.
Proof. exact (EQ_MP (@lem5485078) (@lem0)). Qed.
Lemma lem5485080 : term255.
Proof. exact (@lem5485069 (@lem5485079)). Qed.
Lemma lem5485082 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485083 : term173 = term174.
Proof. exact (@lem5485082 term144 term144). Qed.
Lemma lem5485084 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485085 : term176 = term144.
Proof. exact (EQ_MP (@lem5485084) (@lem940073)). Qed.
Lemma lem5485086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485087 : term174 = term143.
Proof. exact (MK_COMB (@lem5485086) (@lem5485085)). Qed.
Lemma lem5485088 : term173 = term143.
Proof. exact (TRANS (@lem5485083) (@lem5485087)). Qed.
Lemma lem5485090 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5485091 : term192 = term197.
Proof. exact (@lem5485090 term144 term144). Qed.
Lemma lem5485092 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485093 : term176 = term144.
Proof. exact (EQ_MP (@lem5485092) (@lem940073)). Qed.
Lemma lem5485094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485095 : term174 = term143.
Proof. exact (MK_COMB (@lem5485094) (@lem5485093)). Qed.
Lemma lem5485096 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5485097 : term197 = term164.
Proof. exact (MK_COMB (@lem5485096) (@lem5485095)). Qed.
Lemma lem5485098 : term192 = term164.
Proof. exact (TRANS (@lem5485091) (@lem5485097)). Qed.
Lemma lem5485099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485100 : term256 = term248.
Proof. exact (MK_COMB (@lem5485099) (@lem5485098)). Qed.
Lemma lem5485101 : term257 = term250.
Proof. exact (MK_COMB (@lem5485100) (@lem5485088)). Qed.
Lemma lem5485103 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5485104 : term250 = term129.
Proof. exact (@lem5485103 term144). Qed.
Lemma lem5485105 : term257 = term129.
Proof. exact (TRANS (@lem5485101) (@lem5485104)). Qed.
Lemma lem5485106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485107 : term259 = term260.
Proof. exact (MK_COMB (@lem5485106) (@lem5485105)). Qed.
Lemma lem5485108 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5485109 : term261 = term222.
Proof. exact (MK_COMB (@lem5485107) (@lem5485108)). Qed.
Lemma lem5485111 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485112 : term222 = term129.
Proof. exact (@lem5485111 term144). Qed.
Lemma lem5485113 : term261 = term129.
Proof. exact (TRANS (@lem5485109) (@lem5485112)). Qed.
Lemma lem5485115 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485116 : term173 = term174.
Proof. exact (@lem5485115 term144 term144). Qed.
Lemma lem5485117 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485118 : term176 = term144.
Proof. exact (EQ_MP (@lem5485117) (@lem940073)). Qed.
Lemma lem5485119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485120 : term174 = term143.
Proof. exact (MK_COMB (@lem5485119) (@lem5485118)). Qed.
Lemma lem5485121 : term173 = term143.
Proof. exact (TRANS (@lem5485116) (@lem5485120)). Qed.
Lemma lem5485122 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5485123 : term262 = term222.
Proof. exact (MK_COMB (@lem5485122) (@lem5485121)). Qed.
Lemma lem5485125 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485126 : term222 = term129.
Proof. exact (@lem5485125 term144). Qed.
Lemma lem5485127 : term262 = term129.
Proof. exact (TRANS (@lem5485123) (@lem5485126)). Qed.
Lemma lem5485128 : term129 = term262.
Proof. exact (SYM (@lem5485127)). Qed.
Lemma lem5485129 : term261 = term262.
Proof. exact (TRANS (@lem5485113) (@lem5485128)). Qed.
Lemma lem5485130 : term251 = term161.
Proof. exact (@lem5485080 (@lem5485129)). Qed.
Lemma lem5485131 : term250 = term161.
Proof. exact (TRANS (@lem5485046) (@lem5485130)). Qed.
Lemma lem5485133 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5485134 : term161 = term129.
Proof. exact (@lem5485133 term129). Qed.
Lemma lem5485135 : term250 = term129.
Proof. exact (TRANS (@lem5485131) (@lem5485134)). Qed.
Lemma lem5485136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485137 : term263 = term260.
Proof. exact (MK_COMB (@lem5485136) (@lem5485135)). Qed.
Lemma lem5485138 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5485139 (_70606 : int) : (term247 _70606) = (term264 _70606).
Proof. exact (MK_COMB (@lem5485137) (@lem5485138 _70606)). Qed.
Lemma lem5485140 (_70606 : int) : (term246 _70606) = (term264 _70606).
Proof. exact (TRANS (@lem5485037 _70606) (@lem5485139 _70606)). Qed.
Lemma lem5485141 (_70606 : int) : (term264 _70606) = term129.
Proof. exact (@lem1982719 (real_of_int _70606)). Qed.
Lemma lem5485142 (_70606 : int) : (term246 _70606) = term129.
Proof. exact (TRANS (@lem5485140 _70606) (@lem5485141 _70606)). Qed.
Lemma lem5485143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485144 (_70606 : int) : (term265 _70606) = term266.
Proof. exact (MK_COMB (@lem5485143) (@lem5485142 _70606)). Qed.
Lemma lem5485145 (_70608 : int) : (term239 _70608) = (term239 _70608).
Proof. exact (eq_refl (term239 _70608)). Qed.
Lemma lem5485146 (_70606 : int) (_70608 : int) : (term868 _70606 _70608) = (term869 _70608).
Proof. exact (MK_COMB (@lem5485144 _70606) (@lem5485145 _70608)). Qed.
Lemma lem5485147 (_70606 : int) (_70608 : int) : (term867 _70606 _70608) = (term869 _70608).
Proof. exact (TRANS (@lem5485036 _70606 _70608) (@lem5485146 _70606 _70608)). Qed.
Lemma lem5485148 (_70608 : int) : (term869 _70608) = (term239 _70608).
Proof. exact (@lem1982721 (term239 _70608)). Qed.
Lemma lem5485149 (_70606 : int) (_70608 : int) : (term867 _70606 _70608) = (term239 _70608).
Proof. exact (TRANS (@lem5485147 _70606 _70608) (@lem5485148 _70608)). Qed.
Lemma lem5485150 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485151 (_70606 : int) (_70608 : int) : (term870 _70606 _70608) = (term575 _70608).
Proof. exact (MK_COMB (@lem5485150) (@lem5485149 _70606 _70608)). Qed.
Lemma lem5485152 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485153 (_70606 : int) (_70608 : int) : (term866 _70606 _70608) = (term576 _70608).
Proof. exact (MK_COMB (@lem5485151 _70606 _70608) (@lem5485152)). Qed.
Lemma lem5485154 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term576 _70608.
Proof. exact (EQ_MP (@lem5485153 _70606 _70608) (@lem5485035 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485156 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5485157 : term210 = term211.
Proof. exact (@lem5485156 term129 term143). Qed.
Lemma lem5485159 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485160 : term143 = term191.
Proof. exact (@lem5485159 term144). Qed.
Lemma lem5485162 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485163 : term129 = term161.
Proof. exact (@lem5485162 (NUMERAL 0)). Qed.
Lemma lem5485164 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485165 : term212 = term213.
Proof. exact (MK_COMB (@lem5485164) (@lem5485163)). Qed.
Lemma lem5485166 : term211 = term214.
Proof. exact (MK_COMB (@lem5485165) (@lem5485160)). Qed.
Lemma lem5485167 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5485169 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485170 : term211 = term217.
Proof. exact (@lem5485169 (NUMERAL 0) term144). Qed.
Lemma lem5485171 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485172 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485173 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485172 h1) (fun h1 : term217 = True => @lem5485171)). Qed.
Lemma lem5485174 : term217 = True.
Proof. exact (EQ_MP (@lem5485173) (@lem5485171)). Qed.
Lemma lem5485175 : term211 = True.
Proof. exact (TRANS (@lem5485170) (@lem5485174)). Qed.
Lemma lem5485176 : True = term211.
Proof. exact (SYM (@lem5485175)). Qed.
Lemma lem5485177 : term211.
Proof. exact (EQ_MP (@lem5485176) (@lem0)). Qed.
Lemma lem5485178 : term219.
Proof. exact (@lem5485167 (@lem5485177)). Qed.
Lemma lem5485180 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485181 : term211 = term217.
Proof. exact (@lem5485180 (NUMERAL 0) term144). Qed.
Lemma lem5485182 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485183 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485184 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485183 h1) (fun h1 : term217 = True => @lem5485182)). Qed.
Lemma lem5485185 : term217 = True.
Proof. exact (EQ_MP (@lem5485184) (@lem5485182)). Qed.
Lemma lem5485186 : term211 = True.
Proof. exact (TRANS (@lem5485181) (@lem5485185)). Qed.
Lemma lem5485187 : True = term211.
Proof. exact (SYM (@lem5485186)). Qed.
Lemma lem5485188 : term211.
Proof. exact (EQ_MP (@lem5485187) (@lem0)). Qed.
Lemma lem5485189 : term214 = term220.
Proof. exact (@lem5485178 (@lem5485188)). Qed.
Lemma lem5485191 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485192 : term173 = term174.
Proof. exact (@lem5485191 term144 term144). Qed.
Lemma lem5485193 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485194 : term176 = term144.
Proof. exact (EQ_MP (@lem5485193) (@lem940073)). Qed.
Lemma lem5485195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485196 : term174 = term143.
Proof. exact (MK_COMB (@lem5485195) (@lem5485194)). Qed.
Lemma lem5485197 : term173 = term143.
Proof. exact (TRANS (@lem5485192) (@lem5485196)). Qed.
Lemma lem5485199 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485200 : term222 = term129.
Proof. exact (@lem5485199 term144). Qed.
Lemma lem5485201 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485202 : term223 = term212.
Proof. exact (MK_COMB (@lem5485201) (@lem5485200)). Qed.
Lemma lem5485203 : term220 = term211.
Proof. exact (MK_COMB (@lem5485202) (@lem5485197)). Qed.
Lemma lem5485205 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485206 : term211 = term217.
Proof. exact (@lem5485205 (NUMERAL 0) term144). Qed.
Lemma lem5485207 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485208 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485209 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485208 h1) (fun h1 : term217 = True => @lem5485207)). Qed.
Lemma lem5485210 : term217 = True.
Proof. exact (EQ_MP (@lem5485209) (@lem5485207)). Qed.
Lemma lem5485211 : term211 = True.
Proof. exact (TRANS (@lem5485206) (@lem5485210)). Qed.
Lemma lem5485212 : term220 = True.
Proof. exact (TRANS (@lem5485203) (@lem5485211)). Qed.
Lemma lem5485213 : term214 = True.
Proof. exact (TRANS (@lem5485189) (@lem5485212)). Qed.
Lemma lem5485214 : term211 = True.
Proof. exact (TRANS (@lem5485166) (@lem5485213)). Qed.
Lemma lem5485215 : term210 = True.
Proof. exact (TRANS (@lem5485157) (@lem5485214)). Qed.
Lemma lem5485216 : True = term210.
Proof. exact (SYM (@lem5485215)). Qed.
Lemma lem5485217 : term210.
Proof. exact (EQ_MP (@lem5485216) (@lem0)). Qed.
Lemma lem5485218 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term871 _70608.
Proof. exact (conj (@lem5485217) (@lem5485154 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485220 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5485221 (_70608 : int) : term872 _70608.
Proof. exact (@lem5485220 term143 (term239 _70608)). Qed.
Lemma lem5485222 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term873 _70608.
Proof. exact (@lem5485221 _70608 (@lem5485218 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485223 (_70608 : int) : (term874 _70608) = (term239 _70608).
Proof. exact (@lem1982733 (term239 _70608)). Qed.
Lemma lem5485224 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485225 (_70608 : int) : (term875 _70608) = (term575 _70608).
Proof. exact (MK_COMB (@lem5485224) (@lem5485223 _70608)). Qed.
Lemma lem5485226 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485227 (_70608 : int) : (term873 _70608) = (term576 _70608).
Proof. exact (MK_COMB (@lem5485225 _70608) (@lem5485226)). Qed.
Lemma lem5485228 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term576 _70608.
Proof. exact (EQ_MP (@lem5485227 _70608) (@lem5485222 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485229 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term876 _70607 _70608.
Proof. exact (conj (@lem5485228 _70607 _70606 _70608 h1) (@lem5484943 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485231 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5485232 (_70607 : int) (_70608 : int) : term877 _70607 _70608.
Proof. exact (@lem5485231 (term239 _70608) (term584 _70607 _70608)). Qed.
Lemma lem5485233 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term878 _70607 _70608.
Proof. exact (@lem5485232 _70607 _70608 (@lem5485229 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485234 (_70607 : int) (_70608 : int) : (term879 _70607 _70608) = (term880 _70607 _70608).
Proof. exact (@lem1982757 (term239 _70607) (term239 _70608) (real_of_int _70608)). Qed.
Lemma lem5485235 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5485237 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485238 : term143 = term191.
Proof. exact (@lem5485237 term144). Qed.
Lemma lem5485240 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5485241 : term164 = term165.
Proof. exact (@lem5485240 term144). Qed.
Lemma lem5485242 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485243 : term248 = term249.
Proof. exact (MK_COMB (@lem5485242) (@lem5485241)). Qed.
Lemma lem5485244 : term250 = term251.
Proof. exact (MK_COMB (@lem5485243) (@lem5485238)). Qed.
Lemma lem5485245 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5485247 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485248 : term211 = term217.
Proof. exact (@lem5485247 (NUMERAL 0) term144). Qed.
Lemma lem5485249 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485250 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485251 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485250 h1) (fun h1 : term217 = True => @lem5485249)). Qed.
Lemma lem5485252 : term217 = True.
Proof. exact (EQ_MP (@lem5485251) (@lem5485249)). Qed.
Lemma lem5485253 : term211 = True.
Proof. exact (TRANS (@lem5485248) (@lem5485252)). Qed.
Lemma lem5485254 : True = term211.
Proof. exact (SYM (@lem5485253)). Qed.
Lemma lem5485255 : term211.
Proof. exact (EQ_MP (@lem5485254) (@lem0)). Qed.
Lemma lem5485256 : term253.
Proof. exact (@lem5485245 (@lem5485255)). Qed.
Lemma lem5485258 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485259 : term211 = term217.
Proof. exact (@lem5485258 (NUMERAL 0) term144). Qed.
Lemma lem5485260 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485261 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485262 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485261 h1) (fun h1 : term217 = True => @lem5485260)). Qed.
Lemma lem5485263 : term217 = True.
Proof. exact (EQ_MP (@lem5485262) (@lem5485260)). Qed.
Lemma lem5485264 : term211 = True.
Proof. exact (TRANS (@lem5485259) (@lem5485263)). Qed.
Lemma lem5485265 : True = term211.
Proof. exact (SYM (@lem5485264)). Qed.
Lemma lem5485266 : term211.
Proof. exact (EQ_MP (@lem5485265) (@lem0)). Qed.
Lemma lem5485267 : term254.
Proof. exact (@lem5485256 (@lem5485266)). Qed.
Lemma lem5485269 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485270 : term211 = term217.
Proof. exact (@lem5485269 (NUMERAL 0) term144). Qed.
Lemma lem5485271 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485272 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485273 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485272 h1) (fun h1 : term217 = True => @lem5485271)). Qed.
Lemma lem5485274 : term217 = True.
Proof. exact (EQ_MP (@lem5485273) (@lem5485271)). Qed.
Lemma lem5485275 : term211 = True.
Proof. exact (TRANS (@lem5485270) (@lem5485274)). Qed.
Lemma lem5485276 : True = term211.
Proof. exact (SYM (@lem5485275)). Qed.
Lemma lem5485277 : term211.
Proof. exact (EQ_MP (@lem5485276) (@lem0)). Qed.
Lemma lem5485278 : term255.
Proof. exact (@lem5485267 (@lem5485277)). Qed.
Lemma lem5485280 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485281 : term173 = term174.
Proof. exact (@lem5485280 term144 term144). Qed.
Lemma lem5485282 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485283 : term176 = term144.
Proof. exact (EQ_MP (@lem5485282) (@lem940073)). Qed.
Lemma lem5485284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485285 : term174 = term143.
Proof. exact (MK_COMB (@lem5485284) (@lem5485283)). Qed.
Lemma lem5485286 : term173 = term143.
Proof. exact (TRANS (@lem5485281) (@lem5485285)). Qed.
Lemma lem5485288 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5485289 : term192 = term197.
Proof. exact (@lem5485288 term144 term144). Qed.
Lemma lem5485290 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485291 : term176 = term144.
Proof. exact (EQ_MP (@lem5485290) (@lem940073)). Qed.
Lemma lem5485292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485293 : term174 = term143.
Proof. exact (MK_COMB (@lem5485292) (@lem5485291)). Qed.
Lemma lem5485294 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5485295 : term197 = term164.
Proof. exact (MK_COMB (@lem5485294) (@lem5485293)). Qed.
Lemma lem5485296 : term192 = term164.
Proof. exact (TRANS (@lem5485289) (@lem5485295)). Qed.
Lemma lem5485297 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485298 : term256 = term248.
Proof. exact (MK_COMB (@lem5485297) (@lem5485296)). Qed.
Lemma lem5485299 : term257 = term250.
Proof. exact (MK_COMB (@lem5485298) (@lem5485286)). Qed.
Lemma lem5485301 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5485302 : term250 = term129.
Proof. exact (@lem5485301 term144). Qed.
Lemma lem5485303 : term257 = term129.
Proof. exact (TRANS (@lem5485299) (@lem5485302)). Qed.
Lemma lem5485304 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485305 : term259 = term260.
Proof. exact (MK_COMB (@lem5485304) (@lem5485303)). Qed.
Lemma lem5485306 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5485307 : term261 = term222.
Proof. exact (MK_COMB (@lem5485305) (@lem5485306)). Qed.
Lemma lem5485309 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485310 : term222 = term129.
Proof. exact (@lem5485309 term144). Qed.
Lemma lem5485311 : term261 = term129.
Proof. exact (TRANS (@lem5485307) (@lem5485310)). Qed.
Lemma lem5485313 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485314 : term173 = term174.
Proof. exact (@lem5485313 term144 term144). Qed.
Lemma lem5485315 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485316 : term176 = term144.
Proof. exact (EQ_MP (@lem5485315) (@lem940073)). Qed.
Lemma lem5485317 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485318 : term174 = term143.
Proof. exact (MK_COMB (@lem5485317) (@lem5485316)). Qed.
Lemma lem5485319 : term173 = term143.
Proof. exact (TRANS (@lem5485314) (@lem5485318)). Qed.
Lemma lem5485320 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5485321 : term262 = term222.
Proof. exact (MK_COMB (@lem5485320) (@lem5485319)). Qed.
Lemma lem5485323 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485324 : term222 = term129.
Proof. exact (@lem5485323 term144). Qed.
Lemma lem5485325 : term262 = term129.
Proof. exact (TRANS (@lem5485321) (@lem5485324)). Qed.
Lemma lem5485326 : term129 = term262.
Proof. exact (SYM (@lem5485325)). Qed.
Lemma lem5485327 : term261 = term262.
Proof. exact (TRANS (@lem5485311) (@lem5485326)). Qed.
Lemma lem5485328 : term251 = term161.
Proof. exact (@lem5485278 (@lem5485327)). Qed.
Lemma lem5485329 : term250 = term161.
Proof. exact (TRANS (@lem5485244) (@lem5485328)). Qed.
Lemma lem5485331 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5485332 : term161 = term129.
Proof. exact (@lem5485331 term129). Qed.
Lemma lem5485333 : term250 = term129.
Proof. exact (TRANS (@lem5485329) (@lem5485332)). Qed.
Lemma lem5485334 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485335 : term263 = term260.
Proof. exact (MK_COMB (@lem5485334) (@lem5485333)). Qed.
Lemma lem5485336 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5485337 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5485335) (@lem5485336 _70608)). Qed.
Lemma lem5485338 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5485235 _70608) (@lem5485337 _70608)). Qed.
Lemma lem5485339 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5485340 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5485338 _70608) (@lem5485339 _70608)). Qed.
Lemma lem5485341 (_70607 : int) : (term200 _70607) = (term200 _70607).
Proof. exact (eq_refl (term200 _70607)). Qed.
Lemma lem5485342 (_70608 : int) (_70607 : int) : (term880 _70607 _70608) = (term573 _70607).
Proof. exact (MK_COMB (@lem5485341 _70607) (@lem5485340 _70608)). Qed.
Lemma lem5485343 (_70608 : int) (_70607 : int) : (term879 _70607 _70608) = (term573 _70607).
Proof. exact (TRANS (@lem5485234 _70607 _70608) (@lem5485342 _70608 _70607)). Qed.
Lemma lem5485344 (_70607 : int) : (term573 _70607) = (term239 _70607).
Proof. exact (@lem1982723 (term239 _70607)). Qed.
Lemma lem5485345 (_70608 : int) (_70607 : int) : (term879 _70607 _70608) = (term239 _70607).
Proof. exact (TRANS (@lem5485343 _70608 _70607) (@lem5485344 _70607)). Qed.
Lemma lem5485346 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485347 (_70608 : int) (_70607 : int) : (term881 _70607 _70608) = (term575 _70607).
Proof. exact (MK_COMB (@lem5485346) (@lem5485345 _70608 _70607)). Qed.
Lemma lem5485348 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485349 (_70608 : int) (_70607 : int) : (term878 _70607 _70608) = (term576 _70607).
Proof. exact (MK_COMB (@lem5485347 _70608 _70607) (@lem5485348)). Qed.
Lemma lem5485350 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term576 _70607.
Proof. exact (EQ_MP (@lem5485349 _70608 _70607) (@lem5485233 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485352 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5485353 : term210 = term211.
Proof. exact (@lem5485352 term129 term143). Qed.
Lemma lem5485355 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485356 : term143 = term191.
Proof. exact (@lem5485355 term144). Qed.
Lemma lem5485358 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485359 : term129 = term161.
Proof. exact (@lem5485358 (NUMERAL 0)). Qed.
Lemma lem5485360 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485361 : term212 = term213.
Proof. exact (MK_COMB (@lem5485360) (@lem5485359)). Qed.
Lemma lem5485362 : term211 = term214.
Proof. exact (MK_COMB (@lem5485361) (@lem5485356)). Qed.
Lemma lem5485363 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5485365 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485366 : term211 = term217.
Proof. exact (@lem5485365 (NUMERAL 0) term144). Qed.
Lemma lem5485367 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485368 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485369 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485368 h1) (fun h1 : term217 = True => @lem5485367)). Qed.
Lemma lem5485370 : term217 = True.
Proof. exact (EQ_MP (@lem5485369) (@lem5485367)). Qed.
Lemma lem5485371 : term211 = True.
Proof. exact (TRANS (@lem5485366) (@lem5485370)). Qed.
Lemma lem5485372 : True = term211.
Proof. exact (SYM (@lem5485371)). Qed.
Lemma lem5485373 : term211.
Proof. exact (EQ_MP (@lem5485372) (@lem0)). Qed.
Lemma lem5485374 : term219.
Proof. exact (@lem5485363 (@lem5485373)). Qed.
Lemma lem5485376 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485377 : term211 = term217.
Proof. exact (@lem5485376 (NUMERAL 0) term144). Qed.
Lemma lem5485378 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485379 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485380 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485379 h1) (fun h1 : term217 = True => @lem5485378)). Qed.
Lemma lem5485381 : term217 = True.
Proof. exact (EQ_MP (@lem5485380) (@lem5485378)). Qed.
Lemma lem5485382 : term211 = True.
Proof. exact (TRANS (@lem5485377) (@lem5485381)). Qed.
Lemma lem5485383 : True = term211.
Proof. exact (SYM (@lem5485382)). Qed.
Lemma lem5485384 : term211.
Proof. exact (EQ_MP (@lem5485383) (@lem0)). Qed.
Lemma lem5485385 : term214 = term220.
Proof. exact (@lem5485374 (@lem5485384)). Qed.
Lemma lem5485387 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485388 : term173 = term174.
Proof. exact (@lem5485387 term144 term144). Qed.
Lemma lem5485389 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485390 : term176 = term144.
Proof. exact (EQ_MP (@lem5485389) (@lem940073)). Qed.
Lemma lem5485391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485392 : term174 = term143.
Proof. exact (MK_COMB (@lem5485391) (@lem5485390)). Qed.
Lemma lem5485393 : term173 = term143.
Proof. exact (TRANS (@lem5485388) (@lem5485392)). Qed.
Lemma lem5485395 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485396 : term222 = term129.
Proof. exact (@lem5485395 term144). Qed.
Lemma lem5485397 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485398 : term223 = term212.
Proof. exact (MK_COMB (@lem5485397) (@lem5485396)). Qed.
Lemma lem5485399 : term220 = term211.
Proof. exact (MK_COMB (@lem5485398) (@lem5485393)). Qed.
Lemma lem5485401 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485402 : term211 = term217.
Proof. exact (@lem5485401 (NUMERAL 0) term144). Qed.
Lemma lem5485403 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485404 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485405 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485404 h1) (fun h1 : term217 = True => @lem5485403)). Qed.
Lemma lem5485406 : term217 = True.
Proof. exact (EQ_MP (@lem5485405) (@lem5485403)). Qed.
Lemma lem5485407 : term211 = True.
Proof. exact (TRANS (@lem5485402) (@lem5485406)). Qed.
Lemma lem5485408 : term220 = True.
Proof. exact (TRANS (@lem5485399) (@lem5485407)). Qed.
Lemma lem5485409 : term214 = True.
Proof. exact (TRANS (@lem5485385) (@lem5485408)). Qed.
Lemma lem5485410 : term211 = True.
Proof. exact (TRANS (@lem5485362) (@lem5485409)). Qed.
Lemma lem5485411 : term210 = True.
Proof. exact (TRANS (@lem5485353) (@lem5485410)). Qed.
Lemma lem5485412 : True = term210.
Proof. exact (SYM (@lem5485411)). Qed.
Lemma lem5485413 : term210.
Proof. exact (EQ_MP (@lem5485412) (@lem0)). Qed.
Lemma lem5485414 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term871 _70607.
Proof. exact (conj (@lem5485413) (@lem5485350 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485416 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5485417 (_70607 : int) : term872 _70607.
Proof. exact (@lem5485416 term143 (term239 _70607)). Qed.
Lemma lem5485418 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term873 _70607.
Proof. exact (@lem5485417 _70607 (@lem5485414 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485419 (_70607 : int) : (term874 _70607) = (term239 _70607).
Proof. exact (@lem1982733 (term239 _70607)). Qed.
Lemma lem5485420 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485421 (_70607 : int) : (term875 _70607) = (term575 _70607).
Proof. exact (MK_COMB (@lem5485420) (@lem5485419 _70607)). Qed.
Lemma lem5485422 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485423 (_70607 : int) : (term873 _70607) = (term576 _70607).
Proof. exact (MK_COMB (@lem5485421 _70607) (@lem5485422)). Qed.
Lemma lem5485424 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term576 _70607.
Proof. exact (EQ_MP (@lem5485423 _70607) (@lem5485418 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485425 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term882 _70607.
Proof. exact (conj (@lem5485424 _70607 _70606 _70608 h1) (@lem5484869 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485427 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5485428 (_70607 : int) : term883 _70607.
Proof. exact (@lem5485427 (term239 _70607) (term546 _70607)). Qed.
Lemma lem5485429 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term884 _70607.
Proof. exact (@lem5485428 _70607 (@lem5485425 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485430 (_70607 : int) : (term854 _70607) = (term281 _70607).
Proof. exact (@lem1982763 (term239 _70607) (real_of_int _70607) term164). Qed.
Lemma lem5485431 (_70607 : int) : (term246 _70607) = (term247 _70607).
Proof. exact (@lem1982713 term164 (real_of_int _70607)). Qed.
Lemma lem5485433 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485434 : term143 = term191.
Proof. exact (@lem5485433 term144). Qed.
Lemma lem5485436 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5485437 : term164 = term165.
Proof. exact (@lem5485436 term144). Qed.
Lemma lem5485438 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485439 : term248 = term249.
Proof. exact (MK_COMB (@lem5485438) (@lem5485437)). Qed.
Lemma lem5485440 : term250 = term251.
Proof. exact (MK_COMB (@lem5485439) (@lem5485434)). Qed.
Lemma lem5485441 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5485443 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485444 : term211 = term217.
Proof. exact (@lem5485443 (NUMERAL 0) term144). Qed.
Lemma lem5485445 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485446 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485447 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485446 h1) (fun h1 : term217 = True => @lem5485445)). Qed.
Lemma lem5485448 : term217 = True.
Proof. exact (EQ_MP (@lem5485447) (@lem5485445)). Qed.
Lemma lem5485449 : term211 = True.
Proof. exact (TRANS (@lem5485444) (@lem5485448)). Qed.
Lemma lem5485450 : True = term211.
Proof. exact (SYM (@lem5485449)). Qed.
Lemma lem5485451 : term211.
Proof. exact (EQ_MP (@lem5485450) (@lem0)). Qed.
Lemma lem5485452 : term253.
Proof. exact (@lem5485441 (@lem5485451)). Qed.
Lemma lem5485454 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485455 : term211 = term217.
Proof. exact (@lem5485454 (NUMERAL 0) term144). Qed.
Lemma lem5485456 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485457 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485458 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485457 h1) (fun h1 : term217 = True => @lem5485456)). Qed.
Lemma lem5485459 : term217 = True.
Proof. exact (EQ_MP (@lem5485458) (@lem5485456)). Qed.
Lemma lem5485460 : term211 = True.
Proof. exact (TRANS (@lem5485455) (@lem5485459)). Qed.
Lemma lem5485461 : True = term211.
Proof. exact (SYM (@lem5485460)). Qed.
Lemma lem5485462 : term211.
Proof. exact (EQ_MP (@lem5485461) (@lem0)). Qed.
Lemma lem5485463 : term254.
Proof. exact (@lem5485452 (@lem5485462)). Qed.
Lemma lem5485465 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485466 : term211 = term217.
Proof. exact (@lem5485465 (NUMERAL 0) term144). Qed.
Lemma lem5485467 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485468 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485469 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485468 h1) (fun h1 : term217 = True => @lem5485467)). Qed.
Lemma lem5485470 : term217 = True.
Proof. exact (EQ_MP (@lem5485469) (@lem5485467)). Qed.
Lemma lem5485471 : term211 = True.
Proof. exact (TRANS (@lem5485466) (@lem5485470)). Qed.
Lemma lem5485472 : True = term211.
Proof. exact (SYM (@lem5485471)). Qed.
Lemma lem5485473 : term211.
Proof. exact (EQ_MP (@lem5485472) (@lem0)). Qed.
Lemma lem5485474 : term255.
Proof. exact (@lem5485463 (@lem5485473)). Qed.
Lemma lem5485476 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485477 : term173 = term174.
Proof. exact (@lem5485476 term144 term144). Qed.
Lemma lem5485478 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485479 : term176 = term144.
Proof. exact (EQ_MP (@lem5485478) (@lem940073)). Qed.
Lemma lem5485480 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485481 : term174 = term143.
Proof. exact (MK_COMB (@lem5485480) (@lem5485479)). Qed.
Lemma lem5485482 : term173 = term143.
Proof. exact (TRANS (@lem5485477) (@lem5485481)). Qed.
Lemma lem5485484 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5485485 : term192 = term197.
Proof. exact (@lem5485484 term144 term144). Qed.
Lemma lem5485486 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485487 : term176 = term144.
Proof. exact (EQ_MP (@lem5485486) (@lem940073)). Qed.
Lemma lem5485488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485489 : term174 = term143.
Proof. exact (MK_COMB (@lem5485488) (@lem5485487)). Qed.
Lemma lem5485490 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5485491 : term197 = term164.
Proof. exact (MK_COMB (@lem5485490) (@lem5485489)). Qed.
Lemma lem5485492 : term192 = term164.
Proof. exact (TRANS (@lem5485485) (@lem5485491)). Qed.
Lemma lem5485493 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485494 : term256 = term248.
Proof. exact (MK_COMB (@lem5485493) (@lem5485492)). Qed.
Lemma lem5485495 : term257 = term250.
Proof. exact (MK_COMB (@lem5485494) (@lem5485482)). Qed.
Lemma lem5485497 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5485498 : term250 = term129.
Proof. exact (@lem5485497 term144). Qed.
Lemma lem5485499 : term257 = term129.
Proof. exact (TRANS (@lem5485495) (@lem5485498)). Qed.
Lemma lem5485500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485501 : term259 = term260.
Proof. exact (MK_COMB (@lem5485500) (@lem5485499)). Qed.
Lemma lem5485502 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5485503 : term261 = term222.
Proof. exact (MK_COMB (@lem5485501) (@lem5485502)). Qed.
Lemma lem5485505 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485506 : term222 = term129.
Proof. exact (@lem5485505 term144). Qed.
Lemma lem5485507 : term261 = term129.
Proof. exact (TRANS (@lem5485503) (@lem5485506)). Qed.
Lemma lem5485509 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485510 : term173 = term174.
Proof. exact (@lem5485509 term144 term144). Qed.
Lemma lem5485511 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485512 : term176 = term144.
Proof. exact (EQ_MP (@lem5485511) (@lem940073)). Qed.
Lemma lem5485513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485514 : term174 = term143.
Proof. exact (MK_COMB (@lem5485513) (@lem5485512)). Qed.
Lemma lem5485515 : term173 = term143.
Proof. exact (TRANS (@lem5485510) (@lem5485514)). Qed.
Lemma lem5485516 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5485517 : term262 = term222.
Proof. exact (MK_COMB (@lem5485516) (@lem5485515)). Qed.
Lemma lem5485519 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485520 : term222 = term129.
Proof. exact (@lem5485519 term144). Qed.
Lemma lem5485521 : term262 = term129.
Proof. exact (TRANS (@lem5485517) (@lem5485520)). Qed.
Lemma lem5485522 : term129 = term262.
Proof. exact (SYM (@lem5485521)). Qed.
Lemma lem5485523 : term261 = term262.
Proof. exact (TRANS (@lem5485507) (@lem5485522)). Qed.
Lemma lem5485524 : term251 = term161.
Proof. exact (@lem5485474 (@lem5485523)). Qed.
Lemma lem5485525 : term250 = term161.
Proof. exact (TRANS (@lem5485440) (@lem5485524)). Qed.
Lemma lem5485527 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5485528 : term161 = term129.
Proof. exact (@lem5485527 term129). Qed.
Lemma lem5485529 : term250 = term129.
Proof. exact (TRANS (@lem5485525) (@lem5485528)). Qed.
Lemma lem5485530 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485531 : term263 = term260.
Proof. exact (MK_COMB (@lem5485530) (@lem5485529)). Qed.
Lemma lem5485532 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5485533 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5485531) (@lem5485532 _70607)). Qed.
Lemma lem5485534 (_70607 : int) : (term246 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5485431 _70607) (@lem5485533 _70607)). Qed.
Lemma lem5485535 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5485536 (_70607 : int) : (term246 _70607) = term129.
Proof. exact (TRANS (@lem5485534 _70607) (@lem5485535 _70607)). Qed.
Lemma lem5485537 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485538 (_70607 : int) : (term265 _70607) = term266.
Proof. exact (MK_COMB (@lem5485537) (@lem5485536 _70607)). Qed.
Lemma lem5485539 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5485540 (_70607 : int) : (term281 _70607) = term282.
Proof. exact (MK_COMB (@lem5485538 _70607) (@lem5485539)). Qed.
Lemma lem5485541 (_70607 : int) : (term854 _70607) = term282.
Proof. exact (TRANS (@lem5485430 _70607) (@lem5485540 _70607)). Qed.
Lemma lem5485542 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5485543 (_70607 : int) : (term854 _70607) = term164.
Proof. exact (TRANS (@lem5485541 _70607) (@lem5485542)). Qed.
Lemma lem5485544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485545 (_70607 : int) : (term885 _70607) = term284.
Proof. exact (MK_COMB (@lem5485544) (@lem5485543 _70607)). Qed.
Lemma lem5485546 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485547 (_70607 : int) : (term884 _70607) = term285.
Proof. exact (MK_COMB (@lem5485545 _70607) (@lem5485546)). Qed.
Lemma lem5485548 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : term285.
Proof. exact (EQ_MP (@lem5485547 _70607) (@lem5485429 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485550 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5485551 : term285 = term286.
Proof. exact (@lem5485550 term129 term164). Qed.
Lemma lem5485553 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5485554 : term164 = term165.
Proof. exact (@lem5485553 term144). Qed.
Lemma lem5485556 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485557 : term129 = term161.
Proof. exact (@lem5485556 (NUMERAL 0)). Qed.
Lemma lem5485558 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5485559 : term131 = term287.
Proof. exact (MK_COMB (@lem5485558) (@lem5485557)). Qed.
Lemma lem5485560 : term286 = term288.
Proof. exact (MK_COMB (@lem5485559) (@lem5485554)). Qed.
Lemma lem5485561 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5485563 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485564 : term211 = term217.
Proof. exact (@lem5485563 (NUMERAL 0) term144). Qed.
Lemma lem5485565 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485566 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485567 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485566 h1) (fun h1 : term217 = True => @lem5485565)). Qed.
Lemma lem5485568 : term217 = True.
Proof. exact (EQ_MP (@lem5485567) (@lem5485565)). Qed.
Lemma lem5485569 : term211 = True.
Proof. exact (TRANS (@lem5485564) (@lem5485568)). Qed.
Lemma lem5485570 : True = term211.
Proof. exact (SYM (@lem5485569)). Qed.
Lemma lem5485571 : term211.
Proof. exact (EQ_MP (@lem5485570) (@lem0)). Qed.
Lemma lem5485572 : term290.
Proof. exact (@lem5485561 (@lem5485571)). Qed.
Lemma lem5485574 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485575 : term211 = term217.
Proof. exact (@lem5485574 (NUMERAL 0) term144). Qed.
Lemma lem5485576 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485577 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485578 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485577 h1) (fun h1 : term217 = True => @lem5485576)). Qed.
Lemma lem5485579 : term217 = True.
Proof. exact (EQ_MP (@lem5485578) (@lem5485576)). Qed.
Lemma lem5485580 : term211 = True.
Proof. exact (TRANS (@lem5485575) (@lem5485579)). Qed.
Lemma lem5485581 : True = term211.
Proof. exact (SYM (@lem5485580)). Qed.
Lemma lem5485582 : term211.
Proof. exact (EQ_MP (@lem5485581) (@lem0)). Qed.
Lemma lem5485583 : term288 = term291.
Proof. exact (@lem5485572 (@lem5485582)). Qed.
Lemma lem5485585 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5485586 : term192 = term197.
Proof. exact (@lem5485585 term144 term144). Qed.
Lemma lem5485587 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485588 : term176 = term144.
Proof. exact (EQ_MP (@lem5485587) (@lem940073)). Qed.
Lemma lem5485589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485590 : term174 = term143.
Proof. exact (MK_COMB (@lem5485589) (@lem5485588)). Qed.
Lemma lem5485591 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5485592 : term197 = term164.
Proof. exact (MK_COMB (@lem5485591) (@lem5485590)). Qed.
Lemma lem5485593 : term192 = term164.
Proof. exact (TRANS (@lem5485586) (@lem5485592)). Qed.
Lemma lem5485595 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485596 : term222 = term129.
Proof. exact (@lem5485595 term144). Qed.
Lemma lem5485597 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5485598 : term292 = term131.
Proof. exact (MK_COMB (@lem5485597) (@lem5485596)). Qed.
Lemma lem5485599 : term291 = term286.
Proof. exact (MK_COMB (@lem5485598) (@lem5485593)). Qed.
Lemma lem5485601 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5485602 : term286 = term295.
Proof. exact (@lem5485601 (NUMERAL 0) term144). Qed.
Lemma lem5485603 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485604 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5485605 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485604 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5485603)). Qed.
Lemma lem5485606 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5485605) (@lem5485603)). Qed.
Lemma lem5485607 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5485608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5485609 : term296 = (and True).
Proof. exact (MK_COMB (@lem5485608) (@lem5485607)). Qed.
Lemma lem5485610 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5485609) (@lem5485606)). Qed.
Lemma lem5485612 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5485613 : term295 = False.
Proof. exact (TRANS (@lem5485610) (@lem5485612)). Qed.
Lemma lem5485614 : term286 = False.
Proof. exact (TRANS (@lem5485602) (@lem5485613)). Qed.
Lemma lem5485615 : term291 = False.
Proof. exact (TRANS (@lem5485599) (@lem5485614)). Qed.
Lemma lem5485616 : term288 = False.
Proof. exact (TRANS (@lem5485583) (@lem5485615)). Qed.
Lemma lem5485617 : term286 = False.
Proof. exact (TRANS (@lem5485560) (@lem5485616)). Qed.
Lemma lem5485618 : term285 = False.
Proof. exact (TRANS (@lem5485551) (@lem5485617)). Qed.
Lemma lem5485619 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term858 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5485618) (@lem5485548 _70607 _70606 _70608 h1)). Qed.
Lemma lem5485620 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term804 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5484418 _70607 _70606 _70608 h1) (fun h0 : term857 _70607 _70606 _70608 => @lem5484778 _70607 _70606 _70608 h0) (fun h0 : term858 _70607 _70606 _70608 => @lem5485619 _70607 _70606 _70608 h0)). Qed.
Lemma lem5485621 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term813 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5483043 _70607 _70606 _70608 h1) (fun h0 : term808 _70607 _70606 _70608 => @lem5484417 _70607 _70606 _70608 h0) (fun h0 : term804 _70607 _70606 _70608 => @lem5485620 _70607 _70606 _70608 h0)). Qed.
Lemma lem5485622 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term800 _70607 _70606 _70608) : term800 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5485623 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term797 _70606 _70607 _70608) : term797 _70606 _70607 _70608.
Proof. exact (h1). Qed.
Lemma lem5485624 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term792 _70606 _70607 _70608) : term792 _70606 _70607 _70608.
Proof. exact (h1). Qed.
Lemma lem5485625 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term886 _70606 _70607 _70608.
Proof. exact (h1). Qed.
Lemma lem5485626 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term793 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485625 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485628 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term744 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485626 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485630 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term695 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485628 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485631 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term184 _70608.
Proof. exact (proj1 (@lem5485628 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485632 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term644 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485630 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485634 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term613 _70607 _70608.
Proof. exact (proj2 (@lem5485632 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485636 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term270 _70608.
Proof. exact (proj2 (@lem5485634 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485639 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5485640 : term210 = term211.
Proof. exact (@lem5485639 term129 term143). Qed.
Lemma lem5485642 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485643 : term143 = term191.
Proof. exact (@lem5485642 term144). Qed.
Lemma lem5485645 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485646 : term129 = term161.
Proof. exact (@lem5485645 (NUMERAL 0)). Qed.
Lemma lem5485647 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485648 : term212 = term213.
Proof. exact (MK_COMB (@lem5485647) (@lem5485646)). Qed.
Lemma lem5485649 : term211 = term214.
Proof. exact (MK_COMB (@lem5485648) (@lem5485643)). Qed.
Lemma lem5485650 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5485652 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485653 : term211 = term217.
Proof. exact (@lem5485652 (NUMERAL 0) term144). Qed.
Lemma lem5485654 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485655 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485656 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485655 h1) (fun h1 : term217 = True => @lem5485654)). Qed.
Lemma lem5485657 : term217 = True.
Proof. exact (EQ_MP (@lem5485656) (@lem5485654)). Qed.
Lemma lem5485658 : term211 = True.
Proof. exact (TRANS (@lem5485653) (@lem5485657)). Qed.
Lemma lem5485659 : True = term211.
Proof. exact (SYM (@lem5485658)). Qed.
Lemma lem5485660 : term211.
Proof. exact (EQ_MP (@lem5485659) (@lem0)). Qed.
Lemma lem5485661 : term219.
Proof. exact (@lem5485650 (@lem5485660)). Qed.
Lemma lem5485663 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485664 : term211 = term217.
Proof. exact (@lem5485663 (NUMERAL 0) term144). Qed.
Lemma lem5485665 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485666 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485667 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485666 h1) (fun h1 : term217 = True => @lem5485665)). Qed.
Lemma lem5485668 : term217 = True.
Proof. exact (EQ_MP (@lem5485667) (@lem5485665)). Qed.
Lemma lem5485669 : term211 = True.
Proof. exact (TRANS (@lem5485664) (@lem5485668)). Qed.
Lemma lem5485670 : True = term211.
Proof. exact (SYM (@lem5485669)). Qed.
Lemma lem5485671 : term211.
Proof. exact (EQ_MP (@lem5485670) (@lem0)). Qed.
Lemma lem5485672 : term214 = term220.
Proof. exact (@lem5485661 (@lem5485671)). Qed.
Lemma lem5485674 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485675 : term173 = term174.
Proof. exact (@lem5485674 term144 term144). Qed.
Lemma lem5485676 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485677 : term176 = term144.
Proof. exact (EQ_MP (@lem5485676) (@lem940073)). Qed.
Lemma lem5485678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485679 : term174 = term143.
Proof. exact (MK_COMB (@lem5485678) (@lem5485677)). Qed.
Lemma lem5485680 : term173 = term143.
Proof. exact (TRANS (@lem5485675) (@lem5485679)). Qed.
Lemma lem5485682 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485683 : term222 = term129.
Proof. exact (@lem5485682 term144). Qed.
Lemma lem5485684 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485685 : term223 = term212.
Proof. exact (MK_COMB (@lem5485684) (@lem5485683)). Qed.
Lemma lem5485686 : term220 = term211.
Proof. exact (MK_COMB (@lem5485685) (@lem5485680)). Qed.
Lemma lem5485688 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485689 : term211 = term217.
Proof. exact (@lem5485688 (NUMERAL 0) term144). Qed.
Lemma lem5485690 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485691 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485692 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485691 h1) (fun h1 : term217 = True => @lem5485690)). Qed.
Lemma lem5485693 : term217 = True.
Proof. exact (EQ_MP (@lem5485692) (@lem5485690)). Qed.
Lemma lem5485694 : term211 = True.
Proof. exact (TRANS (@lem5485689) (@lem5485693)). Qed.
Lemma lem5485695 : term220 = True.
Proof. exact (TRANS (@lem5485686) (@lem5485694)). Qed.
Lemma lem5485696 : term214 = True.
Proof. exact (TRANS (@lem5485672) (@lem5485695)). Qed.
Lemma lem5485697 : term211 = True.
Proof. exact (TRANS (@lem5485649) (@lem5485696)). Qed.
Lemma lem5485698 : term210 = True.
Proof. exact (TRANS (@lem5485640) (@lem5485697)). Qed.
Lemma lem5485699 : True = term210.
Proof. exact (SYM (@lem5485698)). Qed.
Lemma lem5485700 : term210.
Proof. exact (EQ_MP (@lem5485699) (@lem0)). Qed.
Lemma lem5485701 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term224 _70608.
Proof. exact (conj (@lem5485700) (@lem5485631 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485703 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5485704 (_70608 : int) : term226 _70608.
Proof. exact (@lem5485703 term143 (real_of_int _70608)). Qed.
Lemma lem5485705 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term227 _70608.
Proof. exact (@lem5485704 _70608 (@lem5485701 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485706 (_70608 : int) : (term228 _70608) = (real_of_int _70608).
Proof. exact (@lem1982733 (real_of_int _70608)). Qed.
Lemma lem5485707 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485708 (_70608 : int) : (term229 _70608) = (term183 _70608).
Proof. exact (MK_COMB (@lem5485707) (@lem5485706 _70608)). Qed.
Lemma lem5485709 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485710 (_70608 : int) : (term227 _70608) = (term184 _70608).
Proof. exact (MK_COMB (@lem5485708 _70608) (@lem5485709)). Qed.
Lemma lem5485711 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term184 _70608.
Proof. exact (EQ_MP (@lem5485710 _70608) (@lem5485705 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485713 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5485714 : term210 = term211.
Proof. exact (@lem5485713 term129 term143). Qed.
Lemma lem5485716 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485717 : term143 = term191.
Proof. exact (@lem5485716 term144). Qed.
Lemma lem5485719 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485720 : term129 = term161.
Proof. exact (@lem5485719 (NUMERAL 0)). Qed.
Lemma lem5485721 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485722 : term212 = term213.
Proof. exact (MK_COMB (@lem5485721) (@lem5485720)). Qed.
Lemma lem5485723 : term211 = term214.
Proof. exact (MK_COMB (@lem5485722) (@lem5485717)). Qed.
Lemma lem5485724 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5485726 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485727 : term211 = term217.
Proof. exact (@lem5485726 (NUMERAL 0) term144). Qed.
Lemma lem5485728 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485729 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485730 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485729 h1) (fun h1 : term217 = True => @lem5485728)). Qed.
Lemma lem5485731 : term217 = True.
Proof. exact (EQ_MP (@lem5485730) (@lem5485728)). Qed.
Lemma lem5485732 : term211 = True.
Proof. exact (TRANS (@lem5485727) (@lem5485731)). Qed.
Lemma lem5485733 : True = term211.
Proof. exact (SYM (@lem5485732)). Qed.
Lemma lem5485734 : term211.
Proof. exact (EQ_MP (@lem5485733) (@lem0)). Qed.
Lemma lem5485735 : term219.
Proof. exact (@lem5485724 (@lem5485734)). Qed.
Lemma lem5485737 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485738 : term211 = term217.
Proof. exact (@lem5485737 (NUMERAL 0) term144). Qed.
Lemma lem5485739 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485740 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485741 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485740 h1) (fun h1 : term217 = True => @lem5485739)). Qed.
Lemma lem5485742 : term217 = True.
Proof. exact (EQ_MP (@lem5485741) (@lem5485739)). Qed.
Lemma lem5485743 : term211 = True.
Proof. exact (TRANS (@lem5485738) (@lem5485742)). Qed.
Lemma lem5485744 : True = term211.
Proof. exact (SYM (@lem5485743)). Qed.
Lemma lem5485745 : term211.
Proof. exact (EQ_MP (@lem5485744) (@lem0)). Qed.
Lemma lem5485746 : term214 = term220.
Proof. exact (@lem5485735 (@lem5485745)). Qed.
Lemma lem5485748 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485749 : term173 = term174.
Proof. exact (@lem5485748 term144 term144). Qed.
Lemma lem5485750 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485751 : term176 = term144.
Proof. exact (EQ_MP (@lem5485750) (@lem940073)). Qed.
Lemma lem5485752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485753 : term174 = term143.
Proof. exact (MK_COMB (@lem5485752) (@lem5485751)). Qed.
Lemma lem5485754 : term173 = term143.
Proof. exact (TRANS (@lem5485749) (@lem5485753)). Qed.
Lemma lem5485756 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485757 : term222 = term129.
Proof. exact (@lem5485756 term144). Qed.
Lemma lem5485758 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5485759 : term223 = term212.
Proof. exact (MK_COMB (@lem5485758) (@lem5485757)). Qed.
Lemma lem5485760 : term220 = term211.
Proof. exact (MK_COMB (@lem5485759) (@lem5485754)). Qed.
Lemma lem5485762 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485763 : term211 = term217.
Proof. exact (@lem5485762 (NUMERAL 0) term144). Qed.
Lemma lem5485764 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485765 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485766 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485765 h1) (fun h1 : term217 = True => @lem5485764)). Qed.
Lemma lem5485767 : term217 = True.
Proof. exact (EQ_MP (@lem5485766) (@lem5485764)). Qed.
Lemma lem5485768 : term211 = True.
Proof. exact (TRANS (@lem5485763) (@lem5485767)). Qed.
Lemma lem5485769 : term220 = True.
Proof. exact (TRANS (@lem5485760) (@lem5485768)). Qed.
Lemma lem5485770 : term214 = True.
Proof. exact (TRANS (@lem5485746) (@lem5485769)). Qed.
Lemma lem5485771 : term211 = True.
Proof. exact (TRANS (@lem5485723) (@lem5485770)). Qed.
Lemma lem5485772 : term210 = True.
Proof. exact (TRANS (@lem5485714) (@lem5485771)). Qed.
Lemma lem5485773 : True = term210.
Proof. exact (SYM (@lem5485772)). Qed.
Lemma lem5485774 : term210.
Proof. exact (EQ_MP (@lem5485773) (@lem0)). Qed.
Lemma lem5485775 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term271 _70608.
Proof. exact (conj (@lem5485774) (@lem5485636 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485777 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5485778 (_70608 : int) : term272 _70608.
Proof. exact (@lem5485777 term143 (term201 _70608)). Qed.
Lemma lem5485779 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term273 _70608.
Proof. exact (@lem5485778 _70608 (@lem5485775 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485780 (_70608 : int) : (term274 _70608) = (term201 _70608).
Proof. exact (@lem1982733 (term201 _70608)). Qed.
Lemma lem5485781 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485782 (_70608 : int) : (term275 _70608) = (term269 _70608).
Proof. exact (MK_COMB (@lem5485781) (@lem5485780 _70608)). Qed.
Lemma lem5485783 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485784 (_70608 : int) : (term273 _70608) = (term270 _70608).
Proof. exact (MK_COMB (@lem5485782 _70608) (@lem5485783)). Qed.
Lemma lem5485785 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term270 _70608.
Proof. exact (EQ_MP (@lem5485784 _70608) (@lem5485779 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485786 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term276 _70608.
Proof. exact (conj (@lem5485785 _70606 _70607 _70608 h1) (@lem5485711 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485788 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5485789 (_70608 : int) : term278 _70608.
Proof. exact (@lem5485788 (term201 _70608) (real_of_int _70608)). Qed.
Lemma lem5485790 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term279 _70608.
Proof. exact (@lem5485789 _70608 (@lem5485786 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485791 (_70608 : int) : (term280 _70608) = (term281 _70608).
Proof. exact (@lem1982759 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5485792 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5485794 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485795 : term143 = term191.
Proof. exact (@lem5485794 term144). Qed.
Lemma lem5485797 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5485798 : term164 = term165.
Proof. exact (@lem5485797 term144). Qed.
Lemma lem5485799 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485800 : term248 = term249.
Proof. exact (MK_COMB (@lem5485799) (@lem5485798)). Qed.
Lemma lem5485801 : term250 = term251.
Proof. exact (MK_COMB (@lem5485800) (@lem5485795)). Qed.
Lemma lem5485802 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5485804 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485805 : term211 = term217.
Proof. exact (@lem5485804 (NUMERAL 0) term144). Qed.
Lemma lem5485806 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485807 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485808 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485807 h1) (fun h1 : term217 = True => @lem5485806)). Qed.
Lemma lem5485809 : term217 = True.
Proof. exact (EQ_MP (@lem5485808) (@lem5485806)). Qed.
Lemma lem5485810 : term211 = True.
Proof. exact (TRANS (@lem5485805) (@lem5485809)). Qed.
Lemma lem5485811 : True = term211.
Proof. exact (SYM (@lem5485810)). Qed.
Lemma lem5485812 : term211.
Proof. exact (EQ_MP (@lem5485811) (@lem0)). Qed.
Lemma lem5485813 : term253.
Proof. exact (@lem5485802 (@lem5485812)). Qed.
Lemma lem5485815 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485816 : term211 = term217.
Proof. exact (@lem5485815 (NUMERAL 0) term144). Qed.
Lemma lem5485817 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485818 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485819 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485818 h1) (fun h1 : term217 = True => @lem5485817)). Qed.
Lemma lem5485820 : term217 = True.
Proof. exact (EQ_MP (@lem5485819) (@lem5485817)). Qed.
Lemma lem5485821 : term211 = True.
Proof. exact (TRANS (@lem5485816) (@lem5485820)). Qed.
Lemma lem5485822 : True = term211.
Proof. exact (SYM (@lem5485821)). Qed.
Lemma lem5485823 : term211.
Proof. exact (EQ_MP (@lem5485822) (@lem0)). Qed.
Lemma lem5485824 : term254.
Proof. exact (@lem5485813 (@lem5485823)). Qed.
Lemma lem5485826 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485827 : term211 = term217.
Proof. exact (@lem5485826 (NUMERAL 0) term144). Qed.
Lemma lem5485828 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485829 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485830 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485829 h1) (fun h1 : term217 = True => @lem5485828)). Qed.
Lemma lem5485831 : term217 = True.
Proof. exact (EQ_MP (@lem5485830) (@lem5485828)). Qed.
Lemma lem5485832 : term211 = True.
Proof. exact (TRANS (@lem5485827) (@lem5485831)). Qed.
Lemma lem5485833 : True = term211.
Proof. exact (SYM (@lem5485832)). Qed.
Lemma lem5485834 : term211.
Proof. exact (EQ_MP (@lem5485833) (@lem0)). Qed.
Lemma lem5485835 : term255.
Proof. exact (@lem5485824 (@lem5485834)). Qed.
Lemma lem5485837 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485838 : term173 = term174.
Proof. exact (@lem5485837 term144 term144). Qed.
Lemma lem5485839 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485840 : term176 = term144.
Proof. exact (EQ_MP (@lem5485839) (@lem940073)). Qed.
Lemma lem5485841 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485842 : term174 = term143.
Proof. exact (MK_COMB (@lem5485841) (@lem5485840)). Qed.
Lemma lem5485843 : term173 = term143.
Proof. exact (TRANS (@lem5485838) (@lem5485842)). Qed.
Lemma lem5485845 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5485846 : term192 = term197.
Proof. exact (@lem5485845 term144 term144). Qed.
Lemma lem5485847 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485848 : term176 = term144.
Proof. exact (EQ_MP (@lem5485847) (@lem940073)). Qed.
Lemma lem5485849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485850 : term174 = term143.
Proof. exact (MK_COMB (@lem5485849) (@lem5485848)). Qed.
Lemma lem5485851 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5485852 : term197 = term164.
Proof. exact (MK_COMB (@lem5485851) (@lem5485850)). Qed.
Lemma lem5485853 : term192 = term164.
Proof. exact (TRANS (@lem5485846) (@lem5485852)). Qed.
Lemma lem5485854 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485855 : term256 = term248.
Proof. exact (MK_COMB (@lem5485854) (@lem5485853)). Qed.
Lemma lem5485856 : term257 = term250.
Proof. exact (MK_COMB (@lem5485855) (@lem5485843)). Qed.
Lemma lem5485858 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5485859 : term250 = term129.
Proof. exact (@lem5485858 term144). Qed.
Lemma lem5485860 : term257 = term129.
Proof. exact (TRANS (@lem5485856) (@lem5485859)). Qed.
Lemma lem5485861 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485862 : term259 = term260.
Proof. exact (MK_COMB (@lem5485861) (@lem5485860)). Qed.
Lemma lem5485863 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5485864 : term261 = term222.
Proof. exact (MK_COMB (@lem5485862) (@lem5485863)). Qed.
Lemma lem5485866 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485867 : term222 = term129.
Proof. exact (@lem5485866 term144). Qed.
Lemma lem5485868 : term261 = term129.
Proof. exact (TRANS (@lem5485864) (@lem5485867)). Qed.
Lemma lem5485870 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5485871 : term173 = term174.
Proof. exact (@lem5485870 term144 term144). Qed.
Lemma lem5485872 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485873 : term176 = term144.
Proof. exact (EQ_MP (@lem5485872) (@lem940073)). Qed.
Lemma lem5485874 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485875 : term174 = term143.
Proof. exact (MK_COMB (@lem5485874) (@lem5485873)). Qed.
Lemma lem5485876 : term173 = term143.
Proof. exact (TRANS (@lem5485871) (@lem5485875)). Qed.
Lemma lem5485877 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5485878 : term262 = term222.
Proof. exact (MK_COMB (@lem5485877) (@lem5485876)). Qed.
Lemma lem5485880 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485881 : term222 = term129.
Proof. exact (@lem5485880 term144). Qed.
Lemma lem5485882 : term262 = term129.
Proof. exact (TRANS (@lem5485878) (@lem5485881)). Qed.
Lemma lem5485883 : term129 = term262.
Proof. exact (SYM (@lem5485882)). Qed.
Lemma lem5485884 : term261 = term262.
Proof. exact (TRANS (@lem5485868) (@lem5485883)). Qed.
Lemma lem5485885 : term251 = term161.
Proof. exact (@lem5485835 (@lem5485884)). Qed.
Lemma lem5485886 : term250 = term161.
Proof. exact (TRANS (@lem5485801) (@lem5485885)). Qed.
Lemma lem5485888 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5485889 : term161 = term129.
Proof. exact (@lem5485888 term129). Qed.
Lemma lem5485890 : term250 = term129.
Proof. exact (TRANS (@lem5485886) (@lem5485889)). Qed.
Lemma lem5485891 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5485892 : term263 = term260.
Proof. exact (MK_COMB (@lem5485891) (@lem5485890)). Qed.
Lemma lem5485893 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5485894 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5485892) (@lem5485893 _70608)). Qed.
Lemma lem5485895 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5485792 _70608) (@lem5485894 _70608)). Qed.
Lemma lem5485896 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5485897 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5485895 _70608) (@lem5485896 _70608)). Qed.
Lemma lem5485898 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5485899 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5485898) (@lem5485897 _70608)). Qed.
Lemma lem5485900 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5485901 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5485899 _70608) (@lem5485900)). Qed.
Lemma lem5485902 (_70608 : int) : (term280 _70608) = term282.
Proof. exact (TRANS (@lem5485791 _70608) (@lem5485901 _70608)). Qed.
Lemma lem5485903 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5485904 (_70608 : int) : (term280 _70608) = term164.
Proof. exact (TRANS (@lem5485902 _70608) (@lem5485903)). Qed.
Lemma lem5485905 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5485906 (_70608 : int) : (term283 _70608) = term284.
Proof. exact (MK_COMB (@lem5485905) (@lem5485904 _70608)). Qed.
Lemma lem5485907 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5485908 (_70608 : int) : (term279 _70608) = term285.
Proof. exact (MK_COMB (@lem5485906 _70608) (@lem5485907)). Qed.
Lemma lem5485909 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : term285.
Proof. exact (EQ_MP (@lem5485908 _70608) (@lem5485790 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485911 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5485912 : term285 = term286.
Proof. exact (@lem5485911 term129 term164). Qed.
Lemma lem5485914 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5485915 : term164 = term165.
Proof. exact (@lem5485914 term144). Qed.
Lemma lem5485917 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485918 : term129 = term161.
Proof. exact (@lem5485917 (NUMERAL 0)). Qed.
Lemma lem5485919 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5485920 : term131 = term287.
Proof. exact (MK_COMB (@lem5485919) (@lem5485918)). Qed.
Lemma lem5485921 : term286 = term288.
Proof. exact (MK_COMB (@lem5485920) (@lem5485915)). Qed.
Lemma lem5485922 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5485924 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485925 : term211 = term217.
Proof. exact (@lem5485924 (NUMERAL 0) term144). Qed.
Lemma lem5485926 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485927 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485928 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485927 h1) (fun h1 : term217 = True => @lem5485926)). Qed.
Lemma lem5485929 : term217 = True.
Proof. exact (EQ_MP (@lem5485928) (@lem5485926)). Qed.
Lemma lem5485930 : term211 = True.
Proof. exact (TRANS (@lem5485925) (@lem5485929)). Qed.
Lemma lem5485931 : True = term211.
Proof. exact (SYM (@lem5485930)). Qed.
Lemma lem5485932 : term211.
Proof. exact (EQ_MP (@lem5485931) (@lem0)). Qed.
Lemma lem5485933 : term290.
Proof. exact (@lem5485922 (@lem5485932)). Qed.
Lemma lem5485935 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5485936 : term211 = term217.
Proof. exact (@lem5485935 (NUMERAL 0) term144). Qed.
Lemma lem5485937 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485938 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5485939 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485938 h1) (fun h1 : term217 = True => @lem5485937)). Qed.
Lemma lem5485940 : term217 = True.
Proof. exact (EQ_MP (@lem5485939) (@lem5485937)). Qed.
Lemma lem5485941 : term211 = True.
Proof. exact (TRANS (@lem5485936) (@lem5485940)). Qed.
Lemma lem5485942 : True = term211.
Proof. exact (SYM (@lem5485941)). Qed.
Lemma lem5485943 : term211.
Proof. exact (EQ_MP (@lem5485942) (@lem0)). Qed.
Lemma lem5485944 : term288 = term291.
Proof. exact (@lem5485933 (@lem5485943)). Qed.
Lemma lem5485946 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5485947 : term192 = term197.
Proof. exact (@lem5485946 term144 term144). Qed.
Lemma lem5485948 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5485949 : term176 = term144.
Proof. exact (EQ_MP (@lem5485948) (@lem940073)). Qed.
Lemma lem5485950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5485951 : term174 = term143.
Proof. exact (MK_COMB (@lem5485950) (@lem5485949)). Qed.
Lemma lem5485952 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5485953 : term197 = term164.
Proof. exact (MK_COMB (@lem5485952) (@lem5485951)). Qed.
Lemma lem5485954 : term192 = term164.
Proof. exact (TRANS (@lem5485947) (@lem5485953)). Qed.
Lemma lem5485956 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5485957 : term222 = term129.
Proof. exact (@lem5485956 term144). Qed.
Lemma lem5485958 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5485959 : term292 = term131.
Proof. exact (MK_COMB (@lem5485958) (@lem5485957)). Qed.
Lemma lem5485960 : term291 = term286.
Proof. exact (MK_COMB (@lem5485959) (@lem5485954)). Qed.
Lemma lem5485962 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5485963 : term286 = term295.
Proof. exact (@lem5485962 (NUMERAL 0) term144). Qed.
Lemma lem5485964 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5485965 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5485966 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5485965 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5485964)). Qed.
Lemma lem5485967 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5485966) (@lem5485964)). Qed.
Lemma lem5485968 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5485969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5485970 : term296 = (and True).
Proof. exact (MK_COMB (@lem5485969) (@lem5485968)). Qed.
Lemma lem5485971 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5485970) (@lem5485967)). Qed.
Lemma lem5485973 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5485974 : term295 = False.
Proof. exact (TRANS (@lem5485971) (@lem5485973)). Qed.
Lemma lem5485975 : term286 = False.
Proof. exact (TRANS (@lem5485963) (@lem5485974)). Qed.
Lemma lem5485976 : term291 = False.
Proof. exact (TRANS (@lem5485960) (@lem5485975)). Qed.
Lemma lem5485977 : term288 = False.
Proof. exact (TRANS (@lem5485944) (@lem5485976)). Qed.
Lemma lem5485978 : term286 = False.
Proof. exact (TRANS (@lem5485921) (@lem5485977)). Qed.
Lemma lem5485979 : term285 = False.
Proof. exact (TRANS (@lem5485912) (@lem5485978)). Qed.
Lemma lem5485980 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term886 _70606 _70607 _70608) : False.
Proof. exact (EQ_MP (@lem5485979) (@lem5485909 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485981 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term887 _70606 _70607 _70608.
Proof. exact (h1). Qed.
Lemma lem5485982 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term794 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485981 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485984 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term745 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485982 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485986 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term696 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485984 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485987 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term184 _70608.
Proof. exact (proj1 (@lem5485984 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485988 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term644 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5485986 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485990 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term613 _70607 _70608.
Proof. exact (proj2 (@lem5485988 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485992 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term270 _70608.
Proof. exact (proj2 (@lem5485990 _70606 _70607 _70608 h1)). Qed.
Lemma lem5485995 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5485996 : term210 = term211.
Proof. exact (@lem5485995 term129 term143). Qed.
Lemma lem5485998 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5485999 : term143 = term191.
Proof. exact (@lem5485998 term144). Qed.
Lemma lem5486001 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486002 : term129 = term161.
Proof. exact (@lem5486001 (NUMERAL 0)). Qed.
Lemma lem5486003 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486004 : term212 = term213.
Proof. exact (MK_COMB (@lem5486003) (@lem5486002)). Qed.
Lemma lem5486005 : term211 = term214.
Proof. exact (MK_COMB (@lem5486004) (@lem5485999)). Qed.
Lemma lem5486006 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5486008 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486009 : term211 = term217.
Proof. exact (@lem5486008 (NUMERAL 0) term144). Qed.
Lemma lem5486010 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486011 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486012 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486011 h1) (fun h1 : term217 = True => @lem5486010)). Qed.
Lemma lem5486013 : term217 = True.
Proof. exact (EQ_MP (@lem5486012) (@lem5486010)). Qed.
Lemma lem5486014 : term211 = True.
Proof. exact (TRANS (@lem5486009) (@lem5486013)). Qed.
Lemma lem5486015 : True = term211.
Proof. exact (SYM (@lem5486014)). Qed.
Lemma lem5486016 : term211.
Proof. exact (EQ_MP (@lem5486015) (@lem0)). Qed.
Lemma lem5486017 : term219.
Proof. exact (@lem5486006 (@lem5486016)). Qed.
Lemma lem5486019 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486020 : term211 = term217.
Proof. exact (@lem5486019 (NUMERAL 0) term144). Qed.
Lemma lem5486021 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486022 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486023 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486022 h1) (fun h1 : term217 = True => @lem5486021)). Qed.
Lemma lem5486024 : term217 = True.
Proof. exact (EQ_MP (@lem5486023) (@lem5486021)). Qed.
Lemma lem5486025 : term211 = True.
Proof. exact (TRANS (@lem5486020) (@lem5486024)). Qed.
Lemma lem5486026 : True = term211.
Proof. exact (SYM (@lem5486025)). Qed.
Lemma lem5486027 : term211.
Proof. exact (EQ_MP (@lem5486026) (@lem0)). Qed.
Lemma lem5486028 : term214 = term220.
Proof. exact (@lem5486017 (@lem5486027)). Qed.
Lemma lem5486030 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486031 : term173 = term174.
Proof. exact (@lem5486030 term144 term144). Qed.
Lemma lem5486032 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486033 : term176 = term144.
Proof. exact (EQ_MP (@lem5486032) (@lem940073)). Qed.
Lemma lem5486034 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486035 : term174 = term143.
Proof. exact (MK_COMB (@lem5486034) (@lem5486033)). Qed.
Lemma lem5486036 : term173 = term143.
Proof. exact (TRANS (@lem5486031) (@lem5486035)). Qed.
Lemma lem5486038 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486039 : term222 = term129.
Proof. exact (@lem5486038 term144). Qed.
Lemma lem5486040 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486041 : term223 = term212.
Proof. exact (MK_COMB (@lem5486040) (@lem5486039)). Qed.
Lemma lem5486042 : term220 = term211.
Proof. exact (MK_COMB (@lem5486041) (@lem5486036)). Qed.
Lemma lem5486044 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486045 : term211 = term217.
Proof. exact (@lem5486044 (NUMERAL 0) term144). Qed.
Lemma lem5486046 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486047 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486048 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486047 h1) (fun h1 : term217 = True => @lem5486046)). Qed.
Lemma lem5486049 : term217 = True.
Proof. exact (EQ_MP (@lem5486048) (@lem5486046)). Qed.
Lemma lem5486050 : term211 = True.
Proof. exact (TRANS (@lem5486045) (@lem5486049)). Qed.
Lemma lem5486051 : term220 = True.
Proof. exact (TRANS (@lem5486042) (@lem5486050)). Qed.
Lemma lem5486052 : term214 = True.
Proof. exact (TRANS (@lem5486028) (@lem5486051)). Qed.
Lemma lem5486053 : term211 = True.
Proof. exact (TRANS (@lem5486005) (@lem5486052)). Qed.
Lemma lem5486054 : term210 = True.
Proof. exact (TRANS (@lem5485996) (@lem5486053)). Qed.
Lemma lem5486055 : True = term210.
Proof. exact (SYM (@lem5486054)). Qed.
Lemma lem5486056 : term210.
Proof. exact (EQ_MP (@lem5486055) (@lem0)). Qed.
Lemma lem5486057 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term224 _70608.
Proof. exact (conj (@lem5486056) (@lem5485987 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486059 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5486060 (_70608 : int) : term226 _70608.
Proof. exact (@lem5486059 term143 (real_of_int _70608)). Qed.
Lemma lem5486061 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term227 _70608.
Proof. exact (@lem5486060 _70608 (@lem5486057 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486062 (_70608 : int) : (term228 _70608) = (real_of_int _70608).
Proof. exact (@lem1982733 (real_of_int _70608)). Qed.
Lemma lem5486063 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486064 (_70608 : int) : (term229 _70608) = (term183 _70608).
Proof. exact (MK_COMB (@lem5486063) (@lem5486062 _70608)). Qed.
Lemma lem5486065 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486066 (_70608 : int) : (term227 _70608) = (term184 _70608).
Proof. exact (MK_COMB (@lem5486064 _70608) (@lem5486065)). Qed.
Lemma lem5486067 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term184 _70608.
Proof. exact (EQ_MP (@lem5486066 _70608) (@lem5486061 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486069 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5486070 : term210 = term211.
Proof. exact (@lem5486069 term129 term143). Qed.
Lemma lem5486072 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486073 : term143 = term191.
Proof. exact (@lem5486072 term144). Qed.
Lemma lem5486075 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486076 : term129 = term161.
Proof. exact (@lem5486075 (NUMERAL 0)). Qed.
Lemma lem5486077 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486078 : term212 = term213.
Proof. exact (MK_COMB (@lem5486077) (@lem5486076)). Qed.
Lemma lem5486079 : term211 = term214.
Proof. exact (MK_COMB (@lem5486078) (@lem5486073)). Qed.
Lemma lem5486080 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5486082 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486083 : term211 = term217.
Proof. exact (@lem5486082 (NUMERAL 0) term144). Qed.
Lemma lem5486084 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486085 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486086 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486085 h1) (fun h1 : term217 = True => @lem5486084)). Qed.
Lemma lem5486087 : term217 = True.
Proof. exact (EQ_MP (@lem5486086) (@lem5486084)). Qed.
Lemma lem5486088 : term211 = True.
Proof. exact (TRANS (@lem5486083) (@lem5486087)). Qed.
Lemma lem5486089 : True = term211.
Proof. exact (SYM (@lem5486088)). Qed.
Lemma lem5486090 : term211.
Proof. exact (EQ_MP (@lem5486089) (@lem0)). Qed.
Lemma lem5486091 : term219.
Proof. exact (@lem5486080 (@lem5486090)). Qed.
Lemma lem5486093 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486094 : term211 = term217.
Proof. exact (@lem5486093 (NUMERAL 0) term144). Qed.
Lemma lem5486095 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486096 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486097 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486096 h1) (fun h1 : term217 = True => @lem5486095)). Qed.
Lemma lem5486098 : term217 = True.
Proof. exact (EQ_MP (@lem5486097) (@lem5486095)). Qed.
Lemma lem5486099 : term211 = True.
Proof. exact (TRANS (@lem5486094) (@lem5486098)). Qed.
Lemma lem5486100 : True = term211.
Proof. exact (SYM (@lem5486099)). Qed.
Lemma lem5486101 : term211.
Proof. exact (EQ_MP (@lem5486100) (@lem0)). Qed.
Lemma lem5486102 : term214 = term220.
Proof. exact (@lem5486091 (@lem5486101)). Qed.
Lemma lem5486104 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486105 : term173 = term174.
Proof. exact (@lem5486104 term144 term144). Qed.
Lemma lem5486106 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486107 : term176 = term144.
Proof. exact (EQ_MP (@lem5486106) (@lem940073)). Qed.
Lemma lem5486108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486109 : term174 = term143.
Proof. exact (MK_COMB (@lem5486108) (@lem5486107)). Qed.
Lemma lem5486110 : term173 = term143.
Proof. exact (TRANS (@lem5486105) (@lem5486109)). Qed.
Lemma lem5486112 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486113 : term222 = term129.
Proof. exact (@lem5486112 term144). Qed.
Lemma lem5486114 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486115 : term223 = term212.
Proof. exact (MK_COMB (@lem5486114) (@lem5486113)). Qed.
Lemma lem5486116 : term220 = term211.
Proof. exact (MK_COMB (@lem5486115) (@lem5486110)). Qed.
Lemma lem5486118 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486119 : term211 = term217.
Proof. exact (@lem5486118 (NUMERAL 0) term144). Qed.
Lemma lem5486120 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486121 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486122 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486121 h1) (fun h1 : term217 = True => @lem5486120)). Qed.
Lemma lem5486123 : term217 = True.
Proof. exact (EQ_MP (@lem5486122) (@lem5486120)). Qed.
Lemma lem5486124 : term211 = True.
Proof. exact (TRANS (@lem5486119) (@lem5486123)). Qed.
Lemma lem5486125 : term220 = True.
Proof. exact (TRANS (@lem5486116) (@lem5486124)). Qed.
Lemma lem5486126 : term214 = True.
Proof. exact (TRANS (@lem5486102) (@lem5486125)). Qed.
Lemma lem5486127 : term211 = True.
Proof. exact (TRANS (@lem5486079) (@lem5486126)). Qed.
Lemma lem5486128 : term210 = True.
Proof. exact (TRANS (@lem5486070) (@lem5486127)). Qed.
Lemma lem5486129 : True = term210.
Proof. exact (SYM (@lem5486128)). Qed.
Lemma lem5486130 : term210.
Proof. exact (EQ_MP (@lem5486129) (@lem0)). Qed.
Lemma lem5486131 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term271 _70608.
Proof. exact (conj (@lem5486130) (@lem5485992 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486133 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5486134 (_70608 : int) : term272 _70608.
Proof. exact (@lem5486133 term143 (term201 _70608)). Qed.
Lemma lem5486135 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term273 _70608.
Proof. exact (@lem5486134 _70608 (@lem5486131 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486136 (_70608 : int) : (term274 _70608) = (term201 _70608).
Proof. exact (@lem1982733 (term201 _70608)). Qed.
Lemma lem5486137 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486138 (_70608 : int) : (term275 _70608) = (term269 _70608).
Proof. exact (MK_COMB (@lem5486137) (@lem5486136 _70608)). Qed.
Lemma lem5486139 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486140 (_70608 : int) : (term273 _70608) = (term270 _70608).
Proof. exact (MK_COMB (@lem5486138 _70608) (@lem5486139)). Qed.
Lemma lem5486141 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term270 _70608.
Proof. exact (EQ_MP (@lem5486140 _70608) (@lem5486135 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486142 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term276 _70608.
Proof. exact (conj (@lem5486141 _70606 _70607 _70608 h1) (@lem5486067 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486144 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5486145 (_70608 : int) : term278 _70608.
Proof. exact (@lem5486144 (term201 _70608) (real_of_int _70608)). Qed.
Lemma lem5486146 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term279 _70608.
Proof. exact (@lem5486145 _70608 (@lem5486142 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486147 (_70608 : int) : (term280 _70608) = (term281 _70608).
Proof. exact (@lem1982759 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5486148 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5486150 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486151 : term143 = term191.
Proof. exact (@lem5486150 term144). Qed.
Lemma lem5486153 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5486154 : term164 = term165.
Proof. exact (@lem5486153 term144). Qed.
Lemma lem5486155 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486156 : term248 = term249.
Proof. exact (MK_COMB (@lem5486155) (@lem5486154)). Qed.
Lemma lem5486157 : term250 = term251.
Proof. exact (MK_COMB (@lem5486156) (@lem5486151)). Qed.
Lemma lem5486158 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5486160 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486161 : term211 = term217.
Proof. exact (@lem5486160 (NUMERAL 0) term144). Qed.
Lemma lem5486162 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486163 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486164 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486163 h1) (fun h1 : term217 = True => @lem5486162)). Qed.
Lemma lem5486165 : term217 = True.
Proof. exact (EQ_MP (@lem5486164) (@lem5486162)). Qed.
Lemma lem5486166 : term211 = True.
Proof. exact (TRANS (@lem5486161) (@lem5486165)). Qed.
Lemma lem5486167 : True = term211.
Proof. exact (SYM (@lem5486166)). Qed.
Lemma lem5486168 : term211.
Proof. exact (EQ_MP (@lem5486167) (@lem0)). Qed.
Lemma lem5486169 : term253.
Proof. exact (@lem5486158 (@lem5486168)). Qed.
Lemma lem5486171 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486172 : term211 = term217.
Proof. exact (@lem5486171 (NUMERAL 0) term144). Qed.
Lemma lem5486173 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486174 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486175 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486174 h1) (fun h1 : term217 = True => @lem5486173)). Qed.
Lemma lem5486176 : term217 = True.
Proof. exact (EQ_MP (@lem5486175) (@lem5486173)). Qed.
Lemma lem5486177 : term211 = True.
Proof. exact (TRANS (@lem5486172) (@lem5486176)). Qed.
Lemma lem5486178 : True = term211.
Proof. exact (SYM (@lem5486177)). Qed.
Lemma lem5486179 : term211.
Proof. exact (EQ_MP (@lem5486178) (@lem0)). Qed.
Lemma lem5486180 : term254.
Proof. exact (@lem5486169 (@lem5486179)). Qed.
Lemma lem5486182 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486183 : term211 = term217.
Proof. exact (@lem5486182 (NUMERAL 0) term144). Qed.
Lemma lem5486184 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486185 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486186 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486185 h1) (fun h1 : term217 = True => @lem5486184)). Qed.
Lemma lem5486187 : term217 = True.
Proof. exact (EQ_MP (@lem5486186) (@lem5486184)). Qed.
Lemma lem5486188 : term211 = True.
Proof. exact (TRANS (@lem5486183) (@lem5486187)). Qed.
Lemma lem5486189 : True = term211.
Proof. exact (SYM (@lem5486188)). Qed.
Lemma lem5486190 : term211.
Proof. exact (EQ_MP (@lem5486189) (@lem0)). Qed.
Lemma lem5486191 : term255.
Proof. exact (@lem5486180 (@lem5486190)). Qed.
Lemma lem5486193 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486194 : term173 = term174.
Proof. exact (@lem5486193 term144 term144). Qed.
Lemma lem5486195 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486196 : term176 = term144.
Proof. exact (EQ_MP (@lem5486195) (@lem940073)). Qed.
Lemma lem5486197 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486198 : term174 = term143.
Proof. exact (MK_COMB (@lem5486197) (@lem5486196)). Qed.
Lemma lem5486199 : term173 = term143.
Proof. exact (TRANS (@lem5486194) (@lem5486198)). Qed.
Lemma lem5486201 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5486202 : term192 = term197.
Proof. exact (@lem5486201 term144 term144). Qed.
Lemma lem5486203 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486204 : term176 = term144.
Proof. exact (EQ_MP (@lem5486203) (@lem940073)). Qed.
Lemma lem5486205 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486206 : term174 = term143.
Proof. exact (MK_COMB (@lem5486205) (@lem5486204)). Qed.
Lemma lem5486207 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5486208 : term197 = term164.
Proof. exact (MK_COMB (@lem5486207) (@lem5486206)). Qed.
Lemma lem5486209 : term192 = term164.
Proof. exact (TRANS (@lem5486202) (@lem5486208)). Qed.
Lemma lem5486210 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486211 : term256 = term248.
Proof. exact (MK_COMB (@lem5486210) (@lem5486209)). Qed.
Lemma lem5486212 : term257 = term250.
Proof. exact (MK_COMB (@lem5486211) (@lem5486199)). Qed.
Lemma lem5486214 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5486215 : term250 = term129.
Proof. exact (@lem5486214 term144). Qed.
Lemma lem5486216 : term257 = term129.
Proof. exact (TRANS (@lem5486212) (@lem5486215)). Qed.
Lemma lem5486217 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5486218 : term259 = term260.
Proof. exact (MK_COMB (@lem5486217) (@lem5486216)). Qed.
Lemma lem5486219 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5486220 : term261 = term222.
Proof. exact (MK_COMB (@lem5486218) (@lem5486219)). Qed.
Lemma lem5486222 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486223 : term222 = term129.
Proof. exact (@lem5486222 term144). Qed.
Lemma lem5486224 : term261 = term129.
Proof. exact (TRANS (@lem5486220) (@lem5486223)). Qed.
Lemma lem5486226 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486227 : term173 = term174.
Proof. exact (@lem5486226 term144 term144). Qed.
Lemma lem5486228 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486229 : term176 = term144.
Proof. exact (EQ_MP (@lem5486228) (@lem940073)). Qed.
Lemma lem5486230 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486231 : term174 = term143.
Proof. exact (MK_COMB (@lem5486230) (@lem5486229)). Qed.
Lemma lem5486232 : term173 = term143.
Proof. exact (TRANS (@lem5486227) (@lem5486231)). Qed.
Lemma lem5486233 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5486234 : term262 = term222.
Proof. exact (MK_COMB (@lem5486233) (@lem5486232)). Qed.
Lemma lem5486236 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486237 : term222 = term129.
Proof. exact (@lem5486236 term144). Qed.
Lemma lem5486238 : term262 = term129.
Proof. exact (TRANS (@lem5486234) (@lem5486237)). Qed.
Lemma lem5486239 : term129 = term262.
Proof. exact (SYM (@lem5486238)). Qed.
Lemma lem5486240 : term261 = term262.
Proof. exact (TRANS (@lem5486224) (@lem5486239)). Qed.
Lemma lem5486241 : term251 = term161.
Proof. exact (@lem5486191 (@lem5486240)). Qed.
Lemma lem5486242 : term250 = term161.
Proof. exact (TRANS (@lem5486157) (@lem5486241)). Qed.
Lemma lem5486244 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5486245 : term161 = term129.
Proof. exact (@lem5486244 term129). Qed.
Lemma lem5486246 : term250 = term129.
Proof. exact (TRANS (@lem5486242) (@lem5486245)). Qed.
Lemma lem5486247 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5486248 : term263 = term260.
Proof. exact (MK_COMB (@lem5486247) (@lem5486246)). Qed.
Lemma lem5486249 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5486250 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5486248) (@lem5486249 _70608)). Qed.
Lemma lem5486251 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5486148 _70608) (@lem5486250 _70608)). Qed.
Lemma lem5486252 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5486253 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5486251 _70608) (@lem5486252 _70608)). Qed.
Lemma lem5486254 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486255 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5486254) (@lem5486253 _70608)). Qed.
Lemma lem5486256 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5486257 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5486255 _70608) (@lem5486256)). Qed.
Lemma lem5486258 (_70608 : int) : (term280 _70608) = term282.
Proof. exact (TRANS (@lem5486147 _70608) (@lem5486257 _70608)). Qed.
Lemma lem5486259 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5486260 (_70608 : int) : (term280 _70608) = term164.
Proof. exact (TRANS (@lem5486258 _70608) (@lem5486259)). Qed.
Lemma lem5486261 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486262 (_70608 : int) : (term283 _70608) = term284.
Proof. exact (MK_COMB (@lem5486261) (@lem5486260 _70608)). Qed.
Lemma lem5486263 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486264 (_70608 : int) : (term279 _70608) = term285.
Proof. exact (MK_COMB (@lem5486262 _70608) (@lem5486263)). Qed.
Lemma lem5486265 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : term285.
Proof. exact (EQ_MP (@lem5486264 _70608) (@lem5486146 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486267 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5486268 : term285 = term286.
Proof. exact (@lem5486267 term129 term164). Qed.
Lemma lem5486270 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5486271 : term164 = term165.
Proof. exact (@lem5486270 term144). Qed.
Lemma lem5486273 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486274 : term129 = term161.
Proof. exact (@lem5486273 (NUMERAL 0)). Qed.
Lemma lem5486275 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5486276 : term131 = term287.
Proof. exact (MK_COMB (@lem5486275) (@lem5486274)). Qed.
Lemma lem5486277 : term286 = term288.
Proof. exact (MK_COMB (@lem5486276) (@lem5486271)). Qed.
Lemma lem5486278 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5486280 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486281 : term211 = term217.
Proof. exact (@lem5486280 (NUMERAL 0) term144). Qed.
Lemma lem5486282 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486283 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486284 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486283 h1) (fun h1 : term217 = True => @lem5486282)). Qed.
Lemma lem5486285 : term217 = True.
Proof. exact (EQ_MP (@lem5486284) (@lem5486282)). Qed.
Lemma lem5486286 : term211 = True.
Proof. exact (TRANS (@lem5486281) (@lem5486285)). Qed.
Lemma lem5486287 : True = term211.
Proof. exact (SYM (@lem5486286)). Qed.
Lemma lem5486288 : term211.
Proof. exact (EQ_MP (@lem5486287) (@lem0)). Qed.
Lemma lem5486289 : term290.
Proof. exact (@lem5486278 (@lem5486288)). Qed.
Lemma lem5486291 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486292 : term211 = term217.
Proof. exact (@lem5486291 (NUMERAL 0) term144). Qed.
Lemma lem5486293 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486294 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486295 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486294 h1) (fun h1 : term217 = True => @lem5486293)). Qed.
Lemma lem5486296 : term217 = True.
Proof. exact (EQ_MP (@lem5486295) (@lem5486293)). Qed.
Lemma lem5486297 : term211 = True.
Proof. exact (TRANS (@lem5486292) (@lem5486296)). Qed.
Lemma lem5486298 : True = term211.
Proof. exact (SYM (@lem5486297)). Qed.
Lemma lem5486299 : term211.
Proof. exact (EQ_MP (@lem5486298) (@lem0)). Qed.
Lemma lem5486300 : term288 = term291.
Proof. exact (@lem5486289 (@lem5486299)). Qed.
Lemma lem5486302 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5486303 : term192 = term197.
Proof. exact (@lem5486302 term144 term144). Qed.
Lemma lem5486304 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486305 : term176 = term144.
Proof. exact (EQ_MP (@lem5486304) (@lem940073)). Qed.
Lemma lem5486306 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486307 : term174 = term143.
Proof. exact (MK_COMB (@lem5486306) (@lem5486305)). Qed.
Lemma lem5486308 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5486309 : term197 = term164.
Proof. exact (MK_COMB (@lem5486308) (@lem5486307)). Qed.
Lemma lem5486310 : term192 = term164.
Proof. exact (TRANS (@lem5486303) (@lem5486309)). Qed.
Lemma lem5486312 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486313 : term222 = term129.
Proof. exact (@lem5486312 term144). Qed.
Lemma lem5486314 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5486315 : term292 = term131.
Proof. exact (MK_COMB (@lem5486314) (@lem5486313)). Qed.
Lemma lem5486316 : term291 = term286.
Proof. exact (MK_COMB (@lem5486315) (@lem5486310)). Qed.
Lemma lem5486318 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5486319 : term286 = term295.
Proof. exact (@lem5486318 (NUMERAL 0) term144). Qed.
Lemma lem5486320 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486321 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5486322 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486321 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5486320)). Qed.
Lemma lem5486323 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5486322) (@lem5486320)). Qed.
Lemma lem5486324 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5486325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5486326 : term296 = (and True).
Proof. exact (MK_COMB (@lem5486325) (@lem5486324)). Qed.
Lemma lem5486327 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5486326) (@lem5486323)). Qed.
Lemma lem5486329 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5486330 : term295 = False.
Proof. exact (TRANS (@lem5486327) (@lem5486329)). Qed.
Lemma lem5486331 : term286 = False.
Proof. exact (TRANS (@lem5486319) (@lem5486330)). Qed.
Lemma lem5486332 : term291 = False.
Proof. exact (TRANS (@lem5486316) (@lem5486331)). Qed.
Lemma lem5486333 : term288 = False.
Proof. exact (TRANS (@lem5486300) (@lem5486332)). Qed.
Lemma lem5486334 : term286 = False.
Proof. exact (TRANS (@lem5486277) (@lem5486333)). Qed.
Lemma lem5486335 : term285 = False.
Proof. exact (TRANS (@lem5486268) (@lem5486334)). Qed.
Lemma lem5486336 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term887 _70606 _70607 _70608) : False.
Proof. exact (EQ_MP (@lem5486335) (@lem5486265 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486337 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term792 _70606 _70607 _70608) : False.
Proof. exact (or_elim (@lem5485624 _70606 _70607 _70608 h1) (fun h0 : term886 _70606 _70607 _70608 => @lem5485980 _70606 _70607 _70608 h0) (fun h0 : term887 _70606 _70607 _70608 => @lem5486336 _70606 _70607 _70608 h0)). Qed.
Lemma lem5486338 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term788 _70606 _70607 _70608) : term788 _70606 _70607 _70608.
Proof. exact (h1). Qed.
Lemma lem5486339 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term888 _70606 _70607 _70608.
Proof. exact (h1). Qed.
Lemma lem5486340 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term789 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486339 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486342 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term740 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486340 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486344 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term691 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486342 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486345 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term184 _70608.
Proof. exact (proj1 (@lem5486342 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486346 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term645 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486344 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486348 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term613 _70607 _70608.
Proof. exact (proj2 (@lem5486346 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486352 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term270 _70608.
Proof. exact (proj2 (@lem5486348 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486355 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5486356 : term210 = term211.
Proof. exact (@lem5486355 term129 term143). Qed.
Lemma lem5486358 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486359 : term143 = term191.
Proof. exact (@lem5486358 term144). Qed.
Lemma lem5486361 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486362 : term129 = term161.
Proof. exact (@lem5486361 (NUMERAL 0)). Qed.
Lemma lem5486363 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486364 : term212 = term213.
Proof. exact (MK_COMB (@lem5486363) (@lem5486362)). Qed.
Lemma lem5486365 : term211 = term214.
Proof. exact (MK_COMB (@lem5486364) (@lem5486359)). Qed.
Lemma lem5486366 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5486368 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486369 : term211 = term217.
Proof. exact (@lem5486368 (NUMERAL 0) term144). Qed.
Lemma lem5486370 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486371 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486372 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486371 h1) (fun h1 : term217 = True => @lem5486370)). Qed.
Lemma lem5486373 : term217 = True.
Proof. exact (EQ_MP (@lem5486372) (@lem5486370)). Qed.
Lemma lem5486374 : term211 = True.
Proof. exact (TRANS (@lem5486369) (@lem5486373)). Qed.
Lemma lem5486375 : True = term211.
Proof. exact (SYM (@lem5486374)). Qed.
Lemma lem5486376 : term211.
Proof. exact (EQ_MP (@lem5486375) (@lem0)). Qed.
Lemma lem5486377 : term219.
Proof. exact (@lem5486366 (@lem5486376)). Qed.
Lemma lem5486379 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486380 : term211 = term217.
Proof. exact (@lem5486379 (NUMERAL 0) term144). Qed.
Lemma lem5486381 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486382 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486383 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486382 h1) (fun h1 : term217 = True => @lem5486381)). Qed.
Lemma lem5486384 : term217 = True.
Proof. exact (EQ_MP (@lem5486383) (@lem5486381)). Qed.
Lemma lem5486385 : term211 = True.
Proof. exact (TRANS (@lem5486380) (@lem5486384)). Qed.
Lemma lem5486386 : True = term211.
Proof. exact (SYM (@lem5486385)). Qed.
Lemma lem5486387 : term211.
Proof. exact (EQ_MP (@lem5486386) (@lem0)). Qed.
Lemma lem5486388 : term214 = term220.
Proof. exact (@lem5486377 (@lem5486387)). Qed.
Lemma lem5486390 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486391 : term173 = term174.
Proof. exact (@lem5486390 term144 term144). Qed.
Lemma lem5486392 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486393 : term176 = term144.
Proof. exact (EQ_MP (@lem5486392) (@lem940073)). Qed.
Lemma lem5486394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486395 : term174 = term143.
Proof. exact (MK_COMB (@lem5486394) (@lem5486393)). Qed.
Lemma lem5486396 : term173 = term143.
Proof. exact (TRANS (@lem5486391) (@lem5486395)). Qed.
Lemma lem5486398 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486399 : term222 = term129.
Proof. exact (@lem5486398 term144). Qed.
Lemma lem5486400 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486401 : term223 = term212.
Proof. exact (MK_COMB (@lem5486400) (@lem5486399)). Qed.
Lemma lem5486402 : term220 = term211.
Proof. exact (MK_COMB (@lem5486401) (@lem5486396)). Qed.
Lemma lem5486404 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486405 : term211 = term217.
Proof. exact (@lem5486404 (NUMERAL 0) term144). Qed.
Lemma lem5486406 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486407 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486408 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486407 h1) (fun h1 : term217 = True => @lem5486406)). Qed.
Lemma lem5486409 : term217 = True.
Proof. exact (EQ_MP (@lem5486408) (@lem5486406)). Qed.
Lemma lem5486410 : term211 = True.
Proof. exact (TRANS (@lem5486405) (@lem5486409)). Qed.
Lemma lem5486411 : term220 = True.
Proof. exact (TRANS (@lem5486402) (@lem5486410)). Qed.
Lemma lem5486412 : term214 = True.
Proof. exact (TRANS (@lem5486388) (@lem5486411)). Qed.
Lemma lem5486413 : term211 = True.
Proof. exact (TRANS (@lem5486365) (@lem5486412)). Qed.
Lemma lem5486414 : term210 = True.
Proof. exact (TRANS (@lem5486356) (@lem5486413)). Qed.
Lemma lem5486415 : True = term210.
Proof. exact (SYM (@lem5486414)). Qed.
Lemma lem5486416 : term210.
Proof. exact (EQ_MP (@lem5486415) (@lem0)). Qed.
Lemma lem5486417 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term224 _70608.
Proof. exact (conj (@lem5486416) (@lem5486345 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486419 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5486420 (_70608 : int) : term226 _70608.
Proof. exact (@lem5486419 term143 (real_of_int _70608)). Qed.
Lemma lem5486421 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term227 _70608.
Proof. exact (@lem5486420 _70608 (@lem5486417 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486422 (_70608 : int) : (term228 _70608) = (real_of_int _70608).
Proof. exact (@lem1982733 (real_of_int _70608)). Qed.
Lemma lem5486423 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486424 (_70608 : int) : (term229 _70608) = (term183 _70608).
Proof. exact (MK_COMB (@lem5486423) (@lem5486422 _70608)). Qed.
Lemma lem5486425 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486426 (_70608 : int) : (term227 _70608) = (term184 _70608).
Proof. exact (MK_COMB (@lem5486424 _70608) (@lem5486425)). Qed.
Lemma lem5486427 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term184 _70608.
Proof. exact (EQ_MP (@lem5486426 _70608) (@lem5486421 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486429 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5486430 : term210 = term211.
Proof. exact (@lem5486429 term129 term143). Qed.
Lemma lem5486432 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486433 : term143 = term191.
Proof. exact (@lem5486432 term144). Qed.
Lemma lem5486435 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486436 : term129 = term161.
Proof. exact (@lem5486435 (NUMERAL 0)). Qed.
Lemma lem5486437 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486438 : term212 = term213.
Proof. exact (MK_COMB (@lem5486437) (@lem5486436)). Qed.
Lemma lem5486439 : term211 = term214.
Proof. exact (MK_COMB (@lem5486438) (@lem5486433)). Qed.
Lemma lem5486440 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5486442 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486443 : term211 = term217.
Proof. exact (@lem5486442 (NUMERAL 0) term144). Qed.
Lemma lem5486444 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486445 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486446 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486445 h1) (fun h1 : term217 = True => @lem5486444)). Qed.
Lemma lem5486447 : term217 = True.
Proof. exact (EQ_MP (@lem5486446) (@lem5486444)). Qed.
Lemma lem5486448 : term211 = True.
Proof. exact (TRANS (@lem5486443) (@lem5486447)). Qed.
Lemma lem5486449 : True = term211.
Proof. exact (SYM (@lem5486448)). Qed.
Lemma lem5486450 : term211.
Proof. exact (EQ_MP (@lem5486449) (@lem0)). Qed.
Lemma lem5486451 : term219.
Proof. exact (@lem5486440 (@lem5486450)). Qed.
Lemma lem5486453 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486454 : term211 = term217.
Proof. exact (@lem5486453 (NUMERAL 0) term144). Qed.
Lemma lem5486455 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486456 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486457 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486456 h1) (fun h1 : term217 = True => @lem5486455)). Qed.
Lemma lem5486458 : term217 = True.
Proof. exact (EQ_MP (@lem5486457) (@lem5486455)). Qed.
Lemma lem5486459 : term211 = True.
Proof. exact (TRANS (@lem5486454) (@lem5486458)). Qed.
Lemma lem5486460 : True = term211.
Proof. exact (SYM (@lem5486459)). Qed.
Lemma lem5486461 : term211.
Proof. exact (EQ_MP (@lem5486460) (@lem0)). Qed.
Lemma lem5486462 : term214 = term220.
Proof. exact (@lem5486451 (@lem5486461)). Qed.
Lemma lem5486464 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486465 : term173 = term174.
Proof. exact (@lem5486464 term144 term144). Qed.
Lemma lem5486466 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486467 : term176 = term144.
Proof. exact (EQ_MP (@lem5486466) (@lem940073)). Qed.
Lemma lem5486468 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486469 : term174 = term143.
Proof. exact (MK_COMB (@lem5486468) (@lem5486467)). Qed.
Lemma lem5486470 : term173 = term143.
Proof. exact (TRANS (@lem5486465) (@lem5486469)). Qed.
Lemma lem5486472 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486473 : term222 = term129.
Proof. exact (@lem5486472 term144). Qed.
Lemma lem5486474 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486475 : term223 = term212.
Proof. exact (MK_COMB (@lem5486474) (@lem5486473)). Qed.
Lemma lem5486476 : term220 = term211.
Proof. exact (MK_COMB (@lem5486475) (@lem5486470)). Qed.
Lemma lem5486478 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486479 : term211 = term217.
Proof. exact (@lem5486478 (NUMERAL 0) term144). Qed.
Lemma lem5486480 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486481 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486482 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486481 h1) (fun h1 : term217 = True => @lem5486480)). Qed.
Lemma lem5486483 : term217 = True.
Proof. exact (EQ_MP (@lem5486482) (@lem5486480)). Qed.
Lemma lem5486484 : term211 = True.
Proof. exact (TRANS (@lem5486479) (@lem5486483)). Qed.
Lemma lem5486485 : term220 = True.
Proof. exact (TRANS (@lem5486476) (@lem5486484)). Qed.
Lemma lem5486486 : term214 = True.
Proof. exact (TRANS (@lem5486462) (@lem5486485)). Qed.
Lemma lem5486487 : term211 = True.
Proof. exact (TRANS (@lem5486439) (@lem5486486)). Qed.
Lemma lem5486488 : term210 = True.
Proof. exact (TRANS (@lem5486430) (@lem5486487)). Qed.
Lemma lem5486489 : True = term210.
Proof. exact (SYM (@lem5486488)). Qed.
Lemma lem5486490 : term210.
Proof. exact (EQ_MP (@lem5486489) (@lem0)). Qed.
Lemma lem5486491 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term271 _70608.
Proof. exact (conj (@lem5486490) (@lem5486352 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486493 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5486494 (_70608 : int) : term272 _70608.
Proof. exact (@lem5486493 term143 (term201 _70608)). Qed.
Lemma lem5486495 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term273 _70608.
Proof. exact (@lem5486494 _70608 (@lem5486491 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486496 (_70608 : int) : (term274 _70608) = (term201 _70608).
Proof. exact (@lem1982733 (term201 _70608)). Qed.
Lemma lem5486497 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486498 (_70608 : int) : (term275 _70608) = (term269 _70608).
Proof. exact (MK_COMB (@lem5486497) (@lem5486496 _70608)). Qed.
Lemma lem5486499 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486500 (_70608 : int) : (term273 _70608) = (term270 _70608).
Proof. exact (MK_COMB (@lem5486498 _70608) (@lem5486499)). Qed.
Lemma lem5486501 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term270 _70608.
Proof. exact (EQ_MP (@lem5486500 _70608) (@lem5486495 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486502 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term276 _70608.
Proof. exact (conj (@lem5486501 _70606 _70607 _70608 h1) (@lem5486427 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486504 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5486505 (_70608 : int) : term278 _70608.
Proof. exact (@lem5486504 (term201 _70608) (real_of_int _70608)). Qed.
Lemma lem5486506 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term279 _70608.
Proof. exact (@lem5486505 _70608 (@lem5486502 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486507 (_70608 : int) : (term280 _70608) = (term281 _70608).
Proof. exact (@lem1982759 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5486508 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5486510 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486511 : term143 = term191.
Proof. exact (@lem5486510 term144). Qed.
Lemma lem5486513 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5486514 : term164 = term165.
Proof. exact (@lem5486513 term144). Qed.
Lemma lem5486515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486516 : term248 = term249.
Proof. exact (MK_COMB (@lem5486515) (@lem5486514)). Qed.
Lemma lem5486517 : term250 = term251.
Proof. exact (MK_COMB (@lem5486516) (@lem5486511)). Qed.
Lemma lem5486518 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5486520 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486521 : term211 = term217.
Proof. exact (@lem5486520 (NUMERAL 0) term144). Qed.
Lemma lem5486522 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486523 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486524 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486523 h1) (fun h1 : term217 = True => @lem5486522)). Qed.
Lemma lem5486525 : term217 = True.
Proof. exact (EQ_MP (@lem5486524) (@lem5486522)). Qed.
Lemma lem5486526 : term211 = True.
Proof. exact (TRANS (@lem5486521) (@lem5486525)). Qed.
Lemma lem5486527 : True = term211.
Proof. exact (SYM (@lem5486526)). Qed.
Lemma lem5486528 : term211.
Proof. exact (EQ_MP (@lem5486527) (@lem0)). Qed.
Lemma lem5486529 : term253.
Proof. exact (@lem5486518 (@lem5486528)). Qed.
Lemma lem5486531 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486532 : term211 = term217.
Proof. exact (@lem5486531 (NUMERAL 0) term144). Qed.
Lemma lem5486533 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486534 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486535 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486534 h1) (fun h1 : term217 = True => @lem5486533)). Qed.
Lemma lem5486536 : term217 = True.
Proof. exact (EQ_MP (@lem5486535) (@lem5486533)). Qed.
Lemma lem5486537 : term211 = True.
Proof. exact (TRANS (@lem5486532) (@lem5486536)). Qed.
Lemma lem5486538 : True = term211.
Proof. exact (SYM (@lem5486537)). Qed.
Lemma lem5486539 : term211.
Proof. exact (EQ_MP (@lem5486538) (@lem0)). Qed.
Lemma lem5486540 : term254.
Proof. exact (@lem5486529 (@lem5486539)). Qed.
Lemma lem5486542 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486543 : term211 = term217.
Proof. exact (@lem5486542 (NUMERAL 0) term144). Qed.
Lemma lem5486544 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486545 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486546 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486545 h1) (fun h1 : term217 = True => @lem5486544)). Qed.
Lemma lem5486547 : term217 = True.
Proof. exact (EQ_MP (@lem5486546) (@lem5486544)). Qed.
Lemma lem5486548 : term211 = True.
Proof. exact (TRANS (@lem5486543) (@lem5486547)). Qed.
Lemma lem5486549 : True = term211.
Proof. exact (SYM (@lem5486548)). Qed.
Lemma lem5486550 : term211.
Proof. exact (EQ_MP (@lem5486549) (@lem0)). Qed.
Lemma lem5486551 : term255.
Proof. exact (@lem5486540 (@lem5486550)). Qed.
Lemma lem5486553 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486554 : term173 = term174.
Proof. exact (@lem5486553 term144 term144). Qed.
Lemma lem5486555 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486556 : term176 = term144.
Proof. exact (EQ_MP (@lem5486555) (@lem940073)). Qed.
Lemma lem5486557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486558 : term174 = term143.
Proof. exact (MK_COMB (@lem5486557) (@lem5486556)). Qed.
Lemma lem5486559 : term173 = term143.
Proof. exact (TRANS (@lem5486554) (@lem5486558)). Qed.
Lemma lem5486561 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5486562 : term192 = term197.
Proof. exact (@lem5486561 term144 term144). Qed.
Lemma lem5486563 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486564 : term176 = term144.
Proof. exact (EQ_MP (@lem5486563) (@lem940073)). Qed.
Lemma lem5486565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486566 : term174 = term143.
Proof. exact (MK_COMB (@lem5486565) (@lem5486564)). Qed.
Lemma lem5486567 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5486568 : term197 = term164.
Proof. exact (MK_COMB (@lem5486567) (@lem5486566)). Qed.
Lemma lem5486569 : term192 = term164.
Proof. exact (TRANS (@lem5486562) (@lem5486568)). Qed.
Lemma lem5486570 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486571 : term256 = term248.
Proof. exact (MK_COMB (@lem5486570) (@lem5486569)). Qed.
Lemma lem5486572 : term257 = term250.
Proof. exact (MK_COMB (@lem5486571) (@lem5486559)). Qed.
Lemma lem5486574 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5486575 : term250 = term129.
Proof. exact (@lem5486574 term144). Qed.
Lemma lem5486576 : term257 = term129.
Proof. exact (TRANS (@lem5486572) (@lem5486575)). Qed.
Lemma lem5486577 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5486578 : term259 = term260.
Proof. exact (MK_COMB (@lem5486577) (@lem5486576)). Qed.
Lemma lem5486579 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5486580 : term261 = term222.
Proof. exact (MK_COMB (@lem5486578) (@lem5486579)). Qed.
Lemma lem5486582 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486583 : term222 = term129.
Proof. exact (@lem5486582 term144). Qed.
Lemma lem5486584 : term261 = term129.
Proof. exact (TRANS (@lem5486580) (@lem5486583)). Qed.
Lemma lem5486586 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486587 : term173 = term174.
Proof. exact (@lem5486586 term144 term144). Qed.
Lemma lem5486588 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486589 : term176 = term144.
Proof. exact (EQ_MP (@lem5486588) (@lem940073)). Qed.
Lemma lem5486590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486591 : term174 = term143.
Proof. exact (MK_COMB (@lem5486590) (@lem5486589)). Qed.
Lemma lem5486592 : term173 = term143.
Proof. exact (TRANS (@lem5486587) (@lem5486591)). Qed.
Lemma lem5486593 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5486594 : term262 = term222.
Proof. exact (MK_COMB (@lem5486593) (@lem5486592)). Qed.
Lemma lem5486596 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486597 : term222 = term129.
Proof. exact (@lem5486596 term144). Qed.
Lemma lem5486598 : term262 = term129.
Proof. exact (TRANS (@lem5486594) (@lem5486597)). Qed.
Lemma lem5486599 : term129 = term262.
Proof. exact (SYM (@lem5486598)). Qed.
Lemma lem5486600 : term261 = term262.
Proof. exact (TRANS (@lem5486584) (@lem5486599)). Qed.
Lemma lem5486601 : term251 = term161.
Proof. exact (@lem5486551 (@lem5486600)). Qed.
Lemma lem5486602 : term250 = term161.
Proof. exact (TRANS (@lem5486517) (@lem5486601)). Qed.
Lemma lem5486604 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5486605 : term161 = term129.
Proof. exact (@lem5486604 term129). Qed.
Lemma lem5486606 : term250 = term129.
Proof. exact (TRANS (@lem5486602) (@lem5486605)). Qed.
Lemma lem5486607 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5486608 : term263 = term260.
Proof. exact (MK_COMB (@lem5486607) (@lem5486606)). Qed.
Lemma lem5486609 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5486610 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5486608) (@lem5486609 _70608)). Qed.
Lemma lem5486611 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5486508 _70608) (@lem5486610 _70608)). Qed.
Lemma lem5486612 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5486613 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5486611 _70608) (@lem5486612 _70608)). Qed.
Lemma lem5486614 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486615 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5486614) (@lem5486613 _70608)). Qed.
Lemma lem5486616 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5486617 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5486615 _70608) (@lem5486616)). Qed.
Lemma lem5486618 (_70608 : int) : (term280 _70608) = term282.
Proof. exact (TRANS (@lem5486507 _70608) (@lem5486617 _70608)). Qed.
Lemma lem5486619 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5486620 (_70608 : int) : (term280 _70608) = term164.
Proof. exact (TRANS (@lem5486618 _70608) (@lem5486619)). Qed.
Lemma lem5486621 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486622 (_70608 : int) : (term283 _70608) = term284.
Proof. exact (MK_COMB (@lem5486621) (@lem5486620 _70608)). Qed.
Lemma lem5486623 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486624 (_70608 : int) : (term279 _70608) = term285.
Proof. exact (MK_COMB (@lem5486622 _70608) (@lem5486623)). Qed.
Lemma lem5486625 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : term285.
Proof. exact (EQ_MP (@lem5486624 _70608) (@lem5486506 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486627 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5486628 : term285 = term286.
Proof. exact (@lem5486627 term129 term164). Qed.
Lemma lem5486630 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5486631 : term164 = term165.
Proof. exact (@lem5486630 term144). Qed.
Lemma lem5486633 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486634 : term129 = term161.
Proof. exact (@lem5486633 (NUMERAL 0)). Qed.
Lemma lem5486635 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5486636 : term131 = term287.
Proof. exact (MK_COMB (@lem5486635) (@lem5486634)). Qed.
Lemma lem5486637 : term286 = term288.
Proof. exact (MK_COMB (@lem5486636) (@lem5486631)). Qed.
Lemma lem5486638 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5486640 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486641 : term211 = term217.
Proof. exact (@lem5486640 (NUMERAL 0) term144). Qed.
Lemma lem5486642 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486643 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486644 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486643 h1) (fun h1 : term217 = True => @lem5486642)). Qed.
Lemma lem5486645 : term217 = True.
Proof. exact (EQ_MP (@lem5486644) (@lem5486642)). Qed.
Lemma lem5486646 : term211 = True.
Proof. exact (TRANS (@lem5486641) (@lem5486645)). Qed.
Lemma lem5486647 : True = term211.
Proof. exact (SYM (@lem5486646)). Qed.
Lemma lem5486648 : term211.
Proof. exact (EQ_MP (@lem5486647) (@lem0)). Qed.
Lemma lem5486649 : term290.
Proof. exact (@lem5486638 (@lem5486648)). Qed.
Lemma lem5486651 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486652 : term211 = term217.
Proof. exact (@lem5486651 (NUMERAL 0) term144). Qed.
Lemma lem5486653 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486654 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486655 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486654 h1) (fun h1 : term217 = True => @lem5486653)). Qed.
Lemma lem5486656 : term217 = True.
Proof. exact (EQ_MP (@lem5486655) (@lem5486653)). Qed.
Lemma lem5486657 : term211 = True.
Proof. exact (TRANS (@lem5486652) (@lem5486656)). Qed.
Lemma lem5486658 : True = term211.
Proof. exact (SYM (@lem5486657)). Qed.
Lemma lem5486659 : term211.
Proof. exact (EQ_MP (@lem5486658) (@lem0)). Qed.
Lemma lem5486660 : term288 = term291.
Proof. exact (@lem5486649 (@lem5486659)). Qed.
Lemma lem5486662 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5486663 : term192 = term197.
Proof. exact (@lem5486662 term144 term144). Qed.
Lemma lem5486664 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486665 : term176 = term144.
Proof. exact (EQ_MP (@lem5486664) (@lem940073)). Qed.
Lemma lem5486666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486667 : term174 = term143.
Proof. exact (MK_COMB (@lem5486666) (@lem5486665)). Qed.
Lemma lem5486668 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5486669 : term197 = term164.
Proof. exact (MK_COMB (@lem5486668) (@lem5486667)). Qed.
Lemma lem5486670 : term192 = term164.
Proof. exact (TRANS (@lem5486663) (@lem5486669)). Qed.
Lemma lem5486672 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486673 : term222 = term129.
Proof. exact (@lem5486672 term144). Qed.
Lemma lem5486674 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5486675 : term292 = term131.
Proof. exact (MK_COMB (@lem5486674) (@lem5486673)). Qed.
Lemma lem5486676 : term291 = term286.
Proof. exact (MK_COMB (@lem5486675) (@lem5486670)). Qed.
Lemma lem5486678 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5486679 : term286 = term295.
Proof. exact (@lem5486678 (NUMERAL 0) term144). Qed.
Lemma lem5486680 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486681 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5486682 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486681 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5486680)). Qed.
Lemma lem5486683 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5486682) (@lem5486680)). Qed.
Lemma lem5486684 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5486685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5486686 : term296 = (and True).
Proof. exact (MK_COMB (@lem5486685) (@lem5486684)). Qed.
Lemma lem5486687 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5486686) (@lem5486683)). Qed.
Lemma lem5486689 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5486690 : term295 = False.
Proof. exact (TRANS (@lem5486687) (@lem5486689)). Qed.
Lemma lem5486691 : term286 = False.
Proof. exact (TRANS (@lem5486679) (@lem5486690)). Qed.
Lemma lem5486692 : term291 = False.
Proof. exact (TRANS (@lem5486676) (@lem5486691)). Qed.
Lemma lem5486693 : term288 = False.
Proof. exact (TRANS (@lem5486660) (@lem5486692)). Qed.
Lemma lem5486694 : term286 = False.
Proof. exact (TRANS (@lem5486637) (@lem5486693)). Qed.
Lemma lem5486695 : term285 = False.
Proof. exact (TRANS (@lem5486628) (@lem5486694)). Qed.
Lemma lem5486696 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term888 _70606 _70607 _70608) : False.
Proof. exact (EQ_MP (@lem5486695) (@lem5486625 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486697 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term889 _70606 _70607 _70608.
Proof. exact (h1). Qed.
Lemma lem5486698 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term790 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486697 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486700 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term741 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486698 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486702 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term692 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486700 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486703 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term184 _70608.
Proof. exact (proj1 (@lem5486700 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486704 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term645 _70606 _70607 _70608.
Proof. exact (proj2 (@lem5486702 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486706 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term613 _70607 _70608.
Proof. exact (proj2 (@lem5486704 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486710 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term270 _70608.
Proof. exact (proj2 (@lem5486706 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486713 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5486714 : term210 = term211.
Proof. exact (@lem5486713 term129 term143). Qed.
Lemma lem5486716 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486717 : term143 = term191.
Proof. exact (@lem5486716 term144). Qed.
Lemma lem5486719 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486720 : term129 = term161.
Proof. exact (@lem5486719 (NUMERAL 0)). Qed.
Lemma lem5486721 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486722 : term212 = term213.
Proof. exact (MK_COMB (@lem5486721) (@lem5486720)). Qed.
Lemma lem5486723 : term211 = term214.
Proof. exact (MK_COMB (@lem5486722) (@lem5486717)). Qed.
Lemma lem5486724 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5486726 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486727 : term211 = term217.
Proof. exact (@lem5486726 (NUMERAL 0) term144). Qed.
Lemma lem5486728 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486729 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486730 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486729 h1) (fun h1 : term217 = True => @lem5486728)). Qed.
Lemma lem5486731 : term217 = True.
Proof. exact (EQ_MP (@lem5486730) (@lem5486728)). Qed.
Lemma lem5486732 : term211 = True.
Proof. exact (TRANS (@lem5486727) (@lem5486731)). Qed.
Lemma lem5486733 : True = term211.
Proof. exact (SYM (@lem5486732)). Qed.
Lemma lem5486734 : term211.
Proof. exact (EQ_MP (@lem5486733) (@lem0)). Qed.
Lemma lem5486735 : term219.
Proof. exact (@lem5486724 (@lem5486734)). Qed.
Lemma lem5486737 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486738 : term211 = term217.
Proof. exact (@lem5486737 (NUMERAL 0) term144). Qed.
Lemma lem5486739 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486740 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486741 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486740 h1) (fun h1 : term217 = True => @lem5486739)). Qed.
Lemma lem5486742 : term217 = True.
Proof. exact (EQ_MP (@lem5486741) (@lem5486739)). Qed.
Lemma lem5486743 : term211 = True.
Proof. exact (TRANS (@lem5486738) (@lem5486742)). Qed.
Lemma lem5486744 : True = term211.
Proof. exact (SYM (@lem5486743)). Qed.
Lemma lem5486745 : term211.
Proof. exact (EQ_MP (@lem5486744) (@lem0)). Qed.
Lemma lem5486746 : term214 = term220.
Proof. exact (@lem5486735 (@lem5486745)). Qed.
Lemma lem5486748 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486749 : term173 = term174.
Proof. exact (@lem5486748 term144 term144). Qed.
Lemma lem5486750 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486751 : term176 = term144.
Proof. exact (EQ_MP (@lem5486750) (@lem940073)). Qed.
Lemma lem5486752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486753 : term174 = term143.
Proof. exact (MK_COMB (@lem5486752) (@lem5486751)). Qed.
Lemma lem5486754 : term173 = term143.
Proof. exact (TRANS (@lem5486749) (@lem5486753)). Qed.
Lemma lem5486756 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486757 : term222 = term129.
Proof. exact (@lem5486756 term144). Qed.
Lemma lem5486758 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486759 : term223 = term212.
Proof. exact (MK_COMB (@lem5486758) (@lem5486757)). Qed.
Lemma lem5486760 : term220 = term211.
Proof. exact (MK_COMB (@lem5486759) (@lem5486754)). Qed.
Lemma lem5486762 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486763 : term211 = term217.
Proof. exact (@lem5486762 (NUMERAL 0) term144). Qed.
Lemma lem5486764 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486765 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486766 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486765 h1) (fun h1 : term217 = True => @lem5486764)). Qed.
Lemma lem5486767 : term217 = True.
Proof. exact (EQ_MP (@lem5486766) (@lem5486764)). Qed.
Lemma lem5486768 : term211 = True.
Proof. exact (TRANS (@lem5486763) (@lem5486767)). Qed.
Lemma lem5486769 : term220 = True.
Proof. exact (TRANS (@lem5486760) (@lem5486768)). Qed.
Lemma lem5486770 : term214 = True.
Proof. exact (TRANS (@lem5486746) (@lem5486769)). Qed.
Lemma lem5486771 : term211 = True.
Proof. exact (TRANS (@lem5486723) (@lem5486770)). Qed.
Lemma lem5486772 : term210 = True.
Proof. exact (TRANS (@lem5486714) (@lem5486771)). Qed.
Lemma lem5486773 : True = term210.
Proof. exact (SYM (@lem5486772)). Qed.
Lemma lem5486774 : term210.
Proof. exact (EQ_MP (@lem5486773) (@lem0)). Qed.
Lemma lem5486775 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term224 _70608.
Proof. exact (conj (@lem5486774) (@lem5486703 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486777 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5486778 (_70608 : int) : term226 _70608.
Proof. exact (@lem5486777 term143 (real_of_int _70608)). Qed.
Lemma lem5486779 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term227 _70608.
Proof. exact (@lem5486778 _70608 (@lem5486775 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486780 (_70608 : int) : (term228 _70608) = (real_of_int _70608).
Proof. exact (@lem1982733 (real_of_int _70608)). Qed.
Lemma lem5486781 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486782 (_70608 : int) : (term229 _70608) = (term183 _70608).
Proof. exact (MK_COMB (@lem5486781) (@lem5486780 _70608)). Qed.
Lemma lem5486783 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486784 (_70608 : int) : (term227 _70608) = (term184 _70608).
Proof. exact (MK_COMB (@lem5486782 _70608) (@lem5486783)). Qed.
Lemma lem5486785 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term184 _70608.
Proof. exact (EQ_MP (@lem5486784 _70608) (@lem5486779 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486787 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5486788 : term210 = term211.
Proof. exact (@lem5486787 term129 term143). Qed.
Lemma lem5486790 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486791 : term143 = term191.
Proof. exact (@lem5486790 term144). Qed.
Lemma lem5486793 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486794 : term129 = term161.
Proof. exact (@lem5486793 (NUMERAL 0)). Qed.
Lemma lem5486795 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486796 : term212 = term213.
Proof. exact (MK_COMB (@lem5486795) (@lem5486794)). Qed.
Lemma lem5486797 : term211 = term214.
Proof. exact (MK_COMB (@lem5486796) (@lem5486791)). Qed.
Lemma lem5486798 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5486800 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486801 : term211 = term217.
Proof. exact (@lem5486800 (NUMERAL 0) term144). Qed.
Lemma lem5486802 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486803 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486804 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486803 h1) (fun h1 : term217 = True => @lem5486802)). Qed.
Lemma lem5486805 : term217 = True.
Proof. exact (EQ_MP (@lem5486804) (@lem5486802)). Qed.
Lemma lem5486806 : term211 = True.
Proof. exact (TRANS (@lem5486801) (@lem5486805)). Qed.
Lemma lem5486807 : True = term211.
Proof. exact (SYM (@lem5486806)). Qed.
Lemma lem5486808 : term211.
Proof. exact (EQ_MP (@lem5486807) (@lem0)). Qed.
Lemma lem5486809 : term219.
Proof. exact (@lem5486798 (@lem5486808)). Qed.
Lemma lem5486811 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486812 : term211 = term217.
Proof. exact (@lem5486811 (NUMERAL 0) term144). Qed.
Lemma lem5486813 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486814 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486815 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486814 h1) (fun h1 : term217 = True => @lem5486813)). Qed.
Lemma lem5486816 : term217 = True.
Proof. exact (EQ_MP (@lem5486815) (@lem5486813)). Qed.
Lemma lem5486817 : term211 = True.
Proof. exact (TRANS (@lem5486812) (@lem5486816)). Qed.
Lemma lem5486818 : True = term211.
Proof. exact (SYM (@lem5486817)). Qed.
Lemma lem5486819 : term211.
Proof. exact (EQ_MP (@lem5486818) (@lem0)). Qed.
Lemma lem5486820 : term214 = term220.
Proof. exact (@lem5486809 (@lem5486819)). Qed.
Lemma lem5486822 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486823 : term173 = term174.
Proof. exact (@lem5486822 term144 term144). Qed.
Lemma lem5486824 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486825 : term176 = term144.
Proof. exact (EQ_MP (@lem5486824) (@lem940073)). Qed.
Lemma lem5486826 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486827 : term174 = term143.
Proof. exact (MK_COMB (@lem5486826) (@lem5486825)). Qed.
Lemma lem5486828 : term173 = term143.
Proof. exact (TRANS (@lem5486823) (@lem5486827)). Qed.
Lemma lem5486830 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486831 : term222 = term129.
Proof. exact (@lem5486830 term144). Qed.
Lemma lem5486832 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5486833 : term223 = term212.
Proof. exact (MK_COMB (@lem5486832) (@lem5486831)). Qed.
Lemma lem5486834 : term220 = term211.
Proof. exact (MK_COMB (@lem5486833) (@lem5486828)). Qed.
Lemma lem5486836 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486837 : term211 = term217.
Proof. exact (@lem5486836 (NUMERAL 0) term144). Qed.
Lemma lem5486838 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486839 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486840 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486839 h1) (fun h1 : term217 = True => @lem5486838)). Qed.
Lemma lem5486841 : term217 = True.
Proof. exact (EQ_MP (@lem5486840) (@lem5486838)). Qed.
Lemma lem5486842 : term211 = True.
Proof. exact (TRANS (@lem5486837) (@lem5486841)). Qed.
Lemma lem5486843 : term220 = True.
Proof. exact (TRANS (@lem5486834) (@lem5486842)). Qed.
Lemma lem5486844 : term214 = True.
Proof. exact (TRANS (@lem5486820) (@lem5486843)). Qed.
Lemma lem5486845 : term211 = True.
Proof. exact (TRANS (@lem5486797) (@lem5486844)). Qed.
Lemma lem5486846 : term210 = True.
Proof. exact (TRANS (@lem5486788) (@lem5486845)). Qed.
Lemma lem5486847 : True = term210.
Proof. exact (SYM (@lem5486846)). Qed.
Lemma lem5486848 : term210.
Proof. exact (EQ_MP (@lem5486847) (@lem0)). Qed.
Lemma lem5486849 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term271 _70608.
Proof. exact (conj (@lem5486848) (@lem5486710 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486851 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5486852 (_70608 : int) : term272 _70608.
Proof. exact (@lem5486851 term143 (term201 _70608)). Qed.
Lemma lem5486853 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term273 _70608.
Proof. exact (@lem5486852 _70608 (@lem5486849 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486854 (_70608 : int) : (term274 _70608) = (term201 _70608).
Proof. exact (@lem1982733 (term201 _70608)). Qed.
Lemma lem5486855 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486856 (_70608 : int) : (term275 _70608) = (term269 _70608).
Proof. exact (MK_COMB (@lem5486855) (@lem5486854 _70608)). Qed.
Lemma lem5486857 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486858 (_70608 : int) : (term273 _70608) = (term270 _70608).
Proof. exact (MK_COMB (@lem5486856 _70608) (@lem5486857)). Qed.
Lemma lem5486859 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term270 _70608.
Proof. exact (EQ_MP (@lem5486858 _70608) (@lem5486853 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486860 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term276 _70608.
Proof. exact (conj (@lem5486859 _70606 _70607 _70608 h1) (@lem5486785 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486862 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5486863 (_70608 : int) : term278 _70608.
Proof. exact (@lem5486862 (term201 _70608) (real_of_int _70608)). Qed.
Lemma lem5486864 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term279 _70608.
Proof. exact (@lem5486863 _70608 (@lem5486860 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486865 (_70608 : int) : (term280 _70608) = (term281 _70608).
Proof. exact (@lem1982759 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5486866 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5486868 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486869 : term143 = term191.
Proof. exact (@lem5486868 term144). Qed.
Lemma lem5486871 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5486872 : term164 = term165.
Proof. exact (@lem5486871 term144). Qed.
Lemma lem5486873 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486874 : term248 = term249.
Proof. exact (MK_COMB (@lem5486873) (@lem5486872)). Qed.
Lemma lem5486875 : term250 = term251.
Proof. exact (MK_COMB (@lem5486874) (@lem5486869)). Qed.
Lemma lem5486876 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5486878 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486879 : term211 = term217.
Proof. exact (@lem5486878 (NUMERAL 0) term144). Qed.
Lemma lem5486880 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486881 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486882 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486881 h1) (fun h1 : term217 = True => @lem5486880)). Qed.
Lemma lem5486883 : term217 = True.
Proof. exact (EQ_MP (@lem5486882) (@lem5486880)). Qed.
Lemma lem5486884 : term211 = True.
Proof. exact (TRANS (@lem5486879) (@lem5486883)). Qed.
Lemma lem5486885 : True = term211.
Proof. exact (SYM (@lem5486884)). Qed.
Lemma lem5486886 : term211.
Proof. exact (EQ_MP (@lem5486885) (@lem0)). Qed.
Lemma lem5486887 : term253.
Proof. exact (@lem5486876 (@lem5486886)). Qed.
Lemma lem5486889 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486890 : term211 = term217.
Proof. exact (@lem5486889 (NUMERAL 0) term144). Qed.
Lemma lem5486891 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486892 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486893 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486892 h1) (fun h1 : term217 = True => @lem5486891)). Qed.
Lemma lem5486894 : term217 = True.
Proof. exact (EQ_MP (@lem5486893) (@lem5486891)). Qed.
Lemma lem5486895 : term211 = True.
Proof. exact (TRANS (@lem5486890) (@lem5486894)). Qed.
Lemma lem5486896 : True = term211.
Proof. exact (SYM (@lem5486895)). Qed.
Lemma lem5486897 : term211.
Proof. exact (EQ_MP (@lem5486896) (@lem0)). Qed.
Lemma lem5486898 : term254.
Proof. exact (@lem5486887 (@lem5486897)). Qed.
Lemma lem5486900 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486901 : term211 = term217.
Proof. exact (@lem5486900 (NUMERAL 0) term144). Qed.
Lemma lem5486902 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5486903 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5486904 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5486903 h1) (fun h1 : term217 = True => @lem5486902)). Qed.
Lemma lem5486905 : term217 = True.
Proof. exact (EQ_MP (@lem5486904) (@lem5486902)). Qed.
Lemma lem5486906 : term211 = True.
Proof. exact (TRANS (@lem5486901) (@lem5486905)). Qed.
Lemma lem5486907 : True = term211.
Proof. exact (SYM (@lem5486906)). Qed.
Lemma lem5486908 : term211.
Proof. exact (EQ_MP (@lem5486907) (@lem0)). Qed.
Lemma lem5486909 : term255.
Proof. exact (@lem5486898 (@lem5486908)). Qed.
Lemma lem5486911 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486912 : term173 = term174.
Proof. exact (@lem5486911 term144 term144). Qed.
Lemma lem5486913 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486914 : term176 = term144.
Proof. exact (EQ_MP (@lem5486913) (@lem940073)). Qed.
Lemma lem5486915 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486916 : term174 = term143.
Proof. exact (MK_COMB (@lem5486915) (@lem5486914)). Qed.
Lemma lem5486917 : term173 = term143.
Proof. exact (TRANS (@lem5486912) (@lem5486916)). Qed.
Lemma lem5486919 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5486920 : term192 = term197.
Proof. exact (@lem5486919 term144 term144). Qed.
Lemma lem5486921 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486922 : term176 = term144.
Proof. exact (EQ_MP (@lem5486921) (@lem940073)). Qed.
Lemma lem5486923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486924 : term174 = term143.
Proof. exact (MK_COMB (@lem5486923) (@lem5486922)). Qed.
Lemma lem5486925 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5486926 : term197 = term164.
Proof. exact (MK_COMB (@lem5486925) (@lem5486924)). Qed.
Lemma lem5486927 : term192 = term164.
Proof. exact (TRANS (@lem5486920) (@lem5486926)). Qed.
Lemma lem5486928 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486929 : term256 = term248.
Proof. exact (MK_COMB (@lem5486928) (@lem5486927)). Qed.
Lemma lem5486930 : term257 = term250.
Proof. exact (MK_COMB (@lem5486929) (@lem5486917)). Qed.
Lemma lem5486932 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5486933 : term250 = term129.
Proof. exact (@lem5486932 term144). Qed.
Lemma lem5486934 : term257 = term129.
Proof. exact (TRANS (@lem5486930) (@lem5486933)). Qed.
Lemma lem5486935 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5486936 : term259 = term260.
Proof. exact (MK_COMB (@lem5486935) (@lem5486934)). Qed.
Lemma lem5486937 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5486938 : term261 = term222.
Proof. exact (MK_COMB (@lem5486936) (@lem5486937)). Qed.
Lemma lem5486940 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486941 : term222 = term129.
Proof. exact (@lem5486940 term144). Qed.
Lemma lem5486942 : term261 = term129.
Proof. exact (TRANS (@lem5486938) (@lem5486941)). Qed.
Lemma lem5486944 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5486945 : term173 = term174.
Proof. exact (@lem5486944 term144 term144). Qed.
Lemma lem5486946 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5486947 : term176 = term144.
Proof. exact (EQ_MP (@lem5486946) (@lem940073)). Qed.
Lemma lem5486948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5486949 : term174 = term143.
Proof. exact (MK_COMB (@lem5486948) (@lem5486947)). Qed.
Lemma lem5486950 : term173 = term143.
Proof. exact (TRANS (@lem5486945) (@lem5486949)). Qed.
Lemma lem5486951 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5486952 : term262 = term222.
Proof. exact (MK_COMB (@lem5486951) (@lem5486950)). Qed.
Lemma lem5486954 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5486955 : term222 = term129.
Proof. exact (@lem5486954 term144). Qed.
Lemma lem5486956 : term262 = term129.
Proof. exact (TRANS (@lem5486952) (@lem5486955)). Qed.
Lemma lem5486957 : term129 = term262.
Proof. exact (SYM (@lem5486956)). Qed.
Lemma lem5486958 : term261 = term262.
Proof. exact (TRANS (@lem5486942) (@lem5486957)). Qed.
Lemma lem5486959 : term251 = term161.
Proof. exact (@lem5486909 (@lem5486958)). Qed.
Lemma lem5486960 : term250 = term161.
Proof. exact (TRANS (@lem5486875) (@lem5486959)). Qed.
Lemma lem5486962 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5486963 : term161 = term129.
Proof. exact (@lem5486962 term129). Qed.
Lemma lem5486964 : term250 = term129.
Proof. exact (TRANS (@lem5486960) (@lem5486963)). Qed.
Lemma lem5486965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5486966 : term263 = term260.
Proof. exact (MK_COMB (@lem5486965) (@lem5486964)). Qed.
Lemma lem5486967 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5486968 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5486966) (@lem5486967 _70608)). Qed.
Lemma lem5486969 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5486866 _70608) (@lem5486968 _70608)). Qed.
Lemma lem5486970 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5486971 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5486969 _70608) (@lem5486970 _70608)). Qed.
Lemma lem5486972 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5486973 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5486972) (@lem5486971 _70608)). Qed.
Lemma lem5486974 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5486975 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5486973 _70608) (@lem5486974)). Qed.
Lemma lem5486976 (_70608 : int) : (term280 _70608) = term282.
Proof. exact (TRANS (@lem5486865 _70608) (@lem5486975 _70608)). Qed.
Lemma lem5486977 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5486978 (_70608 : int) : (term280 _70608) = term164.
Proof. exact (TRANS (@lem5486976 _70608) (@lem5486977)). Qed.
Lemma lem5486979 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5486980 (_70608 : int) : (term283 _70608) = term284.
Proof. exact (MK_COMB (@lem5486979) (@lem5486978 _70608)). Qed.
Lemma lem5486981 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5486982 (_70608 : int) : (term279 _70608) = term285.
Proof. exact (MK_COMB (@lem5486980 _70608) (@lem5486981)). Qed.
Lemma lem5486983 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : term285.
Proof. exact (EQ_MP (@lem5486982 _70608) (@lem5486864 _70606 _70607 _70608 h1)). Qed.
Lemma lem5486985 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5486986 : term285 = term286.
Proof. exact (@lem5486985 term129 term164). Qed.
Lemma lem5486988 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5486989 : term164 = term165.
Proof. exact (@lem5486988 term144). Qed.
Lemma lem5486991 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5486992 : term129 = term161.
Proof. exact (@lem5486991 (NUMERAL 0)). Qed.
Lemma lem5486993 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5486994 : term131 = term287.
Proof. exact (MK_COMB (@lem5486993) (@lem5486992)). Qed.
Lemma lem5486995 : term286 = term288.
Proof. exact (MK_COMB (@lem5486994) (@lem5486989)). Qed.
Lemma lem5486996 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5486998 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5486999 : term211 = term217.
Proof. exact (@lem5486998 (NUMERAL 0) term144). Qed.
Lemma lem5487000 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487001 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487002 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487001 h1) (fun h1 : term217 = True => @lem5487000)). Qed.
Lemma lem5487003 : term217 = True.
Proof. exact (EQ_MP (@lem5487002) (@lem5487000)). Qed.
Lemma lem5487004 : term211 = True.
Proof. exact (TRANS (@lem5486999) (@lem5487003)). Qed.
Lemma lem5487005 : True = term211.
Proof. exact (SYM (@lem5487004)). Qed.
Lemma lem5487006 : term211.
Proof. exact (EQ_MP (@lem5487005) (@lem0)). Qed.
Lemma lem5487007 : term290.
Proof. exact (@lem5486996 (@lem5487006)). Qed.
Lemma lem5487009 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487010 : term211 = term217.
Proof. exact (@lem5487009 (NUMERAL 0) term144). Qed.
Lemma lem5487011 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487012 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487013 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487012 h1) (fun h1 : term217 = True => @lem5487011)). Qed.
Lemma lem5487014 : term217 = True.
Proof. exact (EQ_MP (@lem5487013) (@lem5487011)). Qed.
Lemma lem5487015 : term211 = True.
Proof. exact (TRANS (@lem5487010) (@lem5487014)). Qed.
Lemma lem5487016 : True = term211.
Proof. exact (SYM (@lem5487015)). Qed.
Lemma lem5487017 : term211.
Proof. exact (EQ_MP (@lem5487016) (@lem0)). Qed.
Lemma lem5487018 : term288 = term291.
Proof. exact (@lem5487007 (@lem5487017)). Qed.
Lemma lem5487020 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5487021 : term192 = term197.
Proof. exact (@lem5487020 term144 term144). Qed.
Lemma lem5487022 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487023 : term176 = term144.
Proof. exact (EQ_MP (@lem5487022) (@lem940073)). Qed.
Lemma lem5487024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487025 : term174 = term143.
Proof. exact (MK_COMB (@lem5487024) (@lem5487023)). Qed.
Lemma lem5487026 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5487027 : term197 = term164.
Proof. exact (MK_COMB (@lem5487026) (@lem5487025)). Qed.
Lemma lem5487028 : term192 = term164.
Proof. exact (TRANS (@lem5487021) (@lem5487027)). Qed.
Lemma lem5487030 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487031 : term222 = term129.
Proof. exact (@lem5487030 term144). Qed.
Lemma lem5487032 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5487033 : term292 = term131.
Proof. exact (MK_COMB (@lem5487032) (@lem5487031)). Qed.
Lemma lem5487034 : term291 = term286.
Proof. exact (MK_COMB (@lem5487033) (@lem5487028)). Qed.
Lemma lem5487036 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5487037 : term286 = term295.
Proof. exact (@lem5487036 (NUMERAL 0) term144). Qed.
Lemma lem5487038 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487039 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5487040 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487039 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5487038)). Qed.
Lemma lem5487041 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5487040) (@lem5487038)). Qed.
Lemma lem5487042 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5487043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5487044 : term296 = (and True).
Proof. exact (MK_COMB (@lem5487043) (@lem5487042)). Qed.
Lemma lem5487045 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5487044) (@lem5487041)). Qed.
Lemma lem5487047 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5487048 : term295 = False.
Proof. exact (TRANS (@lem5487045) (@lem5487047)). Qed.
Lemma lem5487049 : term286 = False.
Proof. exact (TRANS (@lem5487037) (@lem5487048)). Qed.
Lemma lem5487050 : term291 = False.
Proof. exact (TRANS (@lem5487034) (@lem5487049)). Qed.
Lemma lem5487051 : term288 = False.
Proof. exact (TRANS (@lem5487018) (@lem5487050)). Qed.
Lemma lem5487052 : term286 = False.
Proof. exact (TRANS (@lem5486995) (@lem5487051)). Qed.
Lemma lem5487053 : term285 = False.
Proof. exact (TRANS (@lem5486986) (@lem5487052)). Qed.
Lemma lem5487054 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term889 _70606 _70607 _70608) : False.
Proof. exact (EQ_MP (@lem5487053) (@lem5486983 _70606 _70607 _70608 h1)). Qed.
Lemma lem5487055 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term788 _70606 _70607 _70608) : False.
Proof. exact (or_elim (@lem5486338 _70606 _70607 _70608 h1) (fun h0 : term888 _70606 _70607 _70608 => @lem5486696 _70606 _70607 _70608 h0) (fun h0 : term889 _70606 _70607 _70608 => @lem5487054 _70606 _70607 _70608 h0)). Qed.
Lemma lem5487056 (_70606 : int) (_70607 : int) (_70608 : int) (h1 : term797 _70606 _70607 _70608) : False.
Proof. exact (or_elim (@lem5485623 _70606 _70607 _70608 h1) (fun h0 : term792 _70606 _70607 _70608 => @lem5486337 _70606 _70607 _70608 h0) (fun h0 : term788 _70606 _70607 _70608 => @lem5487055 _70606 _70607 _70608 h0)). Qed.
Lemma lem5487057 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term784 _70607 _70606 _70608) : term784 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5487058 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term779 _70607 _70606 _70608) : term779 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5487059 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term890 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5487060 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term780 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487059 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487062 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term731 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487060 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487064 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term682 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487062 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487066 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term633 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487064 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487068 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term614 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487066 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487069 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : (term552 _70606 _70607) = term129.
Proof. exact (proj1 (@lem5487066 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487070 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (proj2 (@lem5487068 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487071 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (proj1 (@lem5487068 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487073 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5487074 : term210 = term211.
Proof. exact (@lem5487073 term129 term143). Qed.
Lemma lem5487076 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487077 : term143 = term191.
Proof. exact (@lem5487076 term144). Qed.
Lemma lem5487079 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487080 : term129 = term161.
Proof. exact (@lem5487079 (NUMERAL 0)). Qed.
Lemma lem5487081 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487082 : term212 = term213.
Proof. exact (MK_COMB (@lem5487081) (@lem5487080)). Qed.
Lemma lem5487083 : term211 = term214.
Proof. exact (MK_COMB (@lem5487082) (@lem5487077)). Qed.
Lemma lem5487084 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5487086 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487087 : term211 = term217.
Proof. exact (@lem5487086 (NUMERAL 0) term144). Qed.
Lemma lem5487088 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487089 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487090 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487089 h1) (fun h1 : term217 = True => @lem5487088)). Qed.
Lemma lem5487091 : term217 = True.
Proof. exact (EQ_MP (@lem5487090) (@lem5487088)). Qed.
Lemma lem5487092 : term211 = True.
Proof. exact (TRANS (@lem5487087) (@lem5487091)). Qed.
Lemma lem5487093 : True = term211.
Proof. exact (SYM (@lem5487092)). Qed.
Lemma lem5487094 : term211.
Proof. exact (EQ_MP (@lem5487093) (@lem0)). Qed.
Lemma lem5487095 : term219.
Proof. exact (@lem5487084 (@lem5487094)). Qed.
Lemma lem5487097 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487098 : term211 = term217.
Proof. exact (@lem5487097 (NUMERAL 0) term144). Qed.
Lemma lem5487099 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487100 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487101 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487100 h1) (fun h1 : term217 = True => @lem5487099)). Qed.
Lemma lem5487102 : term217 = True.
Proof. exact (EQ_MP (@lem5487101) (@lem5487099)). Qed.
Lemma lem5487103 : term211 = True.
Proof. exact (TRANS (@lem5487098) (@lem5487102)). Qed.
Lemma lem5487104 : True = term211.
Proof. exact (SYM (@lem5487103)). Qed.
Lemma lem5487105 : term211.
Proof. exact (EQ_MP (@lem5487104) (@lem0)). Qed.
Lemma lem5487106 : term214 = term220.
Proof. exact (@lem5487095 (@lem5487105)). Qed.
Lemma lem5487108 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487109 : term173 = term174.
Proof. exact (@lem5487108 term144 term144). Qed.
Lemma lem5487110 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487111 : term176 = term144.
Proof. exact (EQ_MP (@lem5487110) (@lem940073)). Qed.
Lemma lem5487112 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487113 : term174 = term143.
Proof. exact (MK_COMB (@lem5487112) (@lem5487111)). Qed.
Lemma lem5487114 : term173 = term143.
Proof. exact (TRANS (@lem5487109) (@lem5487113)). Qed.
Lemma lem5487116 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487117 : term222 = term129.
Proof. exact (@lem5487116 term144). Qed.
Lemma lem5487118 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487119 : term223 = term212.
Proof. exact (MK_COMB (@lem5487118) (@lem5487117)). Qed.
Lemma lem5487120 : term220 = term211.
Proof. exact (MK_COMB (@lem5487119) (@lem5487114)). Qed.
Lemma lem5487122 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487123 : term211 = term217.
Proof. exact (@lem5487122 (NUMERAL 0) term144). Qed.
Lemma lem5487124 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487125 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487126 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487125 h1) (fun h1 : term217 = True => @lem5487124)). Qed.
Lemma lem5487127 : term217 = True.
Proof. exact (EQ_MP (@lem5487126) (@lem5487124)). Qed.
Lemma lem5487128 : term211 = True.
Proof. exact (TRANS (@lem5487123) (@lem5487127)). Qed.
Lemma lem5487129 : term220 = True.
Proof. exact (TRANS (@lem5487120) (@lem5487128)). Qed.
Lemma lem5487130 : term214 = True.
Proof. exact (TRANS (@lem5487106) (@lem5487129)). Qed.
Lemma lem5487131 : term211 = True.
Proof. exact (TRANS (@lem5487083) (@lem5487130)). Qed.
Lemma lem5487132 : term210 = True.
Proof. exact (TRANS (@lem5487074) (@lem5487131)). Qed.
Lemma lem5487133 : True = term210.
Proof. exact (SYM (@lem5487132)). Qed.
Lemma lem5487134 : term210.
Proof. exact (EQ_MP (@lem5487133) (@lem0)). Qed.
Lemma lem5487135 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term840 _70606 _70608.
Proof. exact (conj (@lem5487134) (@lem5487070 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487137 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5487138 (_70606 : int) (_70608 : int) : term841 _70606 _70608.
Proof. exact (@lem5487137 term143 (term552 _70606 _70608)). Qed.
Lemma lem5487139 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term842 _70606 _70608.
Proof. exact (@lem5487138 _70606 _70608 (@lem5487135 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487140 (_70606 : int) (_70608 : int) : (term826 _70606 _70608) = (term552 _70606 _70608).
Proof. exact (@lem1982733 (term552 _70606 _70608)). Qed.
Lemma lem5487141 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5487142 (_70606 : int) (_70608 : int) : (term843 _70606 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5487141) (@lem5487140 _70606 _70608)). Qed.
Lemma lem5487143 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5487144 (_70606 : int) (_70608 : int) : (term842 _70606 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5487142 _70606 _70608) (@lem5487143)). Qed.
Lemma lem5487145 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5487144 _70606 _70608) (@lem5487139 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487147 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5487148 : term210 = term211.
Proof. exact (@lem5487147 term129 term143). Qed.
Lemma lem5487150 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487151 : term143 = term191.
Proof. exact (@lem5487150 term144). Qed.
Lemma lem5487153 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487154 : term129 = term161.
Proof. exact (@lem5487153 (NUMERAL 0)). Qed.
Lemma lem5487155 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487156 : term212 = term213.
Proof. exact (MK_COMB (@lem5487155) (@lem5487154)). Qed.
Lemma lem5487157 : term211 = term214.
Proof. exact (MK_COMB (@lem5487156) (@lem5487151)). Qed.
Lemma lem5487158 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5487160 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487161 : term211 = term217.
Proof. exact (@lem5487160 (NUMERAL 0) term144). Qed.
Lemma lem5487162 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487163 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487164 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487163 h1) (fun h1 : term217 = True => @lem5487162)). Qed.
Lemma lem5487165 : term217 = True.
Proof. exact (EQ_MP (@lem5487164) (@lem5487162)). Qed.
Lemma lem5487166 : term211 = True.
Proof. exact (TRANS (@lem5487161) (@lem5487165)). Qed.
Lemma lem5487167 : True = term211.
Proof. exact (SYM (@lem5487166)). Qed.
Lemma lem5487168 : term211.
Proof. exact (EQ_MP (@lem5487167) (@lem0)). Qed.
Lemma lem5487169 : term219.
Proof. exact (@lem5487158 (@lem5487168)). Qed.
Lemma lem5487171 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487172 : term211 = term217.
Proof. exact (@lem5487171 (NUMERAL 0) term144). Qed.
Lemma lem5487173 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487174 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487175 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487174 h1) (fun h1 : term217 = True => @lem5487173)). Qed.
Lemma lem5487176 : term217 = True.
Proof. exact (EQ_MP (@lem5487175) (@lem5487173)). Qed.
Lemma lem5487177 : term211 = True.
Proof. exact (TRANS (@lem5487172) (@lem5487176)). Qed.
Lemma lem5487178 : True = term211.
Proof. exact (SYM (@lem5487177)). Qed.
Lemma lem5487179 : term211.
Proof. exact (EQ_MP (@lem5487178) (@lem0)). Qed.
Lemma lem5487180 : term214 = term220.
Proof. exact (@lem5487169 (@lem5487179)). Qed.
Lemma lem5487182 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487183 : term173 = term174.
Proof. exact (@lem5487182 term144 term144). Qed.
Lemma lem5487184 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487185 : term176 = term144.
Proof. exact (EQ_MP (@lem5487184) (@lem940073)). Qed.
Lemma lem5487186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487187 : term174 = term143.
Proof. exact (MK_COMB (@lem5487186) (@lem5487185)). Qed.
Lemma lem5487188 : term173 = term143.
Proof. exact (TRANS (@lem5487183) (@lem5487187)). Qed.
Lemma lem5487190 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487191 : term222 = term129.
Proof. exact (@lem5487190 term144). Qed.
Lemma lem5487192 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487193 : term223 = term212.
Proof. exact (MK_COMB (@lem5487192) (@lem5487191)). Qed.
Lemma lem5487194 : term220 = term211.
Proof. exact (MK_COMB (@lem5487193) (@lem5487188)). Qed.
Lemma lem5487196 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487197 : term211 = term217.
Proof. exact (@lem5487196 (NUMERAL 0) term144). Qed.
Lemma lem5487198 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487199 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487200 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487199 h1) (fun h1 : term217 = True => @lem5487198)). Qed.
Lemma lem5487201 : term217 = True.
Proof. exact (EQ_MP (@lem5487200) (@lem5487198)). Qed.
Lemma lem5487202 : term211 = True.
Proof. exact (TRANS (@lem5487197) (@lem5487201)). Qed.
Lemma lem5487203 : term220 = True.
Proof. exact (TRANS (@lem5487194) (@lem5487202)). Qed.
Lemma lem5487204 : term214 = True.
Proof. exact (TRANS (@lem5487180) (@lem5487203)). Qed.
Lemma lem5487205 : term211 = True.
Proof. exact (TRANS (@lem5487157) (@lem5487204)). Qed.
Lemma lem5487206 : term210 = True.
Proof. exact (TRANS (@lem5487148) (@lem5487205)). Qed.
Lemma lem5487207 : True = term210.
Proof. exact (SYM (@lem5487206)). Qed.
Lemma lem5487208 : term210.
Proof. exact (EQ_MP (@lem5487207) (@lem0)). Qed.
Lemma lem5487209 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term230 _70607 _70608.
Proof. exact (conj (@lem5487208) (@lem5487071 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487211 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5487212 (_70607 : int) (_70608 : int) : term231 _70607 _70608.
Proof. exact (@lem5487211 term143 (term202 _70607 _70608)). Qed.
Lemma lem5487213 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term232 _70607 _70608.
Proof. exact (@lem5487212 _70607 _70608 (@lem5487209 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487214 (_70607 : int) (_70608 : int) : (term233 _70607 _70608) = (term202 _70607 _70608).
Proof. exact (@lem1982733 (term202 _70607 _70608)). Qed.
Lemma lem5487215 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5487216 (_70607 : int) (_70608 : int) : (term234 _70607 _70608) = (term204 _70607 _70608).
Proof. exact (MK_COMB (@lem5487215) (@lem5487214 _70607 _70608)). Qed.
Lemma lem5487217 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5487218 (_70607 : int) (_70608 : int) : (term232 _70607 _70608) = (term205 _70607 _70608).
Proof. exact (MK_COMB (@lem5487216 _70607 _70608) (@lem5487217)). Qed.
Lemma lem5487219 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (EQ_MP (@lem5487218 _70607 _70608) (@lem5487213 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487221 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5487222 (_70606 : int) (_70607 : int) : term823 _70606 _70607.
Proof. exact (@lem5487221 (term552 _70606 _70607)). Qed.
Lemma lem5487223 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term824 _70606 _70607.
Proof. exact (@lem5487222 _70606 _70607 (@lem5487069 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487224 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term891 _70606 _70607.
Proof. exact (@lem5487223 _70607 _70606 _70608 h1 term164). Qed.
Lemma lem5487225 (_70606 : int) (_70607 : int) : (term891 _70606 _70607) = ((term892 _70606 _70607) = term129).
Proof. exact (eq_refl (term891 _70606 _70607)). Qed.
Lemma lem5487226 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : (term892 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5487225 _70606 _70607) (@lem5487224 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487227 (_70606 : int) (_70607 : int) : (term892 _70606 _70607) = (term893 _70606 _70607).
Proof. exact (@lem1982781 (term239 _70606) term164 (term546 _70607)). Qed.
Lemma lem5487228 (_70607 : int) : (term894 _70607) = (term895 _70607).
Proof. exact (@lem1982781 (real_of_int _70607) term164 term164). Qed.
Lemma lem5487230 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487231 : term164 = term165.
Proof. exact (@lem5487230 term144). Qed.
Lemma lem5487233 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487234 : term164 = term165.
Proof. exact (@lem5487233 term144). Qed.
Lemma lem5487235 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487236 : term166 = term167.
Proof. exact (MK_COMB (@lem5487235) (@lem5487234)). Qed.
Lemma lem5487237 : term896 = term897.
Proof. exact (MK_COMB (@lem5487236) (@lem5487231)). Qed.
Lemma lem5487238 : term897 = term898.
Proof. exact (@lem1981613 term164 term164 term143 term143). Qed.
Lemma lem5487240 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487241 : term173 = term174.
Proof. exact (@lem5487240 term144 term144). Qed.
Lemma lem5487242 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487243 : term176 = term144.
Proof. exact (EQ_MP (@lem5487242) (@lem940073)). Qed.
Lemma lem5487244 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487245 : term174 = term143.
Proof. exact (MK_COMB (@lem5487244) (@lem5487243)). Qed.
Lemma lem5487246 : term173 = term143.
Proof. exact (TRANS (@lem5487241) (@lem5487245)). Qed.
Lemma lem5487248 (m : nat) (n : nat) : (term899 m n) = (term172 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5487249 : term896 = term174.
Proof. exact (@lem5487248 term144 term144). Qed.
Lemma lem5487250 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487251 : term176 = term144.
Proof. exact (EQ_MP (@lem5487250) (@lem940073)). Qed.
Lemma lem5487252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487253 : term174 = term143.
Proof. exact (MK_COMB (@lem5487252) (@lem5487251)). Qed.
Lemma lem5487254 : term896 = term143.
Proof. exact (TRANS (@lem5487249) (@lem5487253)). Qed.
Lemma lem5487255 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5487256 : term900 = term901.
Proof. exact (MK_COMB (@lem5487255) (@lem5487254)). Qed.
Lemma lem5487257 : term898 = term191.
Proof. exact (MK_COMB (@lem5487256) (@lem5487246)). Qed.
Lemma lem5487258 : term897 = term191.
Proof. exact (TRANS (@lem5487238) (@lem5487257)). Qed.
Lemma lem5487259 : term896 = term191.
Proof. exact (TRANS (@lem5487237) (@lem5487258)). Qed.
Lemma lem5487261 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5487262 : term191 = term143.
Proof. exact (@lem5487261 term143). Qed.
Lemma lem5487263 : term896 = term143.
Proof. exact (TRANS (@lem5487259) (@lem5487262)). Qed.
Lemma lem5487266 (_70607 : int) : (term200 _70607) = (term200 _70607).
Proof. exact (eq_refl (term200 _70607)). Qed.
Lemma lem5487267 (_70607 : int) : (term895 _70607) = (term902 _70607).
Proof. exact (MK_COMB (@lem5487266 _70607) (@lem5487263)). Qed.
Lemma lem5487268 (_70607 : int) : (term894 _70607) = (term902 _70607).
Proof. exact (TRANS (@lem5487228 _70607) (@lem5487267 _70607)). Qed.
Lemma lem5487269 (_70606 : int) : (term903 _70606) = (term904 _70606).
Proof. exact (@lem1982749 term164 term164 (real_of_int _70606)). Qed.
Lemma lem5487271 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487272 : term164 = term165.
Proof. exact (@lem5487271 term144). Qed.
Lemma lem5487274 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487275 : term164 = term165.
Proof. exact (@lem5487274 term144). Qed.
Lemma lem5487276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487277 : term166 = term167.
Proof. exact (MK_COMB (@lem5487276) (@lem5487275)). Qed.
Lemma lem5487278 : term896 = term897.
Proof. exact (MK_COMB (@lem5487277) (@lem5487272)). Qed.
Lemma lem5487279 : term897 = term898.
Proof. exact (@lem1981613 term164 term164 term143 term143). Qed.
Lemma lem5487281 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487282 : term173 = term174.
Proof. exact (@lem5487281 term144 term144). Qed.
Lemma lem5487283 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487284 : term176 = term144.
Proof. exact (EQ_MP (@lem5487283) (@lem940073)). Qed.
Lemma lem5487285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487286 : term174 = term143.
Proof. exact (MK_COMB (@lem5487285) (@lem5487284)). Qed.
Lemma lem5487287 : term173 = term143.
Proof. exact (TRANS (@lem5487282) (@lem5487286)). Qed.
Lemma lem5487289 (m : nat) (n : nat) : (term899 m n) = (term172 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5487290 : term896 = term174.
Proof. exact (@lem5487289 term144 term144). Qed.
Lemma lem5487291 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487292 : term176 = term144.
Proof. exact (EQ_MP (@lem5487291) (@lem940073)). Qed.
Lemma lem5487293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487294 : term174 = term143.
Proof. exact (MK_COMB (@lem5487293) (@lem5487292)). Qed.
Lemma lem5487295 : term896 = term143.
Proof. exact (TRANS (@lem5487290) (@lem5487294)). Qed.
Lemma lem5487296 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5487297 : term900 = term901.
Proof. exact (MK_COMB (@lem5487296) (@lem5487295)). Qed.
Lemma lem5487298 : term898 = term191.
Proof. exact (MK_COMB (@lem5487297) (@lem5487287)). Qed.
Lemma lem5487299 : term897 = term191.
Proof. exact (TRANS (@lem5487279) (@lem5487298)). Qed.
Lemma lem5487300 : term896 = term191.
Proof. exact (TRANS (@lem5487278) (@lem5487299)). Qed.
Lemma lem5487302 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5487303 : term191 = term143.
Proof. exact (@lem5487302 term143). Qed.
Lemma lem5487304 : term896 = term143.
Proof. exact (TRANS (@lem5487300) (@lem5487303)). Qed.
Lemma lem5487305 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487306 : term905 = term906.
Proof. exact (MK_COMB (@lem5487305) (@lem5487304)). Qed.
Lemma lem5487307 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5487308 (_70606 : int) : (term904 _70606) = (term228 _70606).
Proof. exact (MK_COMB (@lem5487306) (@lem5487307 _70606)). Qed.
Lemma lem5487309 (_70606 : int) : (term903 _70606) = (term228 _70606).
Proof. exact (TRANS (@lem5487269 _70606) (@lem5487308 _70606)). Qed.
Lemma lem5487310 (_70606 : int) : (term228 _70606) = (real_of_int _70606).
Proof. exact (@lem1982709 (real_of_int _70606)). Qed.
Lemma lem5487311 (_70606 : int) : (term903 _70606) = (real_of_int _70606).
Proof. exact (TRANS (@lem5487309 _70606) (@lem5487310 _70606)). Qed.
Lemma lem5487312 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487313 (_70606 : int) : (term907 _70606) = (term145 _70606).
Proof. exact (MK_COMB (@lem5487312) (@lem5487311 _70606)). Qed.
Lemma lem5487314 (_70606 : int) (_70607 : int) : (term893 _70606 _70607) = (term908 _70606 _70607).
Proof. exact (MK_COMB (@lem5487313 _70606) (@lem5487268 _70607)). Qed.
Lemma lem5487315 (_70606 : int) (_70607 : int) : (term892 _70606 _70607) = (term908 _70606 _70607).
Proof. exact (TRANS (@lem5487227 _70606 _70607) (@lem5487314 _70606 _70607)). Qed.
Lemma lem5487316 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5487317 (_70606 : int) (_70607 : int) : (term909 _70606 _70607) = (term910 _70606 _70607).
Proof. exact (MK_COMB (@lem5487316) (@lem5487315 _70606 _70607)). Qed.
Lemma lem5487318 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5487319 (_70606 : int) (_70607 : int) : ((term892 _70606 _70607) = term129) = ((term908 _70606 _70607) = term129).
Proof. exact (MK_COMB (@lem5487317 _70606 _70607) (@lem5487318)). Qed.
Lemma lem5487320 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : (term908 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5487319 _70606 _70607) (@lem5487226 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487321 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term911 _70606 _70607 _70608.
Proof. exact (conj (@lem5487320 _70607 _70606 _70608 h1) (@lem5487219 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487323 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5487324 (_70606 : int) (_70607 : int) (_70608 : int) : term912 _70606 _70607 _70608.
Proof. exact (@lem5487323 (term908 _70606 _70607) (term202 _70607 _70608)). Qed.
Lemma lem5487325 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term913 _70606 _70607 _70608.
Proof. exact (@lem5487324 _70606 _70607 _70608 (@lem5487321 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487326 (_70606 : int) (_70607 : int) (_70608 : int) : (term914 _70606 _70607 _70608) = (term915 _70606 _70607 _70608).
Proof. exact (@lem1982755 (real_of_int _70606) (term902 _70607) (term202 _70607 _70608)). Qed.
Lemma lem5487327 (_70607 : int) (_70608 : int) : (term916 _70607 _70608) = (term917 _70607 _70608).
Proof. exact (@lem1982753 (term239 _70607) (real_of_int _70607) term143 (term201 _70608)). Qed.
Lemma lem5487328 (_70607 : int) : (term246 _70607) = (term247 _70607).
Proof. exact (@lem1982713 term164 (real_of_int _70607)). Qed.
Lemma lem5487330 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487331 : term143 = term191.
Proof. exact (@lem5487330 term144). Qed.
Lemma lem5487333 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487334 : term164 = term165.
Proof. exact (@lem5487333 term144). Qed.
Lemma lem5487335 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487336 : term248 = term249.
Proof. exact (MK_COMB (@lem5487335) (@lem5487334)). Qed.
Lemma lem5487337 : term250 = term251.
Proof. exact (MK_COMB (@lem5487336) (@lem5487331)). Qed.
Lemma lem5487338 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5487340 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487341 : term211 = term217.
Proof. exact (@lem5487340 (NUMERAL 0) term144). Qed.
Lemma lem5487342 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487343 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487344 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487343 h1) (fun h1 : term217 = True => @lem5487342)). Qed.
Lemma lem5487345 : term217 = True.
Proof. exact (EQ_MP (@lem5487344) (@lem5487342)). Qed.
Lemma lem5487346 : term211 = True.
Proof. exact (TRANS (@lem5487341) (@lem5487345)). Qed.
Lemma lem5487347 : True = term211.
Proof. exact (SYM (@lem5487346)). Qed.
Lemma lem5487348 : term211.
Proof. exact (EQ_MP (@lem5487347) (@lem0)). Qed.
Lemma lem5487349 : term253.
Proof. exact (@lem5487338 (@lem5487348)). Qed.
Lemma lem5487351 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487352 : term211 = term217.
Proof. exact (@lem5487351 (NUMERAL 0) term144). Qed.
Lemma lem5487353 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487354 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487355 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487354 h1) (fun h1 : term217 = True => @lem5487353)). Qed.
Lemma lem5487356 : term217 = True.
Proof. exact (EQ_MP (@lem5487355) (@lem5487353)). Qed.
Lemma lem5487357 : term211 = True.
Proof. exact (TRANS (@lem5487352) (@lem5487356)). Qed.
Lemma lem5487358 : True = term211.
Proof. exact (SYM (@lem5487357)). Qed.
Lemma lem5487359 : term211.
Proof. exact (EQ_MP (@lem5487358) (@lem0)). Qed.
Lemma lem5487360 : term254.
Proof. exact (@lem5487349 (@lem5487359)). Qed.
Lemma lem5487362 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487363 : term211 = term217.
Proof. exact (@lem5487362 (NUMERAL 0) term144). Qed.
Lemma lem5487364 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487365 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487366 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487365 h1) (fun h1 : term217 = True => @lem5487364)). Qed.
Lemma lem5487367 : term217 = True.
Proof. exact (EQ_MP (@lem5487366) (@lem5487364)). Qed.
Lemma lem5487368 : term211 = True.
Proof. exact (TRANS (@lem5487363) (@lem5487367)). Qed.
Lemma lem5487369 : True = term211.
Proof. exact (SYM (@lem5487368)). Qed.
Lemma lem5487370 : term211.
Proof. exact (EQ_MP (@lem5487369) (@lem0)). Qed.
Lemma lem5487371 : term255.
Proof. exact (@lem5487360 (@lem5487370)). Qed.
Lemma lem5487373 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487374 : term173 = term174.
Proof. exact (@lem5487373 term144 term144). Qed.
Lemma lem5487375 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487376 : term176 = term144.
Proof. exact (EQ_MP (@lem5487375) (@lem940073)). Qed.
Lemma lem5487377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487378 : term174 = term143.
Proof. exact (MK_COMB (@lem5487377) (@lem5487376)). Qed.
Lemma lem5487379 : term173 = term143.
Proof. exact (TRANS (@lem5487374) (@lem5487378)). Qed.
Lemma lem5487381 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5487382 : term192 = term197.
Proof. exact (@lem5487381 term144 term144). Qed.
Lemma lem5487383 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487384 : term176 = term144.
Proof. exact (EQ_MP (@lem5487383) (@lem940073)). Qed.
Lemma lem5487385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487386 : term174 = term143.
Proof. exact (MK_COMB (@lem5487385) (@lem5487384)). Qed.
Lemma lem5487387 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5487388 : term197 = term164.
Proof. exact (MK_COMB (@lem5487387) (@lem5487386)). Qed.
Lemma lem5487389 : term192 = term164.
Proof. exact (TRANS (@lem5487382) (@lem5487388)). Qed.
Lemma lem5487390 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487391 : term256 = term248.
Proof. exact (MK_COMB (@lem5487390) (@lem5487389)). Qed.
Lemma lem5487392 : term257 = term250.
Proof. exact (MK_COMB (@lem5487391) (@lem5487379)). Qed.
Lemma lem5487394 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5487395 : term250 = term129.
Proof. exact (@lem5487394 term144). Qed.
Lemma lem5487396 : term257 = term129.
Proof. exact (TRANS (@lem5487392) (@lem5487395)). Qed.
Lemma lem5487397 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487398 : term259 = term260.
Proof. exact (MK_COMB (@lem5487397) (@lem5487396)). Qed.
Lemma lem5487399 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5487400 : term261 = term222.
Proof. exact (MK_COMB (@lem5487398) (@lem5487399)). Qed.
Lemma lem5487402 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487403 : term222 = term129.
Proof. exact (@lem5487402 term144). Qed.
Lemma lem5487404 : term261 = term129.
Proof. exact (TRANS (@lem5487400) (@lem5487403)). Qed.
Lemma lem5487406 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487407 : term173 = term174.
Proof. exact (@lem5487406 term144 term144). Qed.
Lemma lem5487408 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487409 : term176 = term144.
Proof. exact (EQ_MP (@lem5487408) (@lem940073)). Qed.
Lemma lem5487410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487411 : term174 = term143.
Proof. exact (MK_COMB (@lem5487410) (@lem5487409)). Qed.
Lemma lem5487412 : term173 = term143.
Proof. exact (TRANS (@lem5487407) (@lem5487411)). Qed.
Lemma lem5487413 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5487414 : term262 = term222.
Proof. exact (MK_COMB (@lem5487413) (@lem5487412)). Qed.
Lemma lem5487416 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487417 : term222 = term129.
Proof. exact (@lem5487416 term144). Qed.
Lemma lem5487418 : term262 = term129.
Proof. exact (TRANS (@lem5487414) (@lem5487417)). Qed.
Lemma lem5487419 : term129 = term262.
Proof. exact (SYM (@lem5487418)). Qed.
Lemma lem5487420 : term261 = term262.
Proof. exact (TRANS (@lem5487404) (@lem5487419)). Qed.
Lemma lem5487421 : term251 = term161.
Proof. exact (@lem5487371 (@lem5487420)). Qed.
Lemma lem5487422 : term250 = term161.
Proof. exact (TRANS (@lem5487337) (@lem5487421)). Qed.
Lemma lem5487424 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5487425 : term161 = term129.
Proof. exact (@lem5487424 term129). Qed.
Lemma lem5487426 : term250 = term129.
Proof. exact (TRANS (@lem5487422) (@lem5487425)). Qed.
Lemma lem5487427 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487428 : term263 = term260.
Proof. exact (MK_COMB (@lem5487427) (@lem5487426)). Qed.
Lemma lem5487429 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5487430 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5487428) (@lem5487429 _70607)). Qed.
Lemma lem5487431 (_70607 : int) : (term246 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5487328 _70607) (@lem5487430 _70607)). Qed.
Lemma lem5487432 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5487433 (_70607 : int) : (term246 _70607) = term129.
Proof. exact (TRANS (@lem5487431 _70607) (@lem5487432 _70607)). Qed.
Lemma lem5487434 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487435 (_70607 : int) : (term265 _70607) = term266.
Proof. exact (MK_COMB (@lem5487434) (@lem5487433 _70607)). Qed.
Lemma lem5487436 (_70608 : int) : (term559 _70608) = (term560 _70608).
Proof. exact (@lem1982757 (term239 _70608) term143 term164). Qed.
Lemma lem5487438 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487439 : term164 = term165.
Proof. exact (@lem5487438 term144). Qed.
Lemma lem5487441 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487442 : term143 = term191.
Proof. exact (@lem5487441 term144). Qed.
Lemma lem5487443 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487444 : term558 = term561.
Proof. exact (MK_COMB (@lem5487443) (@lem5487442)). Qed.
Lemma lem5487445 : term562 = term563.
Proof. exact (MK_COMB (@lem5487444) (@lem5487439)). Qed.
Lemma lem5487446 : term564.
Proof. exact (@lem1981473 term143 term143 term164 term143 term129 term143). Qed.
Lemma lem5487448 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487449 : term211 = term217.
Proof. exact (@lem5487448 (NUMERAL 0) term144). Qed.
Lemma lem5487450 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487451 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487452 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487451 h1) (fun h1 : term217 = True => @lem5487450)). Qed.
Lemma lem5487453 : term217 = True.
Proof. exact (EQ_MP (@lem5487452) (@lem5487450)). Qed.
Lemma lem5487454 : term211 = True.
Proof. exact (TRANS (@lem5487449) (@lem5487453)). Qed.
Lemma lem5487455 : True = term211.
Proof. exact (SYM (@lem5487454)). Qed.
Lemma lem5487456 : term211.
Proof. exact (EQ_MP (@lem5487455) (@lem0)). Qed.
Lemma lem5487457 : term565.
Proof. exact (@lem5487446 (@lem5487456)). Qed.
Lemma lem5487459 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487460 : term211 = term217.
Proof. exact (@lem5487459 (NUMERAL 0) term144). Qed.
Lemma lem5487461 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487462 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487463 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487462 h1) (fun h1 : term217 = True => @lem5487461)). Qed.
Lemma lem5487464 : term217 = True.
Proof. exact (EQ_MP (@lem5487463) (@lem5487461)). Qed.
Lemma lem5487465 : term211 = True.
Proof. exact (TRANS (@lem5487460) (@lem5487464)). Qed.
Lemma lem5487466 : True = term211.
Proof. exact (SYM (@lem5487465)). Qed.
Lemma lem5487467 : term211.
Proof. exact (EQ_MP (@lem5487466) (@lem0)). Qed.
Lemma lem5487468 : term566.
Proof. exact (@lem5487457 (@lem5487467)). Qed.
Lemma lem5487470 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487471 : term211 = term217.
Proof. exact (@lem5487470 (NUMERAL 0) term144). Qed.
Lemma lem5487472 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487473 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487474 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487473 h1) (fun h1 : term217 = True => @lem5487472)). Qed.
Lemma lem5487475 : term217 = True.
Proof. exact (EQ_MP (@lem5487474) (@lem5487472)). Qed.
Lemma lem5487476 : term211 = True.
Proof. exact (TRANS (@lem5487471) (@lem5487475)). Qed.
Lemma lem5487477 : True = term211.
Proof. exact (SYM (@lem5487476)). Qed.
Lemma lem5487478 : term211.
Proof. exact (EQ_MP (@lem5487477) (@lem0)). Qed.
Lemma lem5487479 : term567.
Proof. exact (@lem5487468 (@lem5487478)). Qed.
Lemma lem5487481 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5487482 : term192 = term197.
Proof. exact (@lem5487481 term144 term144). Qed.
Lemma lem5487483 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487484 : term176 = term144.
Proof. exact (EQ_MP (@lem5487483) (@lem940073)). Qed.
Lemma lem5487485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487486 : term174 = term143.
Proof. exact (MK_COMB (@lem5487485) (@lem5487484)). Qed.
Lemma lem5487487 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5487488 : term197 = term164.
Proof. exact (MK_COMB (@lem5487487) (@lem5487486)). Qed.
Lemma lem5487489 : term192 = term164.
Proof. exact (TRANS (@lem5487482) (@lem5487488)). Qed.
Lemma lem5487491 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487492 : term173 = term174.
Proof. exact (@lem5487491 term144 term144). Qed.
Lemma lem5487493 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487494 : term176 = term144.
Proof. exact (EQ_MP (@lem5487493) (@lem940073)). Qed.
Lemma lem5487495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487496 : term174 = term143.
Proof. exact (MK_COMB (@lem5487495) (@lem5487494)). Qed.
Lemma lem5487497 : term173 = term143.
Proof. exact (TRANS (@lem5487492) (@lem5487496)). Qed.
Lemma lem5487498 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487499 : term568 = term558.
Proof. exact (MK_COMB (@lem5487498) (@lem5487497)). Qed.
Lemma lem5487500 : term569 = term562.
Proof. exact (MK_COMB (@lem5487499) (@lem5487489)). Qed.
Lemma lem5487502 (m : nat) : (term570 m) = term129.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5487503 : term562 = term129.
Proof. exact (@lem5487502 term144). Qed.
Lemma lem5487504 : term569 = term129.
Proof. exact (TRANS (@lem5487500) (@lem5487503)). Qed.
Lemma lem5487505 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487506 : term571 = term260.
Proof. exact (MK_COMB (@lem5487505) (@lem5487504)). Qed.
Lemma lem5487507 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5487508 : term572 = term222.
Proof. exact (MK_COMB (@lem5487506) (@lem5487507)). Qed.
Lemma lem5487510 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487511 : term222 = term129.
Proof. exact (@lem5487510 term144). Qed.
Lemma lem5487512 : term572 = term129.
Proof. exact (TRANS (@lem5487508) (@lem5487511)). Qed.
Lemma lem5487514 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487515 : term173 = term174.
Proof. exact (@lem5487514 term144 term144). Qed.
Lemma lem5487516 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487517 : term176 = term144.
Proof. exact (EQ_MP (@lem5487516) (@lem940073)). Qed.
Lemma lem5487518 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487519 : term174 = term143.
Proof. exact (MK_COMB (@lem5487518) (@lem5487517)). Qed.
Lemma lem5487520 : term173 = term143.
Proof. exact (TRANS (@lem5487515) (@lem5487519)). Qed.
Lemma lem5487521 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5487522 : term262 = term222.
Proof. exact (MK_COMB (@lem5487521) (@lem5487520)). Qed.
Lemma lem5487524 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487525 : term222 = term129.
Proof. exact (@lem5487524 term144). Qed.
Lemma lem5487526 : term262 = term129.
Proof. exact (TRANS (@lem5487522) (@lem5487525)). Qed.
Lemma lem5487527 : term129 = term262.
Proof. exact (SYM (@lem5487526)). Qed.
Lemma lem5487528 : term572 = term262.
Proof. exact (TRANS (@lem5487512) (@lem5487527)). Qed.
Lemma lem5487529 : term563 = term161.
Proof. exact (@lem5487479 (@lem5487528)). Qed.
Lemma lem5487530 : term562 = term161.
Proof. exact (TRANS (@lem5487445) (@lem5487529)). Qed.
Lemma lem5487532 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5487533 : term161 = term129.
Proof. exact (@lem5487532 term129). Qed.
Lemma lem5487534 : term562 = term129.
Proof. exact (TRANS (@lem5487530) (@lem5487533)). Qed.
Lemma lem5487535 (_70608 : int) : (term200 _70608) = (term200 _70608).
Proof. exact (eq_refl (term200 _70608)). Qed.
Lemma lem5487536 (_70608 : int) : (term560 _70608) = (term573 _70608).
Proof. exact (MK_COMB (@lem5487535 _70608) (@lem5487534)). Qed.
Lemma lem5487537 (_70608 : int) : (term559 _70608) = (term573 _70608).
Proof. exact (TRANS (@lem5487436 _70608) (@lem5487536 _70608)). Qed.
Lemma lem5487538 (_70608 : int) : (term573 _70608) = (term239 _70608).
Proof. exact (@lem1982723 (term239 _70608)). Qed.
Lemma lem5487539 (_70608 : int) : (term559 _70608) = (term239 _70608).
Proof. exact (TRANS (@lem5487537 _70608) (@lem5487538 _70608)). Qed.
Lemma lem5487540 (_70607 : int) (_70608 : int) : (term917 _70607 _70608) = (term869 _70608).
Proof. exact (MK_COMB (@lem5487435 _70607) (@lem5487539 _70608)). Qed.
Lemma lem5487541 (_70607 : int) (_70608 : int) : (term916 _70607 _70608) = (term869 _70608).
Proof. exact (TRANS (@lem5487327 _70607 _70608) (@lem5487540 _70607 _70608)). Qed.
Lemma lem5487542 (_70608 : int) : (term869 _70608) = (term239 _70608).
Proof. exact (@lem1982721 (term239 _70608)). Qed.
Lemma lem5487543 (_70607 : int) (_70608 : int) : (term916 _70607 _70608) = (term239 _70608).
Proof. exact (TRANS (@lem5487541 _70607 _70608) (@lem5487542 _70608)). Qed.
Lemma lem5487544 (_70606 : int) : (term145 _70606) = (term145 _70606).
Proof. exact (eq_refl (term145 _70606)). Qed.
Lemma lem5487545 (_70607 : int) (_70606 : int) (_70608 : int) : (term915 _70606 _70607 _70608) = (term583 _70606 _70608).
Proof. exact (MK_COMB (@lem5487544 _70606) (@lem5487543 _70607 _70608)). Qed.
Lemma lem5487546 (_70607 : int) (_70606 : int) (_70608 : int) : (term914 _70606 _70607 _70608) = (term583 _70606 _70608).
Proof. exact (TRANS (@lem5487326 _70606 _70607 _70608) (@lem5487545 _70607 _70606 _70608)). Qed.
Lemma lem5487547 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5487548 (_70607 : int) (_70606 : int) (_70608 : int) : (term918 _70606 _70607 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5487547) (@lem5487546 _70607 _70606 _70608)). Qed.
Lemma lem5487549 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5487550 (_70607 : int) (_70606 : int) (_70608 : int) : (term913 _70606 _70607 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5487548 _70607 _70606 _70608) (@lem5487549)). Qed.
Lemma lem5487551 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (EQ_MP (@lem5487550 _70607 _70606 _70608) (@lem5487325 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487553 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5487554 : term210 = term211.
Proof. exact (@lem5487553 term129 term143). Qed.
Lemma lem5487556 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487557 : term143 = term191.
Proof. exact (@lem5487556 term144). Qed.
Lemma lem5487559 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487560 : term129 = term161.
Proof. exact (@lem5487559 (NUMERAL 0)). Qed.
Lemma lem5487561 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487562 : term212 = term213.
Proof. exact (MK_COMB (@lem5487561) (@lem5487560)). Qed.
Lemma lem5487563 : term211 = term214.
Proof. exact (MK_COMB (@lem5487562) (@lem5487557)). Qed.
Lemma lem5487564 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5487566 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487567 : term211 = term217.
Proof. exact (@lem5487566 (NUMERAL 0) term144). Qed.
Lemma lem5487568 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487569 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487570 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487569 h1) (fun h1 : term217 = True => @lem5487568)). Qed.
Lemma lem5487571 : term217 = True.
Proof. exact (EQ_MP (@lem5487570) (@lem5487568)). Qed.
Lemma lem5487572 : term211 = True.
Proof. exact (TRANS (@lem5487567) (@lem5487571)). Qed.
Lemma lem5487573 : True = term211.
Proof. exact (SYM (@lem5487572)). Qed.
Lemma lem5487574 : term211.
Proof. exact (EQ_MP (@lem5487573) (@lem0)). Qed.
Lemma lem5487575 : term219.
Proof. exact (@lem5487564 (@lem5487574)). Qed.
Lemma lem5487577 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487578 : term211 = term217.
Proof. exact (@lem5487577 (NUMERAL 0) term144). Qed.
Lemma lem5487579 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487580 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487581 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487580 h1) (fun h1 : term217 = True => @lem5487579)). Qed.
Lemma lem5487582 : term217 = True.
Proof. exact (EQ_MP (@lem5487581) (@lem5487579)). Qed.
Lemma lem5487583 : term211 = True.
Proof. exact (TRANS (@lem5487578) (@lem5487582)). Qed.
Lemma lem5487584 : True = term211.
Proof. exact (SYM (@lem5487583)). Qed.
Lemma lem5487585 : term211.
Proof. exact (EQ_MP (@lem5487584) (@lem0)). Qed.
Lemma lem5487586 : term214 = term220.
Proof. exact (@lem5487575 (@lem5487585)). Qed.
Lemma lem5487588 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487589 : term173 = term174.
Proof. exact (@lem5487588 term144 term144). Qed.
Lemma lem5487590 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487591 : term176 = term144.
Proof. exact (EQ_MP (@lem5487590) (@lem940073)). Qed.
Lemma lem5487592 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487593 : term174 = term143.
Proof. exact (MK_COMB (@lem5487592) (@lem5487591)). Qed.
Lemma lem5487594 : term173 = term143.
Proof. exact (TRANS (@lem5487589) (@lem5487593)). Qed.
Lemma lem5487596 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487597 : term222 = term129.
Proof. exact (@lem5487596 term144). Qed.
Lemma lem5487598 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487599 : term223 = term212.
Proof. exact (MK_COMB (@lem5487598) (@lem5487597)). Qed.
Lemma lem5487600 : term220 = term211.
Proof. exact (MK_COMB (@lem5487599) (@lem5487594)). Qed.
Lemma lem5487602 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487603 : term211 = term217.
Proof. exact (@lem5487602 (NUMERAL 0) term144). Qed.
Lemma lem5487604 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487605 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487606 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487605 h1) (fun h1 : term217 = True => @lem5487604)). Qed.
Lemma lem5487607 : term217 = True.
Proof. exact (EQ_MP (@lem5487606) (@lem5487604)). Qed.
Lemma lem5487608 : term211 = True.
Proof. exact (TRANS (@lem5487603) (@lem5487607)). Qed.
Lemma lem5487609 : term220 = True.
Proof. exact (TRANS (@lem5487600) (@lem5487608)). Qed.
Lemma lem5487610 : term214 = True.
Proof. exact (TRANS (@lem5487586) (@lem5487609)). Qed.
Lemma lem5487611 : term211 = True.
Proof. exact (TRANS (@lem5487563) (@lem5487610)). Qed.
Lemma lem5487612 : term210 = True.
Proof. exact (TRANS (@lem5487554) (@lem5487611)). Qed.
Lemma lem5487613 : True = term210.
Proof. exact (SYM (@lem5487612)). Qed.
Lemma lem5487614 : term210.
Proof. exact (EQ_MP (@lem5487613) (@lem0)). Qed.
Lemma lem5487615 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term844 _70606 _70608.
Proof. exact (conj (@lem5487614) (@lem5487551 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487617 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5487618 (_70606 : int) (_70608 : int) : term845 _70606 _70608.
Proof. exact (@lem5487617 term143 (term583 _70606 _70608)). Qed.
Lemma lem5487619 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term846 _70606 _70608.
Proof. exact (@lem5487618 _70606 _70608 (@lem5487615 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487620 (_70606 : int) (_70608 : int) : (term847 _70606 _70608) = (term583 _70606 _70608).
Proof. exact (@lem1982733 (term583 _70606 _70608)). Qed.
Lemma lem5487621 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5487622 (_70606 : int) (_70608 : int) : (term848 _70606 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5487621) (@lem5487620 _70606 _70608)). Qed.
Lemma lem5487623 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5487624 (_70606 : int) (_70608 : int) : (term846 _70606 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5487622 _70606 _70608) (@lem5487623)). Qed.
Lemma lem5487625 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (EQ_MP (@lem5487624 _70606 _70608) (@lem5487619 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487626 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term849 _70606 _70608.
Proof. exact (conj (@lem5487625 _70607 _70606 _70608 h1) (@lem5487145 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487628 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5487629 (_70606 : int) (_70608 : int) : term850 _70606 _70608.
Proof. exact (@lem5487628 (term583 _70606 _70608) (term552 _70606 _70608)). Qed.
Lemma lem5487630 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term851 _70606 _70608.
Proof. exact (@lem5487629 _70606 _70608 (@lem5487626 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487631 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = (term853 _70606 _70608).
Proof. exact (@lem1982753 (real_of_int _70606) (term239 _70606) (term239 _70608) (term546 _70608)). Qed.
Lemma lem5487632 (_70606 : int) : (term835 _70606) = (term247 _70606).
Proof. exact (@lem1982715 term164 (real_of_int _70606)). Qed.
Lemma lem5487634 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487635 : term143 = term191.
Proof. exact (@lem5487634 term144). Qed.
Lemma lem5487637 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487638 : term164 = term165.
Proof. exact (@lem5487637 term144). Qed.
Lemma lem5487639 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487640 : term248 = term249.
Proof. exact (MK_COMB (@lem5487639) (@lem5487638)). Qed.
Lemma lem5487641 : term250 = term251.
Proof. exact (MK_COMB (@lem5487640) (@lem5487635)). Qed.
Lemma lem5487642 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5487644 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487645 : term211 = term217.
Proof. exact (@lem5487644 (NUMERAL 0) term144). Qed.
Lemma lem5487646 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487647 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487648 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487647 h1) (fun h1 : term217 = True => @lem5487646)). Qed.
Lemma lem5487649 : term217 = True.
Proof. exact (EQ_MP (@lem5487648) (@lem5487646)). Qed.
Lemma lem5487650 : term211 = True.
Proof. exact (TRANS (@lem5487645) (@lem5487649)). Qed.
Lemma lem5487651 : True = term211.
Proof. exact (SYM (@lem5487650)). Qed.
Lemma lem5487652 : term211.
Proof. exact (EQ_MP (@lem5487651) (@lem0)). Qed.
Lemma lem5487653 : term253.
Proof. exact (@lem5487642 (@lem5487652)). Qed.
Lemma lem5487655 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487656 : term211 = term217.
Proof. exact (@lem5487655 (NUMERAL 0) term144). Qed.
Lemma lem5487657 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487658 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487659 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487658 h1) (fun h1 : term217 = True => @lem5487657)). Qed.
Lemma lem5487660 : term217 = True.
Proof. exact (EQ_MP (@lem5487659) (@lem5487657)). Qed.
Lemma lem5487661 : term211 = True.
Proof. exact (TRANS (@lem5487656) (@lem5487660)). Qed.
Lemma lem5487662 : True = term211.
Proof. exact (SYM (@lem5487661)). Qed.
Lemma lem5487663 : term211.
Proof. exact (EQ_MP (@lem5487662) (@lem0)). Qed.
Lemma lem5487664 : term254.
Proof. exact (@lem5487653 (@lem5487663)). Qed.
Lemma lem5487666 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487667 : term211 = term217.
Proof. exact (@lem5487666 (NUMERAL 0) term144). Qed.
Lemma lem5487668 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487669 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487670 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487669 h1) (fun h1 : term217 = True => @lem5487668)). Qed.
Lemma lem5487671 : term217 = True.
Proof. exact (EQ_MP (@lem5487670) (@lem5487668)). Qed.
Lemma lem5487672 : term211 = True.
Proof. exact (TRANS (@lem5487667) (@lem5487671)). Qed.
Lemma lem5487673 : True = term211.
Proof. exact (SYM (@lem5487672)). Qed.
Lemma lem5487674 : term211.
Proof. exact (EQ_MP (@lem5487673) (@lem0)). Qed.
Lemma lem5487675 : term255.
Proof. exact (@lem5487664 (@lem5487674)). Qed.
Lemma lem5487677 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487678 : term173 = term174.
Proof. exact (@lem5487677 term144 term144). Qed.
Lemma lem5487679 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487680 : term176 = term144.
Proof. exact (EQ_MP (@lem5487679) (@lem940073)). Qed.
Lemma lem5487681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487682 : term174 = term143.
Proof. exact (MK_COMB (@lem5487681) (@lem5487680)). Qed.
Lemma lem5487683 : term173 = term143.
Proof. exact (TRANS (@lem5487678) (@lem5487682)). Qed.
Lemma lem5487685 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5487686 : term192 = term197.
Proof. exact (@lem5487685 term144 term144). Qed.
Lemma lem5487687 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487688 : term176 = term144.
Proof. exact (EQ_MP (@lem5487687) (@lem940073)). Qed.
Lemma lem5487689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487690 : term174 = term143.
Proof. exact (MK_COMB (@lem5487689) (@lem5487688)). Qed.
Lemma lem5487691 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5487692 : term197 = term164.
Proof. exact (MK_COMB (@lem5487691) (@lem5487690)). Qed.
Lemma lem5487693 : term192 = term164.
Proof. exact (TRANS (@lem5487686) (@lem5487692)). Qed.
Lemma lem5487694 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487695 : term256 = term248.
Proof. exact (MK_COMB (@lem5487694) (@lem5487693)). Qed.
Lemma lem5487696 : term257 = term250.
Proof. exact (MK_COMB (@lem5487695) (@lem5487683)). Qed.
Lemma lem5487698 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5487699 : term250 = term129.
Proof. exact (@lem5487698 term144). Qed.
Lemma lem5487700 : term257 = term129.
Proof. exact (TRANS (@lem5487696) (@lem5487699)). Qed.
Lemma lem5487701 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487702 : term259 = term260.
Proof. exact (MK_COMB (@lem5487701) (@lem5487700)). Qed.
Lemma lem5487703 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5487704 : term261 = term222.
Proof. exact (MK_COMB (@lem5487702) (@lem5487703)). Qed.
Lemma lem5487706 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487707 : term222 = term129.
Proof. exact (@lem5487706 term144). Qed.
Lemma lem5487708 : term261 = term129.
Proof. exact (TRANS (@lem5487704) (@lem5487707)). Qed.
Lemma lem5487710 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487711 : term173 = term174.
Proof. exact (@lem5487710 term144 term144). Qed.
Lemma lem5487712 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487713 : term176 = term144.
Proof. exact (EQ_MP (@lem5487712) (@lem940073)). Qed.
Lemma lem5487714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487715 : term174 = term143.
Proof. exact (MK_COMB (@lem5487714) (@lem5487713)). Qed.
Lemma lem5487716 : term173 = term143.
Proof. exact (TRANS (@lem5487711) (@lem5487715)). Qed.
Lemma lem5487717 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5487718 : term262 = term222.
Proof. exact (MK_COMB (@lem5487717) (@lem5487716)). Qed.
Lemma lem5487720 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487721 : term222 = term129.
Proof. exact (@lem5487720 term144). Qed.
Lemma lem5487722 : term262 = term129.
Proof. exact (TRANS (@lem5487718) (@lem5487721)). Qed.
Lemma lem5487723 : term129 = term262.
Proof. exact (SYM (@lem5487722)). Qed.
Lemma lem5487724 : term261 = term262.
Proof. exact (TRANS (@lem5487708) (@lem5487723)). Qed.
Lemma lem5487725 : term251 = term161.
Proof. exact (@lem5487675 (@lem5487724)). Qed.
Lemma lem5487726 : term250 = term161.
Proof. exact (TRANS (@lem5487641) (@lem5487725)). Qed.
Lemma lem5487728 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5487729 : term161 = term129.
Proof. exact (@lem5487728 term129). Qed.
Lemma lem5487730 : term250 = term129.
Proof. exact (TRANS (@lem5487726) (@lem5487729)). Qed.
Lemma lem5487731 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487732 : term263 = term260.
Proof. exact (MK_COMB (@lem5487731) (@lem5487730)). Qed.
Lemma lem5487733 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5487734 (_70606 : int) : (term247 _70606) = (term264 _70606).
Proof. exact (MK_COMB (@lem5487732) (@lem5487733 _70606)). Qed.
Lemma lem5487735 (_70606 : int) : (term835 _70606) = (term264 _70606).
Proof. exact (TRANS (@lem5487632 _70606) (@lem5487734 _70606)). Qed.
Lemma lem5487736 (_70606 : int) : (term264 _70606) = term129.
Proof. exact (@lem1982719 (real_of_int _70606)). Qed.
Lemma lem5487737 (_70606 : int) : (term835 _70606) = term129.
Proof. exact (TRANS (@lem5487735 _70606) (@lem5487736 _70606)). Qed.
Lemma lem5487738 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487739 (_70606 : int) : (term836 _70606) = term266.
Proof. exact (MK_COMB (@lem5487738) (@lem5487737 _70606)). Qed.
Lemma lem5487740 (_70608 : int) : (term854 _70608) = (term281 _70608).
Proof. exact (@lem1982763 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5487741 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5487743 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487744 : term143 = term191.
Proof. exact (@lem5487743 term144). Qed.
Lemma lem5487746 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487747 : term164 = term165.
Proof. exact (@lem5487746 term144). Qed.
Lemma lem5487748 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487749 : term248 = term249.
Proof. exact (MK_COMB (@lem5487748) (@lem5487747)). Qed.
Lemma lem5487750 : term250 = term251.
Proof. exact (MK_COMB (@lem5487749) (@lem5487744)). Qed.
Lemma lem5487751 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5487753 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487754 : term211 = term217.
Proof. exact (@lem5487753 (NUMERAL 0) term144). Qed.
Lemma lem5487755 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487756 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487757 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487756 h1) (fun h1 : term217 = True => @lem5487755)). Qed.
Lemma lem5487758 : term217 = True.
Proof. exact (EQ_MP (@lem5487757) (@lem5487755)). Qed.
Lemma lem5487759 : term211 = True.
Proof. exact (TRANS (@lem5487754) (@lem5487758)). Qed.
Lemma lem5487760 : True = term211.
Proof. exact (SYM (@lem5487759)). Qed.
Lemma lem5487761 : term211.
Proof. exact (EQ_MP (@lem5487760) (@lem0)). Qed.
Lemma lem5487762 : term253.
Proof. exact (@lem5487751 (@lem5487761)). Qed.
Lemma lem5487764 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487765 : term211 = term217.
Proof. exact (@lem5487764 (NUMERAL 0) term144). Qed.
Lemma lem5487766 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487767 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487768 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487767 h1) (fun h1 : term217 = True => @lem5487766)). Qed.
Lemma lem5487769 : term217 = True.
Proof. exact (EQ_MP (@lem5487768) (@lem5487766)). Qed.
Lemma lem5487770 : term211 = True.
Proof. exact (TRANS (@lem5487765) (@lem5487769)). Qed.
Lemma lem5487771 : True = term211.
Proof. exact (SYM (@lem5487770)). Qed.
Lemma lem5487772 : term211.
Proof. exact (EQ_MP (@lem5487771) (@lem0)). Qed.
Lemma lem5487773 : term254.
Proof. exact (@lem5487762 (@lem5487772)). Qed.
Lemma lem5487775 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487776 : term211 = term217.
Proof. exact (@lem5487775 (NUMERAL 0) term144). Qed.
Lemma lem5487777 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487778 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487779 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487778 h1) (fun h1 : term217 = True => @lem5487777)). Qed.
Lemma lem5487780 : term217 = True.
Proof. exact (EQ_MP (@lem5487779) (@lem5487777)). Qed.
Lemma lem5487781 : term211 = True.
Proof. exact (TRANS (@lem5487776) (@lem5487780)). Qed.
Lemma lem5487782 : True = term211.
Proof. exact (SYM (@lem5487781)). Qed.
Lemma lem5487783 : term211.
Proof. exact (EQ_MP (@lem5487782) (@lem0)). Qed.
Lemma lem5487784 : term255.
Proof. exact (@lem5487773 (@lem5487783)). Qed.
Lemma lem5487786 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487787 : term173 = term174.
Proof. exact (@lem5487786 term144 term144). Qed.
Lemma lem5487788 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487789 : term176 = term144.
Proof. exact (EQ_MP (@lem5487788) (@lem940073)). Qed.
Lemma lem5487790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487791 : term174 = term143.
Proof. exact (MK_COMB (@lem5487790) (@lem5487789)). Qed.
Lemma lem5487792 : term173 = term143.
Proof. exact (TRANS (@lem5487787) (@lem5487791)). Qed.
Lemma lem5487794 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5487795 : term192 = term197.
Proof. exact (@lem5487794 term144 term144). Qed.
Lemma lem5487796 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487797 : term176 = term144.
Proof. exact (EQ_MP (@lem5487796) (@lem940073)). Qed.
Lemma lem5487798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487799 : term174 = term143.
Proof. exact (MK_COMB (@lem5487798) (@lem5487797)). Qed.
Lemma lem5487800 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5487801 : term197 = term164.
Proof. exact (MK_COMB (@lem5487800) (@lem5487799)). Qed.
Lemma lem5487802 : term192 = term164.
Proof. exact (TRANS (@lem5487795) (@lem5487801)). Qed.
Lemma lem5487803 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487804 : term256 = term248.
Proof. exact (MK_COMB (@lem5487803) (@lem5487802)). Qed.
Lemma lem5487805 : term257 = term250.
Proof. exact (MK_COMB (@lem5487804) (@lem5487792)). Qed.
Lemma lem5487807 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5487808 : term250 = term129.
Proof. exact (@lem5487807 term144). Qed.
Lemma lem5487809 : term257 = term129.
Proof. exact (TRANS (@lem5487805) (@lem5487808)). Qed.
Lemma lem5487810 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487811 : term259 = term260.
Proof. exact (MK_COMB (@lem5487810) (@lem5487809)). Qed.
Lemma lem5487812 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5487813 : term261 = term222.
Proof. exact (MK_COMB (@lem5487811) (@lem5487812)). Qed.
Lemma lem5487815 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487816 : term222 = term129.
Proof. exact (@lem5487815 term144). Qed.
Lemma lem5487817 : term261 = term129.
Proof. exact (TRANS (@lem5487813) (@lem5487816)). Qed.
Lemma lem5487819 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487820 : term173 = term174.
Proof. exact (@lem5487819 term144 term144). Qed.
Lemma lem5487821 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487822 : term176 = term144.
Proof. exact (EQ_MP (@lem5487821) (@lem940073)). Qed.
Lemma lem5487823 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487824 : term174 = term143.
Proof. exact (MK_COMB (@lem5487823) (@lem5487822)). Qed.
Lemma lem5487825 : term173 = term143.
Proof. exact (TRANS (@lem5487820) (@lem5487824)). Qed.
Lemma lem5487826 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5487827 : term262 = term222.
Proof. exact (MK_COMB (@lem5487826) (@lem5487825)). Qed.
Lemma lem5487829 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487830 : term222 = term129.
Proof. exact (@lem5487829 term144). Qed.
Lemma lem5487831 : term262 = term129.
Proof. exact (TRANS (@lem5487827) (@lem5487830)). Qed.
Lemma lem5487832 : term129 = term262.
Proof. exact (SYM (@lem5487831)). Qed.
Lemma lem5487833 : term261 = term262.
Proof. exact (TRANS (@lem5487817) (@lem5487832)). Qed.
Lemma lem5487834 : term251 = term161.
Proof. exact (@lem5487784 (@lem5487833)). Qed.
Lemma lem5487835 : term250 = term161.
Proof. exact (TRANS (@lem5487750) (@lem5487834)). Qed.
Lemma lem5487837 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5487838 : term161 = term129.
Proof. exact (@lem5487837 term129). Qed.
Lemma lem5487839 : term250 = term129.
Proof. exact (TRANS (@lem5487835) (@lem5487838)). Qed.
Lemma lem5487840 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5487841 : term263 = term260.
Proof. exact (MK_COMB (@lem5487840) (@lem5487839)). Qed.
Lemma lem5487842 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5487843 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5487841) (@lem5487842 _70608)). Qed.
Lemma lem5487844 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5487741 _70608) (@lem5487843 _70608)). Qed.
Lemma lem5487845 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5487846 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5487844 _70608) (@lem5487845 _70608)). Qed.
Lemma lem5487847 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5487848 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5487847) (@lem5487846 _70608)). Qed.
Lemma lem5487849 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5487850 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5487848 _70608) (@lem5487849)). Qed.
Lemma lem5487851 (_70608 : int) : (term854 _70608) = term282.
Proof. exact (TRANS (@lem5487740 _70608) (@lem5487850 _70608)). Qed.
Lemma lem5487852 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5487853 (_70608 : int) : (term854 _70608) = term164.
Proof. exact (TRANS (@lem5487851 _70608) (@lem5487852)). Qed.
Lemma lem5487854 (_70606 : int) (_70608 : int) : (term853 _70606 _70608) = term282.
Proof. exact (MK_COMB (@lem5487739 _70606) (@lem5487853 _70608)). Qed.
Lemma lem5487855 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term282.
Proof. exact (TRANS (@lem5487631 _70606 _70608) (@lem5487854 _70606 _70608)). Qed.
Lemma lem5487856 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5487857 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term164.
Proof. exact (TRANS (@lem5487855 _70606 _70608) (@lem5487856)). Qed.
Lemma lem5487858 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5487859 (_70606 : int) (_70608 : int) : (term855 _70606 _70608) = term284.
Proof. exact (MK_COMB (@lem5487858) (@lem5487857 _70606 _70608)). Qed.
Lemma lem5487860 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5487861 (_70606 : int) (_70608 : int) : (term851 _70606 _70608) = term285.
Proof. exact (MK_COMB (@lem5487859 _70606 _70608) (@lem5487860)). Qed.
Lemma lem5487862 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : term285.
Proof. exact (EQ_MP (@lem5487861 _70606 _70608) (@lem5487630 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487864 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5487865 : term285 = term286.
Proof. exact (@lem5487864 term129 term164). Qed.
Lemma lem5487867 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5487868 : term164 = term165.
Proof. exact (@lem5487867 term144). Qed.
Lemma lem5487870 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487871 : term129 = term161.
Proof. exact (@lem5487870 (NUMERAL 0)). Qed.
Lemma lem5487872 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5487873 : term131 = term287.
Proof. exact (MK_COMB (@lem5487872) (@lem5487871)). Qed.
Lemma lem5487874 : term286 = term288.
Proof. exact (MK_COMB (@lem5487873) (@lem5487868)). Qed.
Lemma lem5487875 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5487877 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487878 : term211 = term217.
Proof. exact (@lem5487877 (NUMERAL 0) term144). Qed.
Lemma lem5487879 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487880 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487881 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487880 h1) (fun h1 : term217 = True => @lem5487879)). Qed.
Lemma lem5487882 : term217 = True.
Proof. exact (EQ_MP (@lem5487881) (@lem5487879)). Qed.
Lemma lem5487883 : term211 = True.
Proof. exact (TRANS (@lem5487878) (@lem5487882)). Qed.
Lemma lem5487884 : True = term211.
Proof. exact (SYM (@lem5487883)). Qed.
Lemma lem5487885 : term211.
Proof. exact (EQ_MP (@lem5487884) (@lem0)). Qed.
Lemma lem5487886 : term290.
Proof. exact (@lem5487875 (@lem5487885)). Qed.
Lemma lem5487888 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487889 : term211 = term217.
Proof. exact (@lem5487888 (NUMERAL 0) term144). Qed.
Lemma lem5487890 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487891 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487892 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487891 h1) (fun h1 : term217 = True => @lem5487890)). Qed.
Lemma lem5487893 : term217 = True.
Proof. exact (EQ_MP (@lem5487892) (@lem5487890)). Qed.
Lemma lem5487894 : term211 = True.
Proof. exact (TRANS (@lem5487889) (@lem5487893)). Qed.
Lemma lem5487895 : True = term211.
Proof. exact (SYM (@lem5487894)). Qed.
Lemma lem5487896 : term211.
Proof. exact (EQ_MP (@lem5487895) (@lem0)). Qed.
Lemma lem5487897 : term288 = term291.
Proof. exact (@lem5487886 (@lem5487896)). Qed.
Lemma lem5487899 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5487900 : term192 = term197.
Proof. exact (@lem5487899 term144 term144). Qed.
Lemma lem5487901 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487902 : term176 = term144.
Proof. exact (EQ_MP (@lem5487901) (@lem940073)). Qed.
Lemma lem5487903 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487904 : term174 = term143.
Proof. exact (MK_COMB (@lem5487903) (@lem5487902)). Qed.
Lemma lem5487905 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5487906 : term197 = term164.
Proof. exact (MK_COMB (@lem5487905) (@lem5487904)). Qed.
Lemma lem5487907 : term192 = term164.
Proof. exact (TRANS (@lem5487900) (@lem5487906)). Qed.
Lemma lem5487909 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487910 : term222 = term129.
Proof. exact (@lem5487909 term144). Qed.
Lemma lem5487911 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5487912 : term292 = term131.
Proof. exact (MK_COMB (@lem5487911) (@lem5487910)). Qed.
Lemma lem5487913 : term291 = term286.
Proof. exact (MK_COMB (@lem5487912) (@lem5487907)). Qed.
Lemma lem5487915 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5487916 : term286 = term295.
Proof. exact (@lem5487915 (NUMERAL 0) term144). Qed.
Lemma lem5487917 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487918 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5487919 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487918 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5487917)). Qed.
Lemma lem5487920 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5487919) (@lem5487917)). Qed.
Lemma lem5487921 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5487922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5487923 : term296 = (and True).
Proof. exact (MK_COMB (@lem5487922) (@lem5487921)). Qed.
Lemma lem5487924 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5487923) (@lem5487920)). Qed.
Lemma lem5487926 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5487927 : term295 = False.
Proof. exact (TRANS (@lem5487924) (@lem5487926)). Qed.
Lemma lem5487928 : term286 = False.
Proof. exact (TRANS (@lem5487916) (@lem5487927)). Qed.
Lemma lem5487929 : term291 = False.
Proof. exact (TRANS (@lem5487913) (@lem5487928)). Qed.
Lemma lem5487930 : term288 = False.
Proof. exact (TRANS (@lem5487897) (@lem5487929)). Qed.
Lemma lem5487931 : term286 = False.
Proof. exact (TRANS (@lem5487874) (@lem5487930)). Qed.
Lemma lem5487932 : term285 = False.
Proof. exact (TRANS (@lem5487865) (@lem5487931)). Qed.
Lemma lem5487933 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term890 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5487932) (@lem5487862 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487934 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term919 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5487935 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term781 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487934 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487937 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term732 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487935 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487939 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term683 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487937 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487941 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term633 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487939 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487943 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term614 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5487941 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487944 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : (term552 _70606 _70607) = term129.
Proof. exact (proj1 (@lem5487941 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487945 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (proj2 (@lem5487943 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487946 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (proj1 (@lem5487943 _70607 _70606 _70608 h1)). Qed.
Lemma lem5487948 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5487949 : term210 = term211.
Proof. exact (@lem5487948 term129 term143). Qed.
Lemma lem5487951 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487952 : term143 = term191.
Proof. exact (@lem5487951 term144). Qed.
Lemma lem5487954 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5487955 : term129 = term161.
Proof. exact (@lem5487954 (NUMERAL 0)). Qed.
Lemma lem5487956 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487957 : term212 = term213.
Proof. exact (MK_COMB (@lem5487956) (@lem5487955)). Qed.
Lemma lem5487958 : term211 = term214.
Proof. exact (MK_COMB (@lem5487957) (@lem5487952)). Qed.
Lemma lem5487959 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5487961 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487962 : term211 = term217.
Proof. exact (@lem5487961 (NUMERAL 0) term144). Qed.
Lemma lem5487963 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487964 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487965 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487964 h1) (fun h1 : term217 = True => @lem5487963)). Qed.
Lemma lem5487966 : term217 = True.
Proof. exact (EQ_MP (@lem5487965) (@lem5487963)). Qed.
Lemma lem5487967 : term211 = True.
Proof. exact (TRANS (@lem5487962) (@lem5487966)). Qed.
Lemma lem5487968 : True = term211.
Proof. exact (SYM (@lem5487967)). Qed.
Lemma lem5487969 : term211.
Proof. exact (EQ_MP (@lem5487968) (@lem0)). Qed.
Lemma lem5487970 : term219.
Proof. exact (@lem5487959 (@lem5487969)). Qed.
Lemma lem5487972 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487973 : term211 = term217.
Proof. exact (@lem5487972 (NUMERAL 0) term144). Qed.
Lemma lem5487974 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5487975 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5487976 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5487975 h1) (fun h1 : term217 = True => @lem5487974)). Qed.
Lemma lem5487977 : term217 = True.
Proof. exact (EQ_MP (@lem5487976) (@lem5487974)). Qed.
Lemma lem5487978 : term211 = True.
Proof. exact (TRANS (@lem5487973) (@lem5487977)). Qed.
Lemma lem5487979 : True = term211.
Proof. exact (SYM (@lem5487978)). Qed.
Lemma lem5487980 : term211.
Proof. exact (EQ_MP (@lem5487979) (@lem0)). Qed.
Lemma lem5487981 : term214 = term220.
Proof. exact (@lem5487970 (@lem5487980)). Qed.
Lemma lem5487983 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5487984 : term173 = term174.
Proof. exact (@lem5487983 term144 term144). Qed.
Lemma lem5487985 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5487986 : term176 = term144.
Proof. exact (EQ_MP (@lem5487985) (@lem940073)). Qed.
Lemma lem5487987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5487988 : term174 = term143.
Proof. exact (MK_COMB (@lem5487987) (@lem5487986)). Qed.
Lemma lem5487989 : term173 = term143.
Proof. exact (TRANS (@lem5487984) (@lem5487988)). Qed.
Lemma lem5487991 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5487992 : term222 = term129.
Proof. exact (@lem5487991 term144). Qed.
Lemma lem5487993 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5487994 : term223 = term212.
Proof. exact (MK_COMB (@lem5487993) (@lem5487992)). Qed.
Lemma lem5487995 : term220 = term211.
Proof. exact (MK_COMB (@lem5487994) (@lem5487989)). Qed.
Lemma lem5487997 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5487998 : term211 = term217.
Proof. exact (@lem5487997 (NUMERAL 0) term144). Qed.
Lemma lem5487999 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488000 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488001 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488000 h1) (fun h1 : term217 = True => @lem5487999)). Qed.
Lemma lem5488002 : term217 = True.
Proof. exact (EQ_MP (@lem5488001) (@lem5487999)). Qed.
Lemma lem5488003 : term211 = True.
Proof. exact (TRANS (@lem5487998) (@lem5488002)). Qed.
Lemma lem5488004 : term220 = True.
Proof. exact (TRANS (@lem5487995) (@lem5488003)). Qed.
Lemma lem5488005 : term214 = True.
Proof. exact (TRANS (@lem5487981) (@lem5488004)). Qed.
Lemma lem5488006 : term211 = True.
Proof. exact (TRANS (@lem5487958) (@lem5488005)). Qed.
Lemma lem5488007 : term210 = True.
Proof. exact (TRANS (@lem5487949) (@lem5488006)). Qed.
Lemma lem5488008 : True = term210.
Proof. exact (SYM (@lem5488007)). Qed.
Lemma lem5488009 : term210.
Proof. exact (EQ_MP (@lem5488008) (@lem0)). Qed.
Lemma lem5488010 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term840 _70606 _70608.
Proof. exact (conj (@lem5488009) (@lem5487945 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488012 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5488013 (_70606 : int) (_70608 : int) : term841 _70606 _70608.
Proof. exact (@lem5488012 term143 (term552 _70606 _70608)). Qed.
Lemma lem5488014 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term842 _70606 _70608.
Proof. exact (@lem5488013 _70606 _70608 (@lem5488010 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488015 (_70606 : int) (_70608 : int) : (term826 _70606 _70608) = (term552 _70606 _70608).
Proof. exact (@lem1982733 (term552 _70606 _70608)). Qed.
Lemma lem5488016 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5488017 (_70606 : int) (_70608 : int) : (term843 _70606 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5488016) (@lem5488015 _70606 _70608)). Qed.
Lemma lem5488018 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488019 (_70606 : int) (_70608 : int) : (term842 _70606 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5488017 _70606 _70608) (@lem5488018)). Qed.
Lemma lem5488020 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5488019 _70606 _70608) (@lem5488014 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488022 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5488023 : term210 = term211.
Proof. exact (@lem5488022 term129 term143). Qed.
Lemma lem5488025 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488026 : term143 = term191.
Proof. exact (@lem5488025 term144). Qed.
Lemma lem5488028 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488029 : term129 = term161.
Proof. exact (@lem5488028 (NUMERAL 0)). Qed.
Lemma lem5488030 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5488031 : term212 = term213.
Proof. exact (MK_COMB (@lem5488030) (@lem5488029)). Qed.
Lemma lem5488032 : term211 = term214.
Proof. exact (MK_COMB (@lem5488031) (@lem5488026)). Qed.
Lemma lem5488033 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5488035 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488036 : term211 = term217.
Proof. exact (@lem5488035 (NUMERAL 0) term144). Qed.
Lemma lem5488037 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488038 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488039 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488038 h1) (fun h1 : term217 = True => @lem5488037)). Qed.
Lemma lem5488040 : term217 = True.
Proof. exact (EQ_MP (@lem5488039) (@lem5488037)). Qed.
Lemma lem5488041 : term211 = True.
Proof. exact (TRANS (@lem5488036) (@lem5488040)). Qed.
Lemma lem5488042 : True = term211.
Proof. exact (SYM (@lem5488041)). Qed.
Lemma lem5488043 : term211.
Proof. exact (EQ_MP (@lem5488042) (@lem0)). Qed.
Lemma lem5488044 : term219.
Proof. exact (@lem5488033 (@lem5488043)). Qed.
Lemma lem5488046 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488047 : term211 = term217.
Proof. exact (@lem5488046 (NUMERAL 0) term144). Qed.
Lemma lem5488048 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488049 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488050 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488049 h1) (fun h1 : term217 = True => @lem5488048)). Qed.
Lemma lem5488051 : term217 = True.
Proof. exact (EQ_MP (@lem5488050) (@lem5488048)). Qed.
Lemma lem5488052 : term211 = True.
Proof. exact (TRANS (@lem5488047) (@lem5488051)). Qed.
Lemma lem5488053 : True = term211.
Proof. exact (SYM (@lem5488052)). Qed.
Lemma lem5488054 : term211.
Proof. exact (EQ_MP (@lem5488053) (@lem0)). Qed.
Lemma lem5488055 : term214 = term220.
Proof. exact (@lem5488044 (@lem5488054)). Qed.
Lemma lem5488057 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488058 : term173 = term174.
Proof. exact (@lem5488057 term144 term144). Qed.
Lemma lem5488059 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488060 : term176 = term144.
Proof. exact (EQ_MP (@lem5488059) (@lem940073)). Qed.
Lemma lem5488061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488062 : term174 = term143.
Proof. exact (MK_COMB (@lem5488061) (@lem5488060)). Qed.
Lemma lem5488063 : term173 = term143.
Proof. exact (TRANS (@lem5488058) (@lem5488062)). Qed.
Lemma lem5488065 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488066 : term222 = term129.
Proof. exact (@lem5488065 term144). Qed.
Lemma lem5488067 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5488068 : term223 = term212.
Proof. exact (MK_COMB (@lem5488067) (@lem5488066)). Qed.
Lemma lem5488069 : term220 = term211.
Proof. exact (MK_COMB (@lem5488068) (@lem5488063)). Qed.
Lemma lem5488071 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488072 : term211 = term217.
Proof. exact (@lem5488071 (NUMERAL 0) term144). Qed.
Lemma lem5488073 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488074 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488075 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488074 h1) (fun h1 : term217 = True => @lem5488073)). Qed.
Lemma lem5488076 : term217 = True.
Proof. exact (EQ_MP (@lem5488075) (@lem5488073)). Qed.
Lemma lem5488077 : term211 = True.
Proof. exact (TRANS (@lem5488072) (@lem5488076)). Qed.
Lemma lem5488078 : term220 = True.
Proof. exact (TRANS (@lem5488069) (@lem5488077)). Qed.
Lemma lem5488079 : term214 = True.
Proof. exact (TRANS (@lem5488055) (@lem5488078)). Qed.
Lemma lem5488080 : term211 = True.
Proof. exact (TRANS (@lem5488032) (@lem5488079)). Qed.
Lemma lem5488081 : term210 = True.
Proof. exact (TRANS (@lem5488023) (@lem5488080)). Qed.
Lemma lem5488082 : True = term210.
Proof. exact (SYM (@lem5488081)). Qed.
Lemma lem5488083 : term210.
Proof. exact (EQ_MP (@lem5488082) (@lem0)). Qed.
Lemma lem5488084 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term230 _70607 _70608.
Proof. exact (conj (@lem5488083) (@lem5487946 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488086 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5488087 (_70607 : int) (_70608 : int) : term231 _70607 _70608.
Proof. exact (@lem5488086 term143 (term202 _70607 _70608)). Qed.
Lemma lem5488088 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term232 _70607 _70608.
Proof. exact (@lem5488087 _70607 _70608 (@lem5488084 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488089 (_70607 : int) (_70608 : int) : (term233 _70607 _70608) = (term202 _70607 _70608).
Proof. exact (@lem1982733 (term202 _70607 _70608)). Qed.
Lemma lem5488090 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5488091 (_70607 : int) (_70608 : int) : (term234 _70607 _70608) = (term204 _70607 _70608).
Proof. exact (MK_COMB (@lem5488090) (@lem5488089 _70607 _70608)). Qed.
Lemma lem5488092 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488093 (_70607 : int) (_70608 : int) : (term232 _70607 _70608) = (term205 _70607 _70608).
Proof. exact (MK_COMB (@lem5488091 _70607 _70608) (@lem5488092)). Qed.
Lemma lem5488094 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (EQ_MP (@lem5488093 _70607 _70608) (@lem5488088 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488096 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5488097 (_70606 : int) (_70607 : int) : term823 _70606 _70607.
Proof. exact (@lem5488096 (term552 _70606 _70607)). Qed.
Lemma lem5488098 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term824 _70606 _70607.
Proof. exact (@lem5488097 _70606 _70607 (@lem5487944 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488099 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term891 _70606 _70607.
Proof. exact (@lem5488098 _70607 _70606 _70608 h1 term164). Qed.
Lemma lem5488100 (_70606 : int) (_70607 : int) : (term891 _70606 _70607) = ((term892 _70606 _70607) = term129).
Proof. exact (eq_refl (term891 _70606 _70607)). Qed.
Lemma lem5488101 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : (term892 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5488100 _70606 _70607) (@lem5488099 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488102 (_70606 : int) (_70607 : int) : (term892 _70606 _70607) = (term893 _70606 _70607).
Proof. exact (@lem1982781 (term239 _70606) term164 (term546 _70607)). Qed.
Lemma lem5488103 (_70607 : int) : (term894 _70607) = (term895 _70607).
Proof. exact (@lem1982781 (real_of_int _70607) term164 term164). Qed.
Lemma lem5488105 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488106 : term164 = term165.
Proof. exact (@lem5488105 term144). Qed.
Lemma lem5488108 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488109 : term164 = term165.
Proof. exact (@lem5488108 term144). Qed.
Lemma lem5488110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488111 : term166 = term167.
Proof. exact (MK_COMB (@lem5488110) (@lem5488109)). Qed.
Lemma lem5488112 : term896 = term897.
Proof. exact (MK_COMB (@lem5488111) (@lem5488106)). Qed.
Lemma lem5488113 : term897 = term898.
Proof. exact (@lem1981613 term164 term164 term143 term143). Qed.
Lemma lem5488115 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488116 : term173 = term174.
Proof. exact (@lem5488115 term144 term144). Qed.
Lemma lem5488117 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488118 : term176 = term144.
Proof. exact (EQ_MP (@lem5488117) (@lem940073)). Qed.
Lemma lem5488119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488120 : term174 = term143.
Proof. exact (MK_COMB (@lem5488119) (@lem5488118)). Qed.
Lemma lem5488121 : term173 = term143.
Proof. exact (TRANS (@lem5488116) (@lem5488120)). Qed.
Lemma lem5488123 (m : nat) (n : nat) : (term899 m n) = (term172 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5488124 : term896 = term174.
Proof. exact (@lem5488123 term144 term144). Qed.
Lemma lem5488125 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488126 : term176 = term144.
Proof. exact (EQ_MP (@lem5488125) (@lem940073)). Qed.
Lemma lem5488127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488128 : term174 = term143.
Proof. exact (MK_COMB (@lem5488127) (@lem5488126)). Qed.
Lemma lem5488129 : term896 = term143.
Proof. exact (TRANS (@lem5488124) (@lem5488128)). Qed.
Lemma lem5488130 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5488131 : term900 = term901.
Proof. exact (MK_COMB (@lem5488130) (@lem5488129)). Qed.
Lemma lem5488132 : term898 = term191.
Proof. exact (MK_COMB (@lem5488131) (@lem5488121)). Qed.
Lemma lem5488133 : term897 = term191.
Proof. exact (TRANS (@lem5488113) (@lem5488132)). Qed.
Lemma lem5488134 : term896 = term191.
Proof. exact (TRANS (@lem5488112) (@lem5488133)). Qed.
Lemma lem5488136 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5488137 : term191 = term143.
Proof. exact (@lem5488136 term143). Qed.
Lemma lem5488138 : term896 = term143.
Proof. exact (TRANS (@lem5488134) (@lem5488137)). Qed.
Lemma lem5488141 (_70607 : int) : (term200 _70607) = (term200 _70607).
Proof. exact (eq_refl (term200 _70607)). Qed.
Lemma lem5488142 (_70607 : int) : (term895 _70607) = (term902 _70607).
Proof. exact (MK_COMB (@lem5488141 _70607) (@lem5488138)). Qed.
Lemma lem5488143 (_70607 : int) : (term894 _70607) = (term902 _70607).
Proof. exact (TRANS (@lem5488103 _70607) (@lem5488142 _70607)). Qed.
Lemma lem5488144 (_70606 : int) : (term903 _70606) = (term904 _70606).
Proof. exact (@lem1982749 term164 term164 (real_of_int _70606)). Qed.
Lemma lem5488146 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488147 : term164 = term165.
Proof. exact (@lem5488146 term144). Qed.
Lemma lem5488149 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488150 : term164 = term165.
Proof. exact (@lem5488149 term144). Qed.
Lemma lem5488151 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488152 : term166 = term167.
Proof. exact (MK_COMB (@lem5488151) (@lem5488150)). Qed.
Lemma lem5488153 : term896 = term897.
Proof. exact (MK_COMB (@lem5488152) (@lem5488147)). Qed.
Lemma lem5488154 : term897 = term898.
Proof. exact (@lem1981613 term164 term164 term143 term143). Qed.
Lemma lem5488156 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488157 : term173 = term174.
Proof. exact (@lem5488156 term144 term144). Qed.
Lemma lem5488158 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488159 : term176 = term144.
Proof. exact (EQ_MP (@lem5488158) (@lem940073)). Qed.
Lemma lem5488160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488161 : term174 = term143.
Proof. exact (MK_COMB (@lem5488160) (@lem5488159)). Qed.
Lemma lem5488162 : term173 = term143.
Proof. exact (TRANS (@lem5488157) (@lem5488161)). Qed.
Lemma lem5488164 (m : nat) (n : nat) : (term899 m n) = (term172 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5488165 : term896 = term174.
Proof. exact (@lem5488164 term144 term144). Qed.
Lemma lem5488166 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488167 : term176 = term144.
Proof. exact (EQ_MP (@lem5488166) (@lem940073)). Qed.
Lemma lem5488168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488169 : term174 = term143.
Proof. exact (MK_COMB (@lem5488168) (@lem5488167)). Qed.
Lemma lem5488170 : term896 = term143.
Proof. exact (TRANS (@lem5488165) (@lem5488169)). Qed.
Lemma lem5488171 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5488172 : term900 = term901.
Proof. exact (MK_COMB (@lem5488171) (@lem5488170)). Qed.
Lemma lem5488173 : term898 = term191.
Proof. exact (MK_COMB (@lem5488172) (@lem5488162)). Qed.
Lemma lem5488174 : term897 = term191.
Proof. exact (TRANS (@lem5488154) (@lem5488173)). Qed.
Lemma lem5488175 : term896 = term191.
Proof. exact (TRANS (@lem5488153) (@lem5488174)). Qed.
Lemma lem5488177 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5488178 : term191 = term143.
Proof. exact (@lem5488177 term143). Qed.
Lemma lem5488179 : term896 = term143.
Proof. exact (TRANS (@lem5488175) (@lem5488178)). Qed.
Lemma lem5488180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488181 : term905 = term906.
Proof. exact (MK_COMB (@lem5488180) (@lem5488179)). Qed.
Lemma lem5488182 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5488183 (_70606 : int) : (term904 _70606) = (term228 _70606).
Proof. exact (MK_COMB (@lem5488181) (@lem5488182 _70606)). Qed.
Lemma lem5488184 (_70606 : int) : (term903 _70606) = (term228 _70606).
Proof. exact (TRANS (@lem5488144 _70606) (@lem5488183 _70606)). Qed.
Lemma lem5488185 (_70606 : int) : (term228 _70606) = (real_of_int _70606).
Proof. exact (@lem1982709 (real_of_int _70606)). Qed.
Lemma lem5488186 (_70606 : int) : (term903 _70606) = (real_of_int _70606).
Proof. exact (TRANS (@lem5488184 _70606) (@lem5488185 _70606)). Qed.
Lemma lem5488187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488188 (_70606 : int) : (term907 _70606) = (term145 _70606).
Proof. exact (MK_COMB (@lem5488187) (@lem5488186 _70606)). Qed.
Lemma lem5488189 (_70606 : int) (_70607 : int) : (term893 _70606 _70607) = (term908 _70606 _70607).
Proof. exact (MK_COMB (@lem5488188 _70606) (@lem5488143 _70607)). Qed.
Lemma lem5488190 (_70606 : int) (_70607 : int) : (term892 _70606 _70607) = (term908 _70606 _70607).
Proof. exact (TRANS (@lem5488102 _70606 _70607) (@lem5488189 _70606 _70607)). Qed.
Lemma lem5488191 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5488192 (_70606 : int) (_70607 : int) : (term909 _70606 _70607) = (term910 _70606 _70607).
Proof. exact (MK_COMB (@lem5488191) (@lem5488190 _70606 _70607)). Qed.
Lemma lem5488193 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488194 (_70606 : int) (_70607 : int) : ((term892 _70606 _70607) = term129) = ((term908 _70606 _70607) = term129).
Proof. exact (MK_COMB (@lem5488192 _70606 _70607) (@lem5488193)). Qed.
Lemma lem5488195 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : (term908 _70606 _70607) = term129.
Proof. exact (EQ_MP (@lem5488194 _70606 _70607) (@lem5488101 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488196 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term911 _70606 _70607 _70608.
Proof. exact (conj (@lem5488195 _70607 _70606 _70608 h1) (@lem5488094 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488198 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5488199 (_70606 : int) (_70607 : int) (_70608 : int) : term912 _70606 _70607 _70608.
Proof. exact (@lem5488198 (term908 _70606 _70607) (term202 _70607 _70608)). Qed.
Lemma lem5488200 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term913 _70606 _70607 _70608.
Proof. exact (@lem5488199 _70606 _70607 _70608 (@lem5488196 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488201 (_70606 : int) (_70607 : int) (_70608 : int) : (term914 _70606 _70607 _70608) = (term915 _70606 _70607 _70608).
Proof. exact (@lem1982755 (real_of_int _70606) (term902 _70607) (term202 _70607 _70608)). Qed.
Lemma lem5488202 (_70607 : int) (_70608 : int) : (term916 _70607 _70608) = (term917 _70607 _70608).
Proof. exact (@lem1982753 (term239 _70607) (real_of_int _70607) term143 (term201 _70608)). Qed.
Lemma lem5488203 (_70607 : int) : (term246 _70607) = (term247 _70607).
Proof. exact (@lem1982713 term164 (real_of_int _70607)). Qed.
Lemma lem5488205 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488206 : term143 = term191.
Proof. exact (@lem5488205 term144). Qed.
Lemma lem5488208 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488209 : term164 = term165.
Proof. exact (@lem5488208 term144). Qed.
Lemma lem5488210 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488211 : term248 = term249.
Proof. exact (MK_COMB (@lem5488210) (@lem5488209)). Qed.
Lemma lem5488212 : term250 = term251.
Proof. exact (MK_COMB (@lem5488211) (@lem5488206)). Qed.
Lemma lem5488213 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5488215 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488216 : term211 = term217.
Proof. exact (@lem5488215 (NUMERAL 0) term144). Qed.
Lemma lem5488217 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488218 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488219 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488218 h1) (fun h1 : term217 = True => @lem5488217)). Qed.
Lemma lem5488220 : term217 = True.
Proof. exact (EQ_MP (@lem5488219) (@lem5488217)). Qed.
Lemma lem5488221 : term211 = True.
Proof. exact (TRANS (@lem5488216) (@lem5488220)). Qed.
Lemma lem5488222 : True = term211.
Proof. exact (SYM (@lem5488221)). Qed.
Lemma lem5488223 : term211.
Proof. exact (EQ_MP (@lem5488222) (@lem0)). Qed.
Lemma lem5488224 : term253.
Proof. exact (@lem5488213 (@lem5488223)). Qed.
Lemma lem5488226 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488227 : term211 = term217.
Proof. exact (@lem5488226 (NUMERAL 0) term144). Qed.
Lemma lem5488228 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488229 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488230 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488229 h1) (fun h1 : term217 = True => @lem5488228)). Qed.
Lemma lem5488231 : term217 = True.
Proof. exact (EQ_MP (@lem5488230) (@lem5488228)). Qed.
Lemma lem5488232 : term211 = True.
Proof. exact (TRANS (@lem5488227) (@lem5488231)). Qed.
Lemma lem5488233 : True = term211.
Proof. exact (SYM (@lem5488232)). Qed.
Lemma lem5488234 : term211.
Proof. exact (EQ_MP (@lem5488233) (@lem0)). Qed.
Lemma lem5488235 : term254.
Proof. exact (@lem5488224 (@lem5488234)). Qed.
Lemma lem5488237 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488238 : term211 = term217.
Proof. exact (@lem5488237 (NUMERAL 0) term144). Qed.
Lemma lem5488239 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488240 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488241 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488240 h1) (fun h1 : term217 = True => @lem5488239)). Qed.
Lemma lem5488242 : term217 = True.
Proof. exact (EQ_MP (@lem5488241) (@lem5488239)). Qed.
Lemma lem5488243 : term211 = True.
Proof. exact (TRANS (@lem5488238) (@lem5488242)). Qed.
Lemma lem5488244 : True = term211.
Proof. exact (SYM (@lem5488243)). Qed.
Lemma lem5488245 : term211.
Proof. exact (EQ_MP (@lem5488244) (@lem0)). Qed.
Lemma lem5488246 : term255.
Proof. exact (@lem5488235 (@lem5488245)). Qed.
Lemma lem5488248 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488249 : term173 = term174.
Proof. exact (@lem5488248 term144 term144). Qed.
Lemma lem5488250 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488251 : term176 = term144.
Proof. exact (EQ_MP (@lem5488250) (@lem940073)). Qed.
Lemma lem5488252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488253 : term174 = term143.
Proof. exact (MK_COMB (@lem5488252) (@lem5488251)). Qed.
Lemma lem5488254 : term173 = term143.
Proof. exact (TRANS (@lem5488249) (@lem5488253)). Qed.
Lemma lem5488256 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5488257 : term192 = term197.
Proof. exact (@lem5488256 term144 term144). Qed.
Lemma lem5488258 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488259 : term176 = term144.
Proof. exact (EQ_MP (@lem5488258) (@lem940073)). Qed.
Lemma lem5488260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488261 : term174 = term143.
Proof. exact (MK_COMB (@lem5488260) (@lem5488259)). Qed.
Lemma lem5488262 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5488263 : term197 = term164.
Proof. exact (MK_COMB (@lem5488262) (@lem5488261)). Qed.
Lemma lem5488264 : term192 = term164.
Proof. exact (TRANS (@lem5488257) (@lem5488263)). Qed.
Lemma lem5488265 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488266 : term256 = term248.
Proof. exact (MK_COMB (@lem5488265) (@lem5488264)). Qed.
Lemma lem5488267 : term257 = term250.
Proof. exact (MK_COMB (@lem5488266) (@lem5488254)). Qed.
Lemma lem5488269 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5488270 : term250 = term129.
Proof. exact (@lem5488269 term144). Qed.
Lemma lem5488271 : term257 = term129.
Proof. exact (TRANS (@lem5488267) (@lem5488270)). Qed.
Lemma lem5488272 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488273 : term259 = term260.
Proof. exact (MK_COMB (@lem5488272) (@lem5488271)). Qed.
Lemma lem5488274 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5488275 : term261 = term222.
Proof. exact (MK_COMB (@lem5488273) (@lem5488274)). Qed.
Lemma lem5488277 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488278 : term222 = term129.
Proof. exact (@lem5488277 term144). Qed.
Lemma lem5488279 : term261 = term129.
Proof. exact (TRANS (@lem5488275) (@lem5488278)). Qed.
Lemma lem5488281 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488282 : term173 = term174.
Proof. exact (@lem5488281 term144 term144). Qed.
Lemma lem5488283 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488284 : term176 = term144.
Proof. exact (EQ_MP (@lem5488283) (@lem940073)). Qed.
Lemma lem5488285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488286 : term174 = term143.
Proof. exact (MK_COMB (@lem5488285) (@lem5488284)). Qed.
Lemma lem5488287 : term173 = term143.
Proof. exact (TRANS (@lem5488282) (@lem5488286)). Qed.
Lemma lem5488288 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5488289 : term262 = term222.
Proof. exact (MK_COMB (@lem5488288) (@lem5488287)). Qed.
Lemma lem5488291 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488292 : term222 = term129.
Proof. exact (@lem5488291 term144). Qed.
Lemma lem5488293 : term262 = term129.
Proof. exact (TRANS (@lem5488289) (@lem5488292)). Qed.
Lemma lem5488294 : term129 = term262.
Proof. exact (SYM (@lem5488293)). Qed.
Lemma lem5488295 : term261 = term262.
Proof. exact (TRANS (@lem5488279) (@lem5488294)). Qed.
Lemma lem5488296 : term251 = term161.
Proof. exact (@lem5488246 (@lem5488295)). Qed.
Lemma lem5488297 : term250 = term161.
Proof. exact (TRANS (@lem5488212) (@lem5488296)). Qed.
Lemma lem5488299 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5488300 : term161 = term129.
Proof. exact (@lem5488299 term129). Qed.
Lemma lem5488301 : term250 = term129.
Proof. exact (TRANS (@lem5488297) (@lem5488300)). Qed.
Lemma lem5488302 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488303 : term263 = term260.
Proof. exact (MK_COMB (@lem5488302) (@lem5488301)). Qed.
Lemma lem5488304 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5488305 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5488303) (@lem5488304 _70607)). Qed.
Lemma lem5488306 (_70607 : int) : (term246 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5488203 _70607) (@lem5488305 _70607)). Qed.
Lemma lem5488307 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5488308 (_70607 : int) : (term246 _70607) = term129.
Proof. exact (TRANS (@lem5488306 _70607) (@lem5488307 _70607)). Qed.
Lemma lem5488309 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488310 (_70607 : int) : (term265 _70607) = term266.
Proof. exact (MK_COMB (@lem5488309) (@lem5488308 _70607)). Qed.
Lemma lem5488311 (_70608 : int) : (term559 _70608) = (term560 _70608).
Proof. exact (@lem1982757 (term239 _70608) term143 term164). Qed.
Lemma lem5488313 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488314 : term164 = term165.
Proof. exact (@lem5488313 term144). Qed.
Lemma lem5488316 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488317 : term143 = term191.
Proof. exact (@lem5488316 term144). Qed.
Lemma lem5488318 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488319 : term558 = term561.
Proof. exact (MK_COMB (@lem5488318) (@lem5488317)). Qed.
Lemma lem5488320 : term562 = term563.
Proof. exact (MK_COMB (@lem5488319) (@lem5488314)). Qed.
Lemma lem5488321 : term564.
Proof. exact (@lem1981473 term143 term143 term164 term143 term129 term143). Qed.
Lemma lem5488323 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488324 : term211 = term217.
Proof. exact (@lem5488323 (NUMERAL 0) term144). Qed.
Lemma lem5488325 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488326 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488327 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488326 h1) (fun h1 : term217 = True => @lem5488325)). Qed.
Lemma lem5488328 : term217 = True.
Proof. exact (EQ_MP (@lem5488327) (@lem5488325)). Qed.
Lemma lem5488329 : term211 = True.
Proof. exact (TRANS (@lem5488324) (@lem5488328)). Qed.
Lemma lem5488330 : True = term211.
Proof. exact (SYM (@lem5488329)). Qed.
Lemma lem5488331 : term211.
Proof. exact (EQ_MP (@lem5488330) (@lem0)). Qed.
Lemma lem5488332 : term565.
Proof. exact (@lem5488321 (@lem5488331)). Qed.
Lemma lem5488334 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488335 : term211 = term217.
Proof. exact (@lem5488334 (NUMERAL 0) term144). Qed.
Lemma lem5488336 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488337 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488338 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488337 h1) (fun h1 : term217 = True => @lem5488336)). Qed.
Lemma lem5488339 : term217 = True.
Proof. exact (EQ_MP (@lem5488338) (@lem5488336)). Qed.
Lemma lem5488340 : term211 = True.
Proof. exact (TRANS (@lem5488335) (@lem5488339)). Qed.
Lemma lem5488341 : True = term211.
Proof. exact (SYM (@lem5488340)). Qed.
Lemma lem5488342 : term211.
Proof. exact (EQ_MP (@lem5488341) (@lem0)). Qed.
Lemma lem5488343 : term566.
Proof. exact (@lem5488332 (@lem5488342)). Qed.
Lemma lem5488345 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488346 : term211 = term217.
Proof. exact (@lem5488345 (NUMERAL 0) term144). Qed.
Lemma lem5488347 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488348 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488349 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488348 h1) (fun h1 : term217 = True => @lem5488347)). Qed.
Lemma lem5488350 : term217 = True.
Proof. exact (EQ_MP (@lem5488349) (@lem5488347)). Qed.
Lemma lem5488351 : term211 = True.
Proof. exact (TRANS (@lem5488346) (@lem5488350)). Qed.
Lemma lem5488352 : True = term211.
Proof. exact (SYM (@lem5488351)). Qed.
Lemma lem5488353 : term211.
Proof. exact (EQ_MP (@lem5488352) (@lem0)). Qed.
Lemma lem5488354 : term567.
Proof. exact (@lem5488343 (@lem5488353)). Qed.
Lemma lem5488356 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5488357 : term192 = term197.
Proof. exact (@lem5488356 term144 term144). Qed.
Lemma lem5488358 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488359 : term176 = term144.
Proof. exact (EQ_MP (@lem5488358) (@lem940073)). Qed.
Lemma lem5488360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488361 : term174 = term143.
Proof. exact (MK_COMB (@lem5488360) (@lem5488359)). Qed.
Lemma lem5488362 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5488363 : term197 = term164.
Proof. exact (MK_COMB (@lem5488362) (@lem5488361)). Qed.
Lemma lem5488364 : term192 = term164.
Proof. exact (TRANS (@lem5488357) (@lem5488363)). Qed.
Lemma lem5488366 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488367 : term173 = term174.
Proof. exact (@lem5488366 term144 term144). Qed.
Lemma lem5488368 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488369 : term176 = term144.
Proof. exact (EQ_MP (@lem5488368) (@lem940073)). Qed.
Lemma lem5488370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488371 : term174 = term143.
Proof. exact (MK_COMB (@lem5488370) (@lem5488369)). Qed.
Lemma lem5488372 : term173 = term143.
Proof. exact (TRANS (@lem5488367) (@lem5488371)). Qed.
Lemma lem5488373 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488374 : term568 = term558.
Proof. exact (MK_COMB (@lem5488373) (@lem5488372)). Qed.
Lemma lem5488375 : term569 = term562.
Proof. exact (MK_COMB (@lem5488374) (@lem5488364)). Qed.
Lemma lem5488377 (m : nat) : (term570 m) = term129.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5488378 : term562 = term129.
Proof. exact (@lem5488377 term144). Qed.
Lemma lem5488379 : term569 = term129.
Proof. exact (TRANS (@lem5488375) (@lem5488378)). Qed.
Lemma lem5488380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488381 : term571 = term260.
Proof. exact (MK_COMB (@lem5488380) (@lem5488379)). Qed.
Lemma lem5488382 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5488383 : term572 = term222.
Proof. exact (MK_COMB (@lem5488381) (@lem5488382)). Qed.
Lemma lem5488385 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488386 : term222 = term129.
Proof. exact (@lem5488385 term144). Qed.
Lemma lem5488387 : term572 = term129.
Proof. exact (TRANS (@lem5488383) (@lem5488386)). Qed.
Lemma lem5488389 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488390 : term173 = term174.
Proof. exact (@lem5488389 term144 term144). Qed.
Lemma lem5488391 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488392 : term176 = term144.
Proof. exact (EQ_MP (@lem5488391) (@lem940073)). Qed.
Lemma lem5488393 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488394 : term174 = term143.
Proof. exact (MK_COMB (@lem5488393) (@lem5488392)). Qed.
Lemma lem5488395 : term173 = term143.
Proof. exact (TRANS (@lem5488390) (@lem5488394)). Qed.
Lemma lem5488396 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5488397 : term262 = term222.
Proof. exact (MK_COMB (@lem5488396) (@lem5488395)). Qed.
Lemma lem5488399 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488400 : term222 = term129.
Proof. exact (@lem5488399 term144). Qed.
Lemma lem5488401 : term262 = term129.
Proof. exact (TRANS (@lem5488397) (@lem5488400)). Qed.
Lemma lem5488402 : term129 = term262.
Proof. exact (SYM (@lem5488401)). Qed.
Lemma lem5488403 : term572 = term262.
Proof. exact (TRANS (@lem5488387) (@lem5488402)). Qed.
Lemma lem5488404 : term563 = term161.
Proof. exact (@lem5488354 (@lem5488403)). Qed.
Lemma lem5488405 : term562 = term161.
Proof. exact (TRANS (@lem5488320) (@lem5488404)). Qed.
Lemma lem5488407 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5488408 : term161 = term129.
Proof. exact (@lem5488407 term129). Qed.
Lemma lem5488409 : term562 = term129.
Proof. exact (TRANS (@lem5488405) (@lem5488408)). Qed.
Lemma lem5488410 (_70608 : int) : (term200 _70608) = (term200 _70608).
Proof. exact (eq_refl (term200 _70608)). Qed.
Lemma lem5488411 (_70608 : int) : (term560 _70608) = (term573 _70608).
Proof. exact (MK_COMB (@lem5488410 _70608) (@lem5488409)). Qed.
Lemma lem5488412 (_70608 : int) : (term559 _70608) = (term573 _70608).
Proof. exact (TRANS (@lem5488311 _70608) (@lem5488411 _70608)). Qed.
Lemma lem5488413 (_70608 : int) : (term573 _70608) = (term239 _70608).
Proof. exact (@lem1982723 (term239 _70608)). Qed.
Lemma lem5488414 (_70608 : int) : (term559 _70608) = (term239 _70608).
Proof. exact (TRANS (@lem5488412 _70608) (@lem5488413 _70608)). Qed.
Lemma lem5488415 (_70607 : int) (_70608 : int) : (term917 _70607 _70608) = (term869 _70608).
Proof. exact (MK_COMB (@lem5488310 _70607) (@lem5488414 _70608)). Qed.
Lemma lem5488416 (_70607 : int) (_70608 : int) : (term916 _70607 _70608) = (term869 _70608).
Proof. exact (TRANS (@lem5488202 _70607 _70608) (@lem5488415 _70607 _70608)). Qed.
Lemma lem5488417 (_70608 : int) : (term869 _70608) = (term239 _70608).
Proof. exact (@lem1982721 (term239 _70608)). Qed.
Lemma lem5488418 (_70607 : int) (_70608 : int) : (term916 _70607 _70608) = (term239 _70608).
Proof. exact (TRANS (@lem5488416 _70607 _70608) (@lem5488417 _70608)). Qed.
Lemma lem5488419 (_70606 : int) : (term145 _70606) = (term145 _70606).
Proof. exact (eq_refl (term145 _70606)). Qed.
Lemma lem5488420 (_70607 : int) (_70606 : int) (_70608 : int) : (term915 _70606 _70607 _70608) = (term583 _70606 _70608).
Proof. exact (MK_COMB (@lem5488419 _70606) (@lem5488418 _70607 _70608)). Qed.
Lemma lem5488421 (_70607 : int) (_70606 : int) (_70608 : int) : (term914 _70606 _70607 _70608) = (term583 _70606 _70608).
Proof. exact (TRANS (@lem5488201 _70606 _70607 _70608) (@lem5488420 _70607 _70606 _70608)). Qed.
Lemma lem5488422 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5488423 (_70607 : int) (_70606 : int) (_70608 : int) : (term918 _70606 _70607 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5488422) (@lem5488421 _70607 _70606 _70608)). Qed.
Lemma lem5488424 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488425 (_70607 : int) (_70606 : int) (_70608 : int) : (term913 _70606 _70607 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5488423 _70607 _70606 _70608) (@lem5488424)). Qed.
Lemma lem5488426 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (EQ_MP (@lem5488425 _70607 _70606 _70608) (@lem5488200 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488428 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5488429 : term210 = term211.
Proof. exact (@lem5488428 term129 term143). Qed.
Lemma lem5488431 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488432 : term143 = term191.
Proof. exact (@lem5488431 term144). Qed.
Lemma lem5488434 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488435 : term129 = term161.
Proof. exact (@lem5488434 (NUMERAL 0)). Qed.
Lemma lem5488436 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5488437 : term212 = term213.
Proof. exact (MK_COMB (@lem5488436) (@lem5488435)). Qed.
Lemma lem5488438 : term211 = term214.
Proof. exact (MK_COMB (@lem5488437) (@lem5488432)). Qed.
Lemma lem5488439 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5488441 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488442 : term211 = term217.
Proof. exact (@lem5488441 (NUMERAL 0) term144). Qed.
Lemma lem5488443 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488444 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488445 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488444 h1) (fun h1 : term217 = True => @lem5488443)). Qed.
Lemma lem5488446 : term217 = True.
Proof. exact (EQ_MP (@lem5488445) (@lem5488443)). Qed.
Lemma lem5488447 : term211 = True.
Proof. exact (TRANS (@lem5488442) (@lem5488446)). Qed.
Lemma lem5488448 : True = term211.
Proof. exact (SYM (@lem5488447)). Qed.
Lemma lem5488449 : term211.
Proof. exact (EQ_MP (@lem5488448) (@lem0)). Qed.
Lemma lem5488450 : term219.
Proof. exact (@lem5488439 (@lem5488449)). Qed.
Lemma lem5488452 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488453 : term211 = term217.
Proof. exact (@lem5488452 (NUMERAL 0) term144). Qed.
Lemma lem5488454 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488455 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488456 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488455 h1) (fun h1 : term217 = True => @lem5488454)). Qed.
Lemma lem5488457 : term217 = True.
Proof. exact (EQ_MP (@lem5488456) (@lem5488454)). Qed.
Lemma lem5488458 : term211 = True.
Proof. exact (TRANS (@lem5488453) (@lem5488457)). Qed.
Lemma lem5488459 : True = term211.
Proof. exact (SYM (@lem5488458)). Qed.
Lemma lem5488460 : term211.
Proof. exact (EQ_MP (@lem5488459) (@lem0)). Qed.
Lemma lem5488461 : term214 = term220.
Proof. exact (@lem5488450 (@lem5488460)). Qed.
Lemma lem5488463 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488464 : term173 = term174.
Proof. exact (@lem5488463 term144 term144). Qed.
Lemma lem5488465 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488466 : term176 = term144.
Proof. exact (EQ_MP (@lem5488465) (@lem940073)). Qed.
Lemma lem5488467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488468 : term174 = term143.
Proof. exact (MK_COMB (@lem5488467) (@lem5488466)). Qed.
Lemma lem5488469 : term173 = term143.
Proof. exact (TRANS (@lem5488464) (@lem5488468)). Qed.
Lemma lem5488471 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488472 : term222 = term129.
Proof. exact (@lem5488471 term144). Qed.
Lemma lem5488473 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5488474 : term223 = term212.
Proof. exact (MK_COMB (@lem5488473) (@lem5488472)). Qed.
Lemma lem5488475 : term220 = term211.
Proof. exact (MK_COMB (@lem5488474) (@lem5488469)). Qed.
Lemma lem5488477 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488478 : term211 = term217.
Proof. exact (@lem5488477 (NUMERAL 0) term144). Qed.
Lemma lem5488479 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488480 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488481 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488480 h1) (fun h1 : term217 = True => @lem5488479)). Qed.
Lemma lem5488482 : term217 = True.
Proof. exact (EQ_MP (@lem5488481) (@lem5488479)). Qed.
Lemma lem5488483 : term211 = True.
Proof. exact (TRANS (@lem5488478) (@lem5488482)). Qed.
Lemma lem5488484 : term220 = True.
Proof. exact (TRANS (@lem5488475) (@lem5488483)). Qed.
Lemma lem5488485 : term214 = True.
Proof. exact (TRANS (@lem5488461) (@lem5488484)). Qed.
Lemma lem5488486 : term211 = True.
Proof. exact (TRANS (@lem5488438) (@lem5488485)). Qed.
Lemma lem5488487 : term210 = True.
Proof. exact (TRANS (@lem5488429) (@lem5488486)). Qed.
Lemma lem5488488 : True = term210.
Proof. exact (SYM (@lem5488487)). Qed.
Lemma lem5488489 : term210.
Proof. exact (EQ_MP (@lem5488488) (@lem0)). Qed.
Lemma lem5488490 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term844 _70606 _70608.
Proof. exact (conj (@lem5488489) (@lem5488426 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488492 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5488493 (_70606 : int) (_70608 : int) : term845 _70606 _70608.
Proof. exact (@lem5488492 term143 (term583 _70606 _70608)). Qed.
Lemma lem5488494 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term846 _70606 _70608.
Proof. exact (@lem5488493 _70606 _70608 (@lem5488490 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488495 (_70606 : int) (_70608 : int) : (term847 _70606 _70608) = (term583 _70606 _70608).
Proof. exact (@lem1982733 (term583 _70606 _70608)). Qed.
Lemma lem5488496 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5488497 (_70606 : int) (_70608 : int) : (term848 _70606 _70608) = (term588 _70606 _70608).
Proof. exact (MK_COMB (@lem5488496) (@lem5488495 _70606 _70608)). Qed.
Lemma lem5488498 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488499 (_70606 : int) (_70608 : int) : (term846 _70606 _70608) = (term589 _70606 _70608).
Proof. exact (MK_COMB (@lem5488497 _70606 _70608) (@lem5488498)). Qed.
Lemma lem5488500 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term589 _70606 _70608.
Proof. exact (EQ_MP (@lem5488499 _70606 _70608) (@lem5488494 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488501 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term849 _70606 _70608.
Proof. exact (conj (@lem5488500 _70607 _70606 _70608 h1) (@lem5488020 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488503 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5488504 (_70606 : int) (_70608 : int) : term850 _70606 _70608.
Proof. exact (@lem5488503 (term583 _70606 _70608) (term552 _70606 _70608)). Qed.
Lemma lem5488505 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term851 _70606 _70608.
Proof. exact (@lem5488504 _70606 _70608 (@lem5488501 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488506 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = (term853 _70606 _70608).
Proof. exact (@lem1982753 (real_of_int _70606) (term239 _70606) (term239 _70608) (term546 _70608)). Qed.
Lemma lem5488507 (_70606 : int) : (term835 _70606) = (term247 _70606).
Proof. exact (@lem1982715 term164 (real_of_int _70606)). Qed.
Lemma lem5488509 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488510 : term143 = term191.
Proof. exact (@lem5488509 term144). Qed.
Lemma lem5488512 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488513 : term164 = term165.
Proof. exact (@lem5488512 term144). Qed.
Lemma lem5488514 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488515 : term248 = term249.
Proof. exact (MK_COMB (@lem5488514) (@lem5488513)). Qed.
Lemma lem5488516 : term250 = term251.
Proof. exact (MK_COMB (@lem5488515) (@lem5488510)). Qed.
Lemma lem5488517 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5488519 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488520 : term211 = term217.
Proof. exact (@lem5488519 (NUMERAL 0) term144). Qed.
Lemma lem5488521 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488522 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488523 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488522 h1) (fun h1 : term217 = True => @lem5488521)). Qed.
Lemma lem5488524 : term217 = True.
Proof. exact (EQ_MP (@lem5488523) (@lem5488521)). Qed.
Lemma lem5488525 : term211 = True.
Proof. exact (TRANS (@lem5488520) (@lem5488524)). Qed.
Lemma lem5488526 : True = term211.
Proof. exact (SYM (@lem5488525)). Qed.
Lemma lem5488527 : term211.
Proof. exact (EQ_MP (@lem5488526) (@lem0)). Qed.
Lemma lem5488528 : term253.
Proof. exact (@lem5488517 (@lem5488527)). Qed.
Lemma lem5488530 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488531 : term211 = term217.
Proof. exact (@lem5488530 (NUMERAL 0) term144). Qed.
Lemma lem5488532 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488533 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488534 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488533 h1) (fun h1 : term217 = True => @lem5488532)). Qed.
Lemma lem5488535 : term217 = True.
Proof. exact (EQ_MP (@lem5488534) (@lem5488532)). Qed.
Lemma lem5488536 : term211 = True.
Proof. exact (TRANS (@lem5488531) (@lem5488535)). Qed.
Lemma lem5488537 : True = term211.
Proof. exact (SYM (@lem5488536)). Qed.
Lemma lem5488538 : term211.
Proof. exact (EQ_MP (@lem5488537) (@lem0)). Qed.
Lemma lem5488539 : term254.
Proof. exact (@lem5488528 (@lem5488538)). Qed.
Lemma lem5488541 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488542 : term211 = term217.
Proof. exact (@lem5488541 (NUMERAL 0) term144). Qed.
Lemma lem5488543 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488544 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488545 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488544 h1) (fun h1 : term217 = True => @lem5488543)). Qed.
Lemma lem5488546 : term217 = True.
Proof. exact (EQ_MP (@lem5488545) (@lem5488543)). Qed.
Lemma lem5488547 : term211 = True.
Proof. exact (TRANS (@lem5488542) (@lem5488546)). Qed.
Lemma lem5488548 : True = term211.
Proof. exact (SYM (@lem5488547)). Qed.
Lemma lem5488549 : term211.
Proof. exact (EQ_MP (@lem5488548) (@lem0)). Qed.
Lemma lem5488550 : term255.
Proof. exact (@lem5488539 (@lem5488549)). Qed.
Lemma lem5488552 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488553 : term173 = term174.
Proof. exact (@lem5488552 term144 term144). Qed.
Lemma lem5488554 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488555 : term176 = term144.
Proof. exact (EQ_MP (@lem5488554) (@lem940073)). Qed.
Lemma lem5488556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488557 : term174 = term143.
Proof. exact (MK_COMB (@lem5488556) (@lem5488555)). Qed.
Lemma lem5488558 : term173 = term143.
Proof. exact (TRANS (@lem5488553) (@lem5488557)). Qed.
Lemma lem5488560 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5488561 : term192 = term197.
Proof. exact (@lem5488560 term144 term144). Qed.
Lemma lem5488562 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488563 : term176 = term144.
Proof. exact (EQ_MP (@lem5488562) (@lem940073)). Qed.
Lemma lem5488564 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488565 : term174 = term143.
Proof. exact (MK_COMB (@lem5488564) (@lem5488563)). Qed.
Lemma lem5488566 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5488567 : term197 = term164.
Proof. exact (MK_COMB (@lem5488566) (@lem5488565)). Qed.
Lemma lem5488568 : term192 = term164.
Proof. exact (TRANS (@lem5488561) (@lem5488567)). Qed.
Lemma lem5488569 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488570 : term256 = term248.
Proof. exact (MK_COMB (@lem5488569) (@lem5488568)). Qed.
Lemma lem5488571 : term257 = term250.
Proof. exact (MK_COMB (@lem5488570) (@lem5488558)). Qed.
Lemma lem5488573 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5488574 : term250 = term129.
Proof. exact (@lem5488573 term144). Qed.
Lemma lem5488575 : term257 = term129.
Proof. exact (TRANS (@lem5488571) (@lem5488574)). Qed.
Lemma lem5488576 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488577 : term259 = term260.
Proof. exact (MK_COMB (@lem5488576) (@lem5488575)). Qed.
Lemma lem5488578 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5488579 : term261 = term222.
Proof. exact (MK_COMB (@lem5488577) (@lem5488578)). Qed.
Lemma lem5488581 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488582 : term222 = term129.
Proof. exact (@lem5488581 term144). Qed.
Lemma lem5488583 : term261 = term129.
Proof. exact (TRANS (@lem5488579) (@lem5488582)). Qed.
Lemma lem5488585 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488586 : term173 = term174.
Proof. exact (@lem5488585 term144 term144). Qed.
Lemma lem5488587 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488588 : term176 = term144.
Proof. exact (EQ_MP (@lem5488587) (@lem940073)). Qed.
Lemma lem5488589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488590 : term174 = term143.
Proof. exact (MK_COMB (@lem5488589) (@lem5488588)). Qed.
Lemma lem5488591 : term173 = term143.
Proof. exact (TRANS (@lem5488586) (@lem5488590)). Qed.
Lemma lem5488592 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5488593 : term262 = term222.
Proof. exact (MK_COMB (@lem5488592) (@lem5488591)). Qed.
Lemma lem5488595 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488596 : term222 = term129.
Proof. exact (@lem5488595 term144). Qed.
Lemma lem5488597 : term262 = term129.
Proof. exact (TRANS (@lem5488593) (@lem5488596)). Qed.
Lemma lem5488598 : term129 = term262.
Proof. exact (SYM (@lem5488597)). Qed.
Lemma lem5488599 : term261 = term262.
Proof. exact (TRANS (@lem5488583) (@lem5488598)). Qed.
Lemma lem5488600 : term251 = term161.
Proof. exact (@lem5488550 (@lem5488599)). Qed.
Lemma lem5488601 : term250 = term161.
Proof. exact (TRANS (@lem5488516) (@lem5488600)). Qed.
Lemma lem5488603 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5488604 : term161 = term129.
Proof. exact (@lem5488603 term129). Qed.
Lemma lem5488605 : term250 = term129.
Proof. exact (TRANS (@lem5488601) (@lem5488604)). Qed.
Lemma lem5488606 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488607 : term263 = term260.
Proof. exact (MK_COMB (@lem5488606) (@lem5488605)). Qed.
Lemma lem5488608 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5488609 (_70606 : int) : (term247 _70606) = (term264 _70606).
Proof. exact (MK_COMB (@lem5488607) (@lem5488608 _70606)). Qed.
Lemma lem5488610 (_70606 : int) : (term835 _70606) = (term264 _70606).
Proof. exact (TRANS (@lem5488507 _70606) (@lem5488609 _70606)). Qed.
Lemma lem5488611 (_70606 : int) : (term264 _70606) = term129.
Proof. exact (@lem1982719 (real_of_int _70606)). Qed.
Lemma lem5488612 (_70606 : int) : (term835 _70606) = term129.
Proof. exact (TRANS (@lem5488610 _70606) (@lem5488611 _70606)). Qed.
Lemma lem5488613 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488614 (_70606 : int) : (term836 _70606) = term266.
Proof. exact (MK_COMB (@lem5488613) (@lem5488612 _70606)). Qed.
Lemma lem5488615 (_70608 : int) : (term854 _70608) = (term281 _70608).
Proof. exact (@lem1982763 (term239 _70608) (real_of_int _70608) term164). Qed.
Lemma lem5488616 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5488618 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488619 : term143 = term191.
Proof. exact (@lem5488618 term144). Qed.
Lemma lem5488621 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488622 : term164 = term165.
Proof. exact (@lem5488621 term144). Qed.
Lemma lem5488623 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488624 : term248 = term249.
Proof. exact (MK_COMB (@lem5488623) (@lem5488622)). Qed.
Lemma lem5488625 : term250 = term251.
Proof. exact (MK_COMB (@lem5488624) (@lem5488619)). Qed.
Lemma lem5488626 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5488628 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488629 : term211 = term217.
Proof. exact (@lem5488628 (NUMERAL 0) term144). Qed.
Lemma lem5488630 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488631 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488632 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488631 h1) (fun h1 : term217 = True => @lem5488630)). Qed.
Lemma lem5488633 : term217 = True.
Proof. exact (EQ_MP (@lem5488632) (@lem5488630)). Qed.
Lemma lem5488634 : term211 = True.
Proof. exact (TRANS (@lem5488629) (@lem5488633)). Qed.
Lemma lem5488635 : True = term211.
Proof. exact (SYM (@lem5488634)). Qed.
Lemma lem5488636 : term211.
Proof. exact (EQ_MP (@lem5488635) (@lem0)). Qed.
Lemma lem5488637 : term253.
Proof. exact (@lem5488626 (@lem5488636)). Qed.
Lemma lem5488639 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488640 : term211 = term217.
Proof. exact (@lem5488639 (NUMERAL 0) term144). Qed.
Lemma lem5488641 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488642 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488643 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488642 h1) (fun h1 : term217 = True => @lem5488641)). Qed.
Lemma lem5488644 : term217 = True.
Proof. exact (EQ_MP (@lem5488643) (@lem5488641)). Qed.
Lemma lem5488645 : term211 = True.
Proof. exact (TRANS (@lem5488640) (@lem5488644)). Qed.
Lemma lem5488646 : True = term211.
Proof. exact (SYM (@lem5488645)). Qed.
Lemma lem5488647 : term211.
Proof. exact (EQ_MP (@lem5488646) (@lem0)). Qed.
Lemma lem5488648 : term254.
Proof. exact (@lem5488637 (@lem5488647)). Qed.
Lemma lem5488650 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488651 : term211 = term217.
Proof. exact (@lem5488650 (NUMERAL 0) term144). Qed.
Lemma lem5488652 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488653 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488654 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488653 h1) (fun h1 : term217 = True => @lem5488652)). Qed.
Lemma lem5488655 : term217 = True.
Proof. exact (EQ_MP (@lem5488654) (@lem5488652)). Qed.
Lemma lem5488656 : term211 = True.
Proof. exact (TRANS (@lem5488651) (@lem5488655)). Qed.
Lemma lem5488657 : True = term211.
Proof. exact (SYM (@lem5488656)). Qed.
Lemma lem5488658 : term211.
Proof. exact (EQ_MP (@lem5488657) (@lem0)). Qed.
Lemma lem5488659 : term255.
Proof. exact (@lem5488648 (@lem5488658)). Qed.
Lemma lem5488661 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488662 : term173 = term174.
Proof. exact (@lem5488661 term144 term144). Qed.
Lemma lem5488663 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488664 : term176 = term144.
Proof. exact (EQ_MP (@lem5488663) (@lem940073)). Qed.
Lemma lem5488665 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488666 : term174 = term143.
Proof. exact (MK_COMB (@lem5488665) (@lem5488664)). Qed.
Lemma lem5488667 : term173 = term143.
Proof. exact (TRANS (@lem5488662) (@lem5488666)). Qed.
Lemma lem5488669 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5488670 : term192 = term197.
Proof. exact (@lem5488669 term144 term144). Qed.
Lemma lem5488671 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488672 : term176 = term144.
Proof. exact (EQ_MP (@lem5488671) (@lem940073)). Qed.
Lemma lem5488673 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488674 : term174 = term143.
Proof. exact (MK_COMB (@lem5488673) (@lem5488672)). Qed.
Lemma lem5488675 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5488676 : term197 = term164.
Proof. exact (MK_COMB (@lem5488675) (@lem5488674)). Qed.
Lemma lem5488677 : term192 = term164.
Proof. exact (TRANS (@lem5488670) (@lem5488676)). Qed.
Lemma lem5488678 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488679 : term256 = term248.
Proof. exact (MK_COMB (@lem5488678) (@lem5488677)). Qed.
Lemma lem5488680 : term257 = term250.
Proof. exact (MK_COMB (@lem5488679) (@lem5488667)). Qed.
Lemma lem5488682 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5488683 : term250 = term129.
Proof. exact (@lem5488682 term144). Qed.
Lemma lem5488684 : term257 = term129.
Proof. exact (TRANS (@lem5488680) (@lem5488683)). Qed.
Lemma lem5488685 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488686 : term259 = term260.
Proof. exact (MK_COMB (@lem5488685) (@lem5488684)). Qed.
Lemma lem5488687 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5488688 : term261 = term222.
Proof. exact (MK_COMB (@lem5488686) (@lem5488687)). Qed.
Lemma lem5488690 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488691 : term222 = term129.
Proof. exact (@lem5488690 term144). Qed.
Lemma lem5488692 : term261 = term129.
Proof. exact (TRANS (@lem5488688) (@lem5488691)). Qed.
Lemma lem5488694 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488695 : term173 = term174.
Proof. exact (@lem5488694 term144 term144). Qed.
Lemma lem5488696 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488697 : term176 = term144.
Proof. exact (EQ_MP (@lem5488696) (@lem940073)). Qed.
Lemma lem5488698 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488699 : term174 = term143.
Proof. exact (MK_COMB (@lem5488698) (@lem5488697)). Qed.
Lemma lem5488700 : term173 = term143.
Proof. exact (TRANS (@lem5488695) (@lem5488699)). Qed.
Lemma lem5488701 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5488702 : term262 = term222.
Proof. exact (MK_COMB (@lem5488701) (@lem5488700)). Qed.
Lemma lem5488704 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488705 : term222 = term129.
Proof. exact (@lem5488704 term144). Qed.
Lemma lem5488706 : term262 = term129.
Proof. exact (TRANS (@lem5488702) (@lem5488705)). Qed.
Lemma lem5488707 : term129 = term262.
Proof. exact (SYM (@lem5488706)). Qed.
Lemma lem5488708 : term261 = term262.
Proof. exact (TRANS (@lem5488692) (@lem5488707)). Qed.
Lemma lem5488709 : term251 = term161.
Proof. exact (@lem5488659 (@lem5488708)). Qed.
Lemma lem5488710 : term250 = term161.
Proof. exact (TRANS (@lem5488625) (@lem5488709)). Qed.
Lemma lem5488712 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5488713 : term161 = term129.
Proof. exact (@lem5488712 term129). Qed.
Lemma lem5488714 : term250 = term129.
Proof. exact (TRANS (@lem5488710) (@lem5488713)). Qed.
Lemma lem5488715 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488716 : term263 = term260.
Proof. exact (MK_COMB (@lem5488715) (@lem5488714)). Qed.
Lemma lem5488717 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5488718 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5488716) (@lem5488717 _70608)). Qed.
Lemma lem5488719 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5488616 _70608) (@lem5488718 _70608)). Qed.
Lemma lem5488720 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5488721 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5488719 _70608) (@lem5488720 _70608)). Qed.
Lemma lem5488722 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488723 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5488722) (@lem5488721 _70608)). Qed.
Lemma lem5488724 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem5488725 (_70608 : int) : (term281 _70608) = term282.
Proof. exact (MK_COMB (@lem5488723 _70608) (@lem5488724)). Qed.
Lemma lem5488726 (_70608 : int) : (term854 _70608) = term282.
Proof. exact (TRANS (@lem5488615 _70608) (@lem5488725 _70608)). Qed.
Lemma lem5488727 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5488728 (_70608 : int) : (term854 _70608) = term164.
Proof. exact (TRANS (@lem5488726 _70608) (@lem5488727)). Qed.
Lemma lem5488729 (_70606 : int) (_70608 : int) : (term853 _70606 _70608) = term282.
Proof. exact (MK_COMB (@lem5488614 _70606) (@lem5488728 _70608)). Qed.
Lemma lem5488730 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term282.
Proof. exact (TRANS (@lem5488506 _70606 _70608) (@lem5488729 _70606 _70608)). Qed.
Lemma lem5488731 : term282 = term164.
Proof. exact (@lem1982721 term164). Qed.
Lemma lem5488732 (_70606 : int) (_70608 : int) : (term852 _70606 _70608) = term164.
Proof. exact (TRANS (@lem5488730 _70606 _70608) (@lem5488731)). Qed.
Lemma lem5488733 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5488734 (_70606 : int) (_70608 : int) : (term855 _70606 _70608) = term284.
Proof. exact (MK_COMB (@lem5488733) (@lem5488732 _70606 _70608)). Qed.
Lemma lem5488735 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488736 (_70606 : int) (_70608 : int) : (term851 _70606 _70608) = term285.
Proof. exact (MK_COMB (@lem5488734 _70606 _70608) (@lem5488735)). Qed.
Lemma lem5488737 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : term285.
Proof. exact (EQ_MP (@lem5488736 _70606 _70608) (@lem5488505 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488739 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5488740 : term285 = term286.
Proof. exact (@lem5488739 term129 term164). Qed.
Lemma lem5488742 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488743 : term164 = term165.
Proof. exact (@lem5488742 term144). Qed.
Lemma lem5488745 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488746 : term129 = term161.
Proof. exact (@lem5488745 (NUMERAL 0)). Qed.
Lemma lem5488747 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5488748 : term131 = term287.
Proof. exact (MK_COMB (@lem5488747) (@lem5488746)). Qed.
Lemma lem5488749 : term286 = term288.
Proof. exact (MK_COMB (@lem5488748) (@lem5488743)). Qed.
Lemma lem5488750 : term289.
Proof. exact (@lem1980026 term129 term143 term164 term143). Qed.
Lemma lem5488752 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488753 : term211 = term217.
Proof. exact (@lem5488752 (NUMERAL 0) term144). Qed.
Lemma lem5488754 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488755 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488756 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488755 h1) (fun h1 : term217 = True => @lem5488754)). Qed.
Lemma lem5488757 : term217 = True.
Proof. exact (EQ_MP (@lem5488756) (@lem5488754)). Qed.
Lemma lem5488758 : term211 = True.
Proof. exact (TRANS (@lem5488753) (@lem5488757)). Qed.
Lemma lem5488759 : True = term211.
Proof. exact (SYM (@lem5488758)). Qed.
Lemma lem5488760 : term211.
Proof. exact (EQ_MP (@lem5488759) (@lem0)). Qed.
Lemma lem5488761 : term290.
Proof. exact (@lem5488750 (@lem5488760)). Qed.
Lemma lem5488763 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488764 : term211 = term217.
Proof. exact (@lem5488763 (NUMERAL 0) term144). Qed.
Lemma lem5488765 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488766 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488767 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488766 h1) (fun h1 : term217 = True => @lem5488765)). Qed.
Lemma lem5488768 : term217 = True.
Proof. exact (EQ_MP (@lem5488767) (@lem5488765)). Qed.
Lemma lem5488769 : term211 = True.
Proof. exact (TRANS (@lem5488764) (@lem5488768)). Qed.
Lemma lem5488770 : True = term211.
Proof. exact (SYM (@lem5488769)). Qed.
Lemma lem5488771 : term211.
Proof. exact (EQ_MP (@lem5488770) (@lem0)). Qed.
Lemma lem5488772 : term288 = term291.
Proof. exact (@lem5488761 (@lem5488771)). Qed.
Lemma lem5488774 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5488775 : term192 = term197.
Proof. exact (@lem5488774 term144 term144). Qed.
Lemma lem5488776 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488777 : term176 = term144.
Proof. exact (EQ_MP (@lem5488776) (@lem940073)). Qed.
Lemma lem5488778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488779 : term174 = term143.
Proof. exact (MK_COMB (@lem5488778) (@lem5488777)). Qed.
Lemma lem5488780 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5488781 : term197 = term164.
Proof. exact (MK_COMB (@lem5488780) (@lem5488779)). Qed.
Lemma lem5488782 : term192 = term164.
Proof. exact (TRANS (@lem5488775) (@lem5488781)). Qed.
Lemma lem5488784 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488785 : term222 = term129.
Proof. exact (@lem5488784 term144). Qed.
Lemma lem5488786 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5488787 : term292 = term131.
Proof. exact (MK_COMB (@lem5488786) (@lem5488785)). Qed.
Lemma lem5488788 : term291 = term286.
Proof. exact (MK_COMB (@lem5488787) (@lem5488782)). Qed.
Lemma lem5488790 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5488791 : term286 = term295.
Proof. exact (@lem5488790 (NUMERAL 0) term144). Qed.
Lemma lem5488792 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488793 (h1 : term218 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5488794 : (term218 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488793 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5488792)). Qed.
Lemma lem5488795 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5488794) (@lem5488792)). Qed.
Lemma lem5488796 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5488797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5488798 : term296 = (and True).
Proof. exact (MK_COMB (@lem5488797) (@lem5488796)). Qed.
Lemma lem5488799 : term295 = (True /\ False).
Proof. exact (MK_COMB (@lem5488798) (@lem5488795)). Qed.
Lemma lem5488801 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5488802 : term295 = False.
Proof. exact (TRANS (@lem5488799) (@lem5488801)). Qed.
Lemma lem5488803 : term286 = False.
Proof. exact (TRANS (@lem5488791) (@lem5488802)). Qed.
Lemma lem5488804 : term291 = False.
Proof. exact (TRANS (@lem5488788) (@lem5488803)). Qed.
Lemma lem5488805 : term288 = False.
Proof. exact (TRANS (@lem5488772) (@lem5488804)). Qed.
Lemma lem5488806 : term286 = False.
Proof. exact (TRANS (@lem5488749) (@lem5488805)). Qed.
Lemma lem5488807 : term285 = False.
Proof. exact (TRANS (@lem5488740) (@lem5488806)). Qed.
Lemma lem5488808 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term919 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5488807) (@lem5488737 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488809 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term779 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5487058 _70607 _70606 _70608 h1) (fun h0 : term890 _70607 _70606 _70608 => @lem5487933 _70607 _70606 _70608 h0) (fun h0 : term919 _70607 _70606 _70608 => @lem5488808 _70607 _70606 _70608 h0)). Qed.
Lemma lem5488810 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term775 _70607 _70606 _70608) : term775 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5488811 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term920 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5488812 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term776 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5488811 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488814 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term727 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5488812 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488816 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term678 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5488814 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488818 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term634 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5488816 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488820 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term614 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5488818 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488821 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term578 _70607 _70606.
Proof. exact (proj1 (@lem5488818 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488822 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : (real_of_int _70606) = term129.
Proof. exact (proj2 (@lem5488821 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488823 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term576 _70607.
Proof. exact (proj1 (@lem5488821 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488824 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (proj2 (@lem5488820 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488825 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (proj1 (@lem5488820 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488827 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5488828 : term210 = term211.
Proof. exact (@lem5488827 term129 term143). Qed.
Lemma lem5488830 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488831 : term143 = term191.
Proof. exact (@lem5488830 term144). Qed.
Lemma lem5488833 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488834 : term129 = term161.
Proof. exact (@lem5488833 (NUMERAL 0)). Qed.
Lemma lem5488835 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5488836 : term212 = term213.
Proof. exact (MK_COMB (@lem5488835) (@lem5488834)). Qed.
Lemma lem5488837 : term211 = term214.
Proof. exact (MK_COMB (@lem5488836) (@lem5488831)). Qed.
Lemma lem5488838 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5488840 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488841 : term211 = term217.
Proof. exact (@lem5488840 (NUMERAL 0) term144). Qed.
Lemma lem5488842 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488843 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488844 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488843 h1) (fun h1 : term217 = True => @lem5488842)). Qed.
Lemma lem5488845 : term217 = True.
Proof. exact (EQ_MP (@lem5488844) (@lem5488842)). Qed.
Lemma lem5488846 : term211 = True.
Proof. exact (TRANS (@lem5488841) (@lem5488845)). Qed.
Lemma lem5488847 : True = term211.
Proof. exact (SYM (@lem5488846)). Qed.
Lemma lem5488848 : term211.
Proof. exact (EQ_MP (@lem5488847) (@lem0)). Qed.
Lemma lem5488849 : term219.
Proof. exact (@lem5488838 (@lem5488848)). Qed.
Lemma lem5488851 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488852 : term211 = term217.
Proof. exact (@lem5488851 (NUMERAL 0) term144). Qed.
Lemma lem5488853 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488854 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488855 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488854 h1) (fun h1 : term217 = True => @lem5488853)). Qed.
Lemma lem5488856 : term217 = True.
Proof. exact (EQ_MP (@lem5488855) (@lem5488853)). Qed.
Lemma lem5488857 : term211 = True.
Proof. exact (TRANS (@lem5488852) (@lem5488856)). Qed.
Lemma lem5488858 : True = term211.
Proof. exact (SYM (@lem5488857)). Qed.
Lemma lem5488859 : term211.
Proof. exact (EQ_MP (@lem5488858) (@lem0)). Qed.
Lemma lem5488860 : term214 = term220.
Proof. exact (@lem5488849 (@lem5488859)). Qed.
Lemma lem5488862 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488863 : term173 = term174.
Proof. exact (@lem5488862 term144 term144). Qed.
Lemma lem5488864 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488865 : term176 = term144.
Proof. exact (EQ_MP (@lem5488864) (@lem940073)). Qed.
Lemma lem5488866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488867 : term174 = term143.
Proof. exact (MK_COMB (@lem5488866) (@lem5488865)). Qed.
Lemma lem5488868 : term173 = term143.
Proof. exact (TRANS (@lem5488863) (@lem5488867)). Qed.
Lemma lem5488870 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488871 : term222 = term129.
Proof. exact (@lem5488870 term144). Qed.
Lemma lem5488872 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5488873 : term223 = term212.
Proof. exact (MK_COMB (@lem5488872) (@lem5488871)). Qed.
Lemma lem5488874 : term220 = term211.
Proof. exact (MK_COMB (@lem5488873) (@lem5488868)). Qed.
Lemma lem5488876 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488877 : term211 = term217.
Proof. exact (@lem5488876 (NUMERAL 0) term144). Qed.
Lemma lem5488878 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488879 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488880 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488879 h1) (fun h1 : term217 = True => @lem5488878)). Qed.
Lemma lem5488881 : term217 = True.
Proof. exact (EQ_MP (@lem5488880) (@lem5488878)). Qed.
Lemma lem5488882 : term211 = True.
Proof. exact (TRANS (@lem5488877) (@lem5488881)). Qed.
Lemma lem5488883 : term220 = True.
Proof. exact (TRANS (@lem5488874) (@lem5488882)). Qed.
Lemma lem5488884 : term214 = True.
Proof. exact (TRANS (@lem5488860) (@lem5488883)). Qed.
Lemma lem5488885 : term211 = True.
Proof. exact (TRANS (@lem5488837) (@lem5488884)). Qed.
Lemma lem5488886 : term210 = True.
Proof. exact (TRANS (@lem5488828) (@lem5488885)). Qed.
Lemma lem5488887 : True = term210.
Proof. exact (SYM (@lem5488886)). Qed.
Lemma lem5488888 : term210.
Proof. exact (EQ_MP (@lem5488887) (@lem0)). Qed.
Lemma lem5488889 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term840 _70606 _70608.
Proof. exact (conj (@lem5488888) (@lem5488824 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488891 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5488892 (_70606 : int) (_70608 : int) : term841 _70606 _70608.
Proof. exact (@lem5488891 term143 (term552 _70606 _70608)). Qed.
Lemma lem5488893 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term842 _70606 _70608.
Proof. exact (@lem5488892 _70606 _70608 (@lem5488889 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488894 (_70606 : int) (_70608 : int) : (term826 _70606 _70608) = (term552 _70606 _70608).
Proof. exact (@lem1982733 (term552 _70606 _70608)). Qed.
Lemma lem5488895 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5488896 (_70606 : int) (_70608 : int) : (term843 _70606 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5488895) (@lem5488894 _70606 _70608)). Qed.
Lemma lem5488897 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488898 (_70606 : int) (_70608 : int) : (term842 _70606 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5488896 _70606 _70608) (@lem5488897)). Qed.
Lemma lem5488899 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5488898 _70606 _70608) (@lem5488893 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488901 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5488902 (_70606 : int) : term236 _70606.
Proof. exact (@lem5488901 (real_of_int _70606)). Qed.
Lemma lem5488903 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term237 _70606.
Proof. exact (@lem5488902 _70606 (@lem5488822 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488904 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term921 _70606.
Proof. exact (@lem5488903 _70607 _70606 _70608 h1 term143). Qed.
Lemma lem5488905 (_70606 : int) : (term921 _70606) = ((term228 _70606) = term129).
Proof. exact (eq_refl (term921 _70606)). Qed.
Lemma lem5488906 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : (term228 _70606) = term129.
Proof. exact (EQ_MP (@lem5488905 _70606) (@lem5488904 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488907 (_70606 : int) : (term228 _70606) = (real_of_int _70606).
Proof. exact (@lem1982733 (real_of_int _70606)). Qed.
Lemma lem5488908 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5488909 (_70606 : int) : (term922 _70606) = (term133 _70606).
Proof. exact (MK_COMB (@lem5488908) (@lem5488907 _70606)). Qed.
Lemma lem5488910 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5488911 (_70606 : int) : ((term228 _70606) = term129) = ((real_of_int _70606) = term129).
Proof. exact (MK_COMB (@lem5488909 _70606) (@lem5488910)). Qed.
Lemma lem5488912 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : (real_of_int _70606) = term129.
Proof. exact (EQ_MP (@lem5488911 _70606) (@lem5488906 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488913 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term923 _70606 _70608.
Proof. exact (conj (@lem5488912 _70607 _70606 _70608 h1) (@lem5488899 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488915 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5488916 (_70606 : int) (_70608 : int) : term924 _70606 _70608.
Proof. exact (@lem5488915 (real_of_int _70606) (term552 _70606 _70608)). Qed.
Lemma lem5488917 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term925 _70606 _70608.
Proof. exact (@lem5488916 _70606 _70608 (@lem5488913 _70607 _70606 _70608 h1)). Qed.
Lemma lem5488918 (_70606 : int) (_70608 : int) : (term926 _70606 _70608) = (term927 _70606 _70608).
Proof. exact (@lem1982763 (real_of_int _70606) (term239 _70606) (term546 _70608)). Qed.
Lemma lem5488919 (_70606 : int) : (term835 _70606) = (term247 _70606).
Proof. exact (@lem1982715 term164 (real_of_int _70606)). Qed.
Lemma lem5488921 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5488922 : term143 = term191.
Proof. exact (@lem5488921 term144). Qed.
Lemma lem5488924 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5488925 : term164 = term165.
Proof. exact (@lem5488924 term144). Qed.
Lemma lem5488926 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488927 : term248 = term249.
Proof. exact (MK_COMB (@lem5488926) (@lem5488925)). Qed.
Lemma lem5488928 : term250 = term251.
Proof. exact (MK_COMB (@lem5488927) (@lem5488922)). Qed.
Lemma lem5488929 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5488931 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488932 : term211 = term217.
Proof. exact (@lem5488931 (NUMERAL 0) term144). Qed.
Lemma lem5488933 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488934 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488935 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488934 h1) (fun h1 : term217 = True => @lem5488933)). Qed.
Lemma lem5488936 : term217 = True.
Proof. exact (EQ_MP (@lem5488935) (@lem5488933)). Qed.
Lemma lem5488937 : term211 = True.
Proof. exact (TRANS (@lem5488932) (@lem5488936)). Qed.
Lemma lem5488938 : True = term211.
Proof. exact (SYM (@lem5488937)). Qed.
Lemma lem5488939 : term211.
Proof. exact (EQ_MP (@lem5488938) (@lem0)). Qed.
Lemma lem5488940 : term253.
Proof. exact (@lem5488929 (@lem5488939)). Qed.
Lemma lem5488942 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488943 : term211 = term217.
Proof. exact (@lem5488942 (NUMERAL 0) term144). Qed.
Lemma lem5488944 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488945 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488946 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488945 h1) (fun h1 : term217 = True => @lem5488944)). Qed.
Lemma lem5488947 : term217 = True.
Proof. exact (EQ_MP (@lem5488946) (@lem5488944)). Qed.
Lemma lem5488948 : term211 = True.
Proof. exact (TRANS (@lem5488943) (@lem5488947)). Qed.
Lemma lem5488949 : True = term211.
Proof. exact (SYM (@lem5488948)). Qed.
Lemma lem5488950 : term211.
Proof. exact (EQ_MP (@lem5488949) (@lem0)). Qed.
Lemma lem5488951 : term254.
Proof. exact (@lem5488940 (@lem5488950)). Qed.
Lemma lem5488953 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5488954 : term211 = term217.
Proof. exact (@lem5488953 (NUMERAL 0) term144). Qed.
Lemma lem5488955 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5488956 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5488957 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5488956 h1) (fun h1 : term217 = True => @lem5488955)). Qed.
Lemma lem5488958 : term217 = True.
Proof. exact (EQ_MP (@lem5488957) (@lem5488955)). Qed.
Lemma lem5488959 : term211 = True.
Proof. exact (TRANS (@lem5488954) (@lem5488958)). Qed.
Lemma lem5488960 : True = term211.
Proof. exact (SYM (@lem5488959)). Qed.
Lemma lem5488961 : term211.
Proof. exact (EQ_MP (@lem5488960) (@lem0)). Qed.
Lemma lem5488962 : term255.
Proof. exact (@lem5488951 (@lem5488961)). Qed.
Lemma lem5488964 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488965 : term173 = term174.
Proof. exact (@lem5488964 term144 term144). Qed.
Lemma lem5488966 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488967 : term176 = term144.
Proof. exact (EQ_MP (@lem5488966) (@lem940073)). Qed.
Lemma lem5488968 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488969 : term174 = term143.
Proof. exact (MK_COMB (@lem5488968) (@lem5488967)). Qed.
Lemma lem5488970 : term173 = term143.
Proof. exact (TRANS (@lem5488965) (@lem5488969)). Qed.
Lemma lem5488972 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5488973 : term192 = term197.
Proof. exact (@lem5488972 term144 term144). Qed.
Lemma lem5488974 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5488975 : term176 = term144.
Proof. exact (EQ_MP (@lem5488974) (@lem940073)). Qed.
Lemma lem5488976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5488977 : term174 = term143.
Proof. exact (MK_COMB (@lem5488976) (@lem5488975)). Qed.
Lemma lem5488978 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5488979 : term197 = term164.
Proof. exact (MK_COMB (@lem5488978) (@lem5488977)). Qed.
Lemma lem5488980 : term192 = term164.
Proof. exact (TRANS (@lem5488973) (@lem5488979)). Qed.
Lemma lem5488981 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5488982 : term256 = term248.
Proof. exact (MK_COMB (@lem5488981) (@lem5488980)). Qed.
Lemma lem5488983 : term257 = term250.
Proof. exact (MK_COMB (@lem5488982) (@lem5488970)). Qed.
Lemma lem5488985 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5488986 : term250 = term129.
Proof. exact (@lem5488985 term144). Qed.
Lemma lem5488987 : term257 = term129.
Proof. exact (TRANS (@lem5488983) (@lem5488986)). Qed.
Lemma lem5488988 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5488989 : term259 = term260.
Proof. exact (MK_COMB (@lem5488988) (@lem5488987)). Qed.
Lemma lem5488990 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5488991 : term261 = term222.
Proof. exact (MK_COMB (@lem5488989) (@lem5488990)). Qed.
Lemma lem5488993 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5488994 : term222 = term129.
Proof. exact (@lem5488993 term144). Qed.
Lemma lem5488995 : term261 = term129.
Proof. exact (TRANS (@lem5488991) (@lem5488994)). Qed.
Lemma lem5488997 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5488998 : term173 = term174.
Proof. exact (@lem5488997 term144 term144). Qed.
Lemma lem5488999 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489000 : term176 = term144.
Proof. exact (EQ_MP (@lem5488999) (@lem940073)). Qed.
Lemma lem5489001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489002 : term174 = term143.
Proof. exact (MK_COMB (@lem5489001) (@lem5489000)). Qed.
Lemma lem5489003 : term173 = term143.
Proof. exact (TRANS (@lem5488998) (@lem5489002)). Qed.
Lemma lem5489004 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5489005 : term262 = term222.
Proof. exact (MK_COMB (@lem5489004) (@lem5489003)). Qed.
Lemma lem5489007 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489008 : term222 = term129.
Proof. exact (@lem5489007 term144). Qed.
Lemma lem5489009 : term262 = term129.
Proof. exact (TRANS (@lem5489005) (@lem5489008)). Qed.
Lemma lem5489010 : term129 = term262.
Proof. exact (SYM (@lem5489009)). Qed.
Lemma lem5489011 : term261 = term262.
Proof. exact (TRANS (@lem5488995) (@lem5489010)). Qed.
Lemma lem5489012 : term251 = term161.
Proof. exact (@lem5488962 (@lem5489011)). Qed.
Lemma lem5489013 : term250 = term161.
Proof. exact (TRANS (@lem5488928) (@lem5489012)). Qed.
Lemma lem5489015 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5489016 : term161 = term129.
Proof. exact (@lem5489015 term129). Qed.
Lemma lem5489017 : term250 = term129.
Proof. exact (TRANS (@lem5489013) (@lem5489016)). Qed.
Lemma lem5489018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489019 : term263 = term260.
Proof. exact (MK_COMB (@lem5489018) (@lem5489017)). Qed.
Lemma lem5489020 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5489021 (_70606 : int) : (term247 _70606) = (term264 _70606).
Proof. exact (MK_COMB (@lem5489019) (@lem5489020 _70606)). Qed.
Lemma lem5489022 (_70606 : int) : (term835 _70606) = (term264 _70606).
Proof. exact (TRANS (@lem5488919 _70606) (@lem5489021 _70606)). Qed.
Lemma lem5489023 (_70606 : int) : (term264 _70606) = term129.
Proof. exact (@lem1982719 (real_of_int _70606)). Qed.
Lemma lem5489024 (_70606 : int) : (term835 _70606) = term129.
Proof. exact (TRANS (@lem5489022 _70606) (@lem5489023 _70606)). Qed.
Lemma lem5489025 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489026 (_70606 : int) : (term836 _70606) = term266.
Proof. exact (MK_COMB (@lem5489025) (@lem5489024 _70606)). Qed.
Lemma lem5489027 (_70608 : int) : (term546 _70608) = (term546 _70608).
Proof. exact (eq_refl (term546 _70608)). Qed.
Lemma lem5489028 (_70606 : int) (_70608 : int) : (term927 _70606 _70608) = (term838 _70608).
Proof. exact (MK_COMB (@lem5489026 _70606) (@lem5489027 _70608)). Qed.
Lemma lem5489029 (_70606 : int) (_70608 : int) : (term926 _70606 _70608) = (term838 _70608).
Proof. exact (TRANS (@lem5488918 _70606 _70608) (@lem5489028 _70606 _70608)). Qed.
Lemma lem5489030 (_70608 : int) : (term838 _70608) = (term546 _70608).
Proof. exact (@lem1982721 (term546 _70608)). Qed.
Lemma lem5489031 (_70606 : int) (_70608 : int) : (term926 _70606 _70608) = (term546 _70608).
Proof. exact (TRANS (@lem5489029 _70606 _70608) (@lem5489030 _70608)). Qed.
Lemma lem5489032 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489033 (_70606 : int) (_70608 : int) : (term928 _70606 _70608) = (term548 _70608).
Proof. exact (MK_COMB (@lem5489032) (@lem5489031 _70606 _70608)). Qed.
Lemma lem5489034 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489035 (_70606 : int) (_70608 : int) : (term925 _70606 _70608) = (term549 _70608).
Proof. exact (MK_COMB (@lem5489033 _70606 _70608) (@lem5489034)). Qed.
Lemma lem5489036 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term549 _70608.
Proof. exact (EQ_MP (@lem5489035 _70606 _70608) (@lem5488917 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489038 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5489039 : term210 = term211.
Proof. exact (@lem5489038 term129 term143). Qed.
Lemma lem5489041 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489042 : term143 = term191.
Proof. exact (@lem5489041 term144). Qed.
Lemma lem5489044 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489045 : term129 = term161.
Proof. exact (@lem5489044 (NUMERAL 0)). Qed.
Lemma lem5489046 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489047 : term212 = term213.
Proof. exact (MK_COMB (@lem5489046) (@lem5489045)). Qed.
Lemma lem5489048 : term211 = term214.
Proof. exact (MK_COMB (@lem5489047) (@lem5489042)). Qed.
Lemma lem5489049 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5489051 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489052 : term211 = term217.
Proof. exact (@lem5489051 (NUMERAL 0) term144). Qed.
Lemma lem5489053 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489054 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489055 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489054 h1) (fun h1 : term217 = True => @lem5489053)). Qed.
Lemma lem5489056 : term217 = True.
Proof. exact (EQ_MP (@lem5489055) (@lem5489053)). Qed.
Lemma lem5489057 : term211 = True.
Proof. exact (TRANS (@lem5489052) (@lem5489056)). Qed.
Lemma lem5489058 : True = term211.
Proof. exact (SYM (@lem5489057)). Qed.
Lemma lem5489059 : term211.
Proof. exact (EQ_MP (@lem5489058) (@lem0)). Qed.
Lemma lem5489060 : term219.
Proof. exact (@lem5489049 (@lem5489059)). Qed.
Lemma lem5489062 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489063 : term211 = term217.
Proof. exact (@lem5489062 (NUMERAL 0) term144). Qed.
Lemma lem5489064 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489065 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489066 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489065 h1) (fun h1 : term217 = True => @lem5489064)). Qed.
Lemma lem5489067 : term217 = True.
Proof. exact (EQ_MP (@lem5489066) (@lem5489064)). Qed.
Lemma lem5489068 : term211 = True.
Proof. exact (TRANS (@lem5489063) (@lem5489067)). Qed.
Lemma lem5489069 : True = term211.
Proof. exact (SYM (@lem5489068)). Qed.
Lemma lem5489070 : term211.
Proof. exact (EQ_MP (@lem5489069) (@lem0)). Qed.
Lemma lem5489071 : term214 = term220.
Proof. exact (@lem5489060 (@lem5489070)). Qed.
Lemma lem5489073 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489074 : term173 = term174.
Proof. exact (@lem5489073 term144 term144). Qed.
Lemma lem5489075 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489076 : term176 = term144.
Proof. exact (EQ_MP (@lem5489075) (@lem940073)). Qed.
Lemma lem5489077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489078 : term174 = term143.
Proof. exact (MK_COMB (@lem5489077) (@lem5489076)). Qed.
Lemma lem5489079 : term173 = term143.
Proof. exact (TRANS (@lem5489074) (@lem5489078)). Qed.
Lemma lem5489081 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489082 : term222 = term129.
Proof. exact (@lem5489081 term144). Qed.
Lemma lem5489083 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489084 : term223 = term212.
Proof. exact (MK_COMB (@lem5489083) (@lem5489082)). Qed.
Lemma lem5489085 : term220 = term211.
Proof. exact (MK_COMB (@lem5489084) (@lem5489079)). Qed.
Lemma lem5489087 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489088 : term211 = term217.
Proof. exact (@lem5489087 (NUMERAL 0) term144). Qed.
Lemma lem5489089 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489090 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489091 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489090 h1) (fun h1 : term217 = True => @lem5489089)). Qed.
Lemma lem5489092 : term217 = True.
Proof. exact (EQ_MP (@lem5489091) (@lem5489089)). Qed.
Lemma lem5489093 : term211 = True.
Proof. exact (TRANS (@lem5489088) (@lem5489092)). Qed.
Lemma lem5489094 : term220 = True.
Proof. exact (TRANS (@lem5489085) (@lem5489093)). Qed.
Lemma lem5489095 : term214 = True.
Proof. exact (TRANS (@lem5489071) (@lem5489094)). Qed.
Lemma lem5489096 : term211 = True.
Proof. exact (TRANS (@lem5489048) (@lem5489095)). Qed.
Lemma lem5489097 : term210 = True.
Proof. exact (TRANS (@lem5489039) (@lem5489096)). Qed.
Lemma lem5489098 : True = term210.
Proof. exact (SYM (@lem5489097)). Qed.
Lemma lem5489099 : term210.
Proof. exact (EQ_MP (@lem5489098) (@lem0)). Qed.
Lemma lem5489100 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term859 _70608.
Proof. exact (conj (@lem5489099) (@lem5489036 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489102 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5489103 (_70608 : int) : term860 _70608.
Proof. exact (@lem5489102 term143 (term546 _70608)). Qed.
Lemma lem5489104 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term861 _70608.
Proof. exact (@lem5489103 _70608 (@lem5489100 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489105 (_70608 : int) : (term862 _70608) = (term546 _70608).
Proof. exact (@lem1982733 (term546 _70608)). Qed.
Lemma lem5489106 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489107 (_70608 : int) : (term863 _70608) = (term548 _70608).
Proof. exact (MK_COMB (@lem5489106) (@lem5489105 _70608)). Qed.
Lemma lem5489108 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489109 (_70608 : int) : (term861 _70608) = (term549 _70608).
Proof. exact (MK_COMB (@lem5489107 _70608) (@lem5489108)). Qed.
Lemma lem5489110 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term549 _70608.
Proof. exact (EQ_MP (@lem5489109 _70608) (@lem5489104 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489112 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5489113 : term210 = term211.
Proof. exact (@lem5489112 term129 term143). Qed.
Lemma lem5489115 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489116 : term143 = term191.
Proof. exact (@lem5489115 term144). Qed.
Lemma lem5489118 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489119 : term129 = term161.
Proof. exact (@lem5489118 (NUMERAL 0)). Qed.
Lemma lem5489120 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489121 : term212 = term213.
Proof. exact (MK_COMB (@lem5489120) (@lem5489119)). Qed.
Lemma lem5489122 : term211 = term214.
Proof. exact (MK_COMB (@lem5489121) (@lem5489116)). Qed.
Lemma lem5489123 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5489125 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489126 : term211 = term217.
Proof. exact (@lem5489125 (NUMERAL 0) term144). Qed.
Lemma lem5489127 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489128 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489129 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489128 h1) (fun h1 : term217 = True => @lem5489127)). Qed.
Lemma lem5489130 : term217 = True.
Proof. exact (EQ_MP (@lem5489129) (@lem5489127)). Qed.
Lemma lem5489131 : term211 = True.
Proof. exact (TRANS (@lem5489126) (@lem5489130)). Qed.
Lemma lem5489132 : True = term211.
Proof. exact (SYM (@lem5489131)). Qed.
Lemma lem5489133 : term211.
Proof. exact (EQ_MP (@lem5489132) (@lem0)). Qed.
Lemma lem5489134 : term219.
Proof. exact (@lem5489123 (@lem5489133)). Qed.
Lemma lem5489136 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489137 : term211 = term217.
Proof. exact (@lem5489136 (NUMERAL 0) term144). Qed.
Lemma lem5489138 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489139 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489140 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489139 h1) (fun h1 : term217 = True => @lem5489138)). Qed.
Lemma lem5489141 : term217 = True.
Proof. exact (EQ_MP (@lem5489140) (@lem5489138)). Qed.
Lemma lem5489142 : term211 = True.
Proof. exact (TRANS (@lem5489137) (@lem5489141)). Qed.
Lemma lem5489143 : True = term211.
Proof. exact (SYM (@lem5489142)). Qed.
Lemma lem5489144 : term211.
Proof. exact (EQ_MP (@lem5489143) (@lem0)). Qed.
Lemma lem5489145 : term214 = term220.
Proof. exact (@lem5489134 (@lem5489144)). Qed.
Lemma lem5489147 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489148 : term173 = term174.
Proof. exact (@lem5489147 term144 term144). Qed.
Lemma lem5489149 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489150 : term176 = term144.
Proof. exact (EQ_MP (@lem5489149) (@lem940073)). Qed.
Lemma lem5489151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489152 : term174 = term143.
Proof. exact (MK_COMB (@lem5489151) (@lem5489150)). Qed.
Lemma lem5489153 : term173 = term143.
Proof. exact (TRANS (@lem5489148) (@lem5489152)). Qed.
Lemma lem5489155 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489156 : term222 = term129.
Proof. exact (@lem5489155 term144). Qed.
Lemma lem5489157 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489158 : term223 = term212.
Proof. exact (MK_COMB (@lem5489157) (@lem5489156)). Qed.
Lemma lem5489159 : term220 = term211.
Proof. exact (MK_COMB (@lem5489158) (@lem5489153)). Qed.
Lemma lem5489161 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489162 : term211 = term217.
Proof. exact (@lem5489161 (NUMERAL 0) term144). Qed.
Lemma lem5489163 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489164 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489165 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489164 h1) (fun h1 : term217 = True => @lem5489163)). Qed.
Lemma lem5489166 : term217 = True.
Proof. exact (EQ_MP (@lem5489165) (@lem5489163)). Qed.
Lemma lem5489167 : term211 = True.
Proof. exact (TRANS (@lem5489162) (@lem5489166)). Qed.
Lemma lem5489168 : term220 = True.
Proof. exact (TRANS (@lem5489159) (@lem5489167)). Qed.
Lemma lem5489169 : term214 = True.
Proof. exact (TRANS (@lem5489145) (@lem5489168)). Qed.
Lemma lem5489170 : term211 = True.
Proof. exact (TRANS (@lem5489122) (@lem5489169)). Qed.
Lemma lem5489171 : term210 = True.
Proof. exact (TRANS (@lem5489113) (@lem5489170)). Qed.
Lemma lem5489172 : True = term210.
Proof. exact (SYM (@lem5489171)). Qed.
Lemma lem5489173 : term210.
Proof. exact (EQ_MP (@lem5489172) (@lem0)). Qed.
Lemma lem5489174 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term230 _70607 _70608.
Proof. exact (conj (@lem5489173) (@lem5488825 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489176 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5489177 (_70607 : int) (_70608 : int) : term231 _70607 _70608.
Proof. exact (@lem5489176 term143 (term202 _70607 _70608)). Qed.
Lemma lem5489178 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term232 _70607 _70608.
Proof. exact (@lem5489177 _70607 _70608 (@lem5489174 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489179 (_70607 : int) (_70608 : int) : (term233 _70607 _70608) = (term202 _70607 _70608).
Proof. exact (@lem1982733 (term202 _70607 _70608)). Qed.
Lemma lem5489180 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489181 (_70607 : int) (_70608 : int) : (term234 _70607 _70608) = (term204 _70607 _70608).
Proof. exact (MK_COMB (@lem5489180) (@lem5489179 _70607 _70608)). Qed.
Lemma lem5489182 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489183 (_70607 : int) (_70608 : int) : (term232 _70607 _70608) = (term205 _70607 _70608).
Proof. exact (MK_COMB (@lem5489181 _70607 _70608) (@lem5489182)). Qed.
Lemma lem5489184 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (EQ_MP (@lem5489183 _70607 _70608) (@lem5489178 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489185 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term929 _70607 _70608.
Proof. exact (conj (@lem5489184 _70607 _70606 _70608 h1) (@lem5489110 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489187 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5489188 (_70607 : int) (_70608 : int) : term930 _70607 _70608.
Proof. exact (@lem5489187 (term202 _70607 _70608) (term546 _70608)). Qed.
Lemma lem5489189 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term931 _70607 _70608.
Proof. exact (@lem5489188 _70607 _70608 (@lem5489185 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489190 (_70607 : int) (_70608 : int) : (term932 _70607 _70608) = (term933 _70607 _70608).
Proof. exact (@lem1982755 (real_of_int _70607) (term201 _70608) (term546 _70608)). Qed.
Lemma lem5489191 (_70608 : int) : (term934 _70608) = (term935 _70608).
Proof. exact (@lem1982753 (term239 _70608) (real_of_int _70608) term164 term164). Qed.
Lemma lem5489192 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5489194 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489195 : term143 = term191.
Proof. exact (@lem5489194 term144). Qed.
Lemma lem5489197 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5489198 : term164 = term165.
Proof. exact (@lem5489197 term144). Qed.
Lemma lem5489199 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489200 : term248 = term249.
Proof. exact (MK_COMB (@lem5489199) (@lem5489198)). Qed.
Lemma lem5489201 : term250 = term251.
Proof. exact (MK_COMB (@lem5489200) (@lem5489195)). Qed.
Lemma lem5489202 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5489204 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489205 : term211 = term217.
Proof. exact (@lem5489204 (NUMERAL 0) term144). Qed.
Lemma lem5489206 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489207 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489208 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489207 h1) (fun h1 : term217 = True => @lem5489206)). Qed.
Lemma lem5489209 : term217 = True.
Proof. exact (EQ_MP (@lem5489208) (@lem5489206)). Qed.
Lemma lem5489210 : term211 = True.
Proof. exact (TRANS (@lem5489205) (@lem5489209)). Qed.
Lemma lem5489211 : True = term211.
Proof. exact (SYM (@lem5489210)). Qed.
Lemma lem5489212 : term211.
Proof. exact (EQ_MP (@lem5489211) (@lem0)). Qed.
Lemma lem5489213 : term253.
Proof. exact (@lem5489202 (@lem5489212)). Qed.
Lemma lem5489215 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489216 : term211 = term217.
Proof. exact (@lem5489215 (NUMERAL 0) term144). Qed.
Lemma lem5489217 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489218 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489219 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489218 h1) (fun h1 : term217 = True => @lem5489217)). Qed.
Lemma lem5489220 : term217 = True.
Proof. exact (EQ_MP (@lem5489219) (@lem5489217)). Qed.
Lemma lem5489221 : term211 = True.
Proof. exact (TRANS (@lem5489216) (@lem5489220)). Qed.
Lemma lem5489222 : True = term211.
Proof. exact (SYM (@lem5489221)). Qed.
Lemma lem5489223 : term211.
Proof. exact (EQ_MP (@lem5489222) (@lem0)). Qed.
Lemma lem5489224 : term254.
Proof. exact (@lem5489213 (@lem5489223)). Qed.
Lemma lem5489226 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489227 : term211 = term217.
Proof. exact (@lem5489226 (NUMERAL 0) term144). Qed.
Lemma lem5489228 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489229 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489230 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489229 h1) (fun h1 : term217 = True => @lem5489228)). Qed.
Lemma lem5489231 : term217 = True.
Proof. exact (EQ_MP (@lem5489230) (@lem5489228)). Qed.
Lemma lem5489232 : term211 = True.
Proof. exact (TRANS (@lem5489227) (@lem5489231)). Qed.
Lemma lem5489233 : True = term211.
Proof. exact (SYM (@lem5489232)). Qed.
Lemma lem5489234 : term211.
Proof. exact (EQ_MP (@lem5489233) (@lem0)). Qed.
Lemma lem5489235 : term255.
Proof. exact (@lem5489224 (@lem5489234)). Qed.
Lemma lem5489237 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489238 : term173 = term174.
Proof. exact (@lem5489237 term144 term144). Qed.
Lemma lem5489239 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489240 : term176 = term144.
Proof. exact (EQ_MP (@lem5489239) (@lem940073)). Qed.
Lemma lem5489241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489242 : term174 = term143.
Proof. exact (MK_COMB (@lem5489241) (@lem5489240)). Qed.
Lemma lem5489243 : term173 = term143.
Proof. exact (TRANS (@lem5489238) (@lem5489242)). Qed.
Lemma lem5489245 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489246 : term192 = term197.
Proof. exact (@lem5489245 term144 term144). Qed.
Lemma lem5489247 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489248 : term176 = term144.
Proof. exact (EQ_MP (@lem5489247) (@lem940073)). Qed.
Lemma lem5489249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489250 : term174 = term143.
Proof. exact (MK_COMB (@lem5489249) (@lem5489248)). Qed.
Lemma lem5489251 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489252 : term197 = term164.
Proof. exact (MK_COMB (@lem5489251) (@lem5489250)). Qed.
Lemma lem5489253 : term192 = term164.
Proof. exact (TRANS (@lem5489246) (@lem5489252)). Qed.
Lemma lem5489254 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489255 : term256 = term248.
Proof. exact (MK_COMB (@lem5489254) (@lem5489253)). Qed.
Lemma lem5489256 : term257 = term250.
Proof. exact (MK_COMB (@lem5489255) (@lem5489243)). Qed.
Lemma lem5489258 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5489259 : term250 = term129.
Proof. exact (@lem5489258 term144). Qed.
Lemma lem5489260 : term257 = term129.
Proof. exact (TRANS (@lem5489256) (@lem5489259)). Qed.
Lemma lem5489261 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489262 : term259 = term260.
Proof. exact (MK_COMB (@lem5489261) (@lem5489260)). Qed.
Lemma lem5489263 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5489264 : term261 = term222.
Proof. exact (MK_COMB (@lem5489262) (@lem5489263)). Qed.
Lemma lem5489266 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489267 : term222 = term129.
Proof. exact (@lem5489266 term144). Qed.
Lemma lem5489268 : term261 = term129.
Proof. exact (TRANS (@lem5489264) (@lem5489267)). Qed.
Lemma lem5489270 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489271 : term173 = term174.
Proof. exact (@lem5489270 term144 term144). Qed.
Lemma lem5489272 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489273 : term176 = term144.
Proof. exact (EQ_MP (@lem5489272) (@lem940073)). Qed.
Lemma lem5489274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489275 : term174 = term143.
Proof. exact (MK_COMB (@lem5489274) (@lem5489273)). Qed.
Lemma lem5489276 : term173 = term143.
Proof. exact (TRANS (@lem5489271) (@lem5489275)). Qed.
Lemma lem5489277 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5489278 : term262 = term222.
Proof. exact (MK_COMB (@lem5489277) (@lem5489276)). Qed.
Lemma lem5489280 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489281 : term222 = term129.
Proof. exact (@lem5489280 term144). Qed.
Lemma lem5489282 : term262 = term129.
Proof. exact (TRANS (@lem5489278) (@lem5489281)). Qed.
Lemma lem5489283 : term129 = term262.
Proof. exact (SYM (@lem5489282)). Qed.
Lemma lem5489284 : term261 = term262.
Proof. exact (TRANS (@lem5489268) (@lem5489283)). Qed.
Lemma lem5489285 : term251 = term161.
Proof. exact (@lem5489235 (@lem5489284)). Qed.
Lemma lem5489286 : term250 = term161.
Proof. exact (TRANS (@lem5489201) (@lem5489285)). Qed.
Lemma lem5489288 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5489289 : term161 = term129.
Proof. exact (@lem5489288 term129). Qed.
Lemma lem5489290 : term250 = term129.
Proof. exact (TRANS (@lem5489286) (@lem5489289)). Qed.
Lemma lem5489291 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489292 : term263 = term260.
Proof. exact (MK_COMB (@lem5489291) (@lem5489290)). Qed.
Lemma lem5489293 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5489294 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5489292) (@lem5489293 _70608)). Qed.
Lemma lem5489295 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5489192 _70608) (@lem5489294 _70608)). Qed.
Lemma lem5489296 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5489297 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5489295 _70608) (@lem5489296 _70608)). Qed.
Lemma lem5489298 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489299 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5489298) (@lem5489297 _70608)). Qed.
Lemma lem5489301 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5489302 : term164 = term165.
Proof. exact (@lem5489301 term144). Qed.
Lemma lem5489304 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5489305 : term164 = term165.
Proof. exact (@lem5489304 term144). Qed.
Lemma lem5489306 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489307 : term248 = term249.
Proof. exact (MK_COMB (@lem5489306) (@lem5489305)). Qed.
Lemma lem5489308 : term936 = term937.
Proof. exact (MK_COMB (@lem5489307) (@lem5489302)). Qed.
Lemma lem5489309 : term938.
Proof. exact (@lem1981473 term164 term143 term164 term143 term939 term143). Qed.
Lemma lem5489311 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489312 : term211 = term217.
Proof. exact (@lem5489311 (NUMERAL 0) term144). Qed.
Lemma lem5489313 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489314 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489315 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489314 h1) (fun h1 : term217 = True => @lem5489313)). Qed.
Lemma lem5489316 : term217 = True.
Proof. exact (EQ_MP (@lem5489315) (@lem5489313)). Qed.
Lemma lem5489317 : term211 = True.
Proof. exact (TRANS (@lem5489312) (@lem5489316)). Qed.
Lemma lem5489318 : True = term211.
Proof. exact (SYM (@lem5489317)). Qed.
Lemma lem5489319 : term211.
Proof. exact (EQ_MP (@lem5489318) (@lem0)). Qed.
Lemma lem5489320 : term940.
Proof. exact (@lem5489309 (@lem5489319)). Qed.
Lemma lem5489322 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489323 : term211 = term217.
Proof. exact (@lem5489322 (NUMERAL 0) term144). Qed.
Lemma lem5489324 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489325 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489326 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489325 h1) (fun h1 : term217 = True => @lem5489324)). Qed.
Lemma lem5489327 : term217 = True.
Proof. exact (EQ_MP (@lem5489326) (@lem5489324)). Qed.
Lemma lem5489328 : term211 = True.
Proof. exact (TRANS (@lem5489323) (@lem5489327)). Qed.
Lemma lem5489329 : True = term211.
Proof. exact (SYM (@lem5489328)). Qed.
Lemma lem5489330 : term211.
Proof. exact (EQ_MP (@lem5489329) (@lem0)). Qed.
Lemma lem5489331 : term941.
Proof. exact (@lem5489320 (@lem5489330)). Qed.
Lemma lem5489333 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489334 : term211 = term217.
Proof. exact (@lem5489333 (NUMERAL 0) term144). Qed.
Lemma lem5489335 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489336 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489337 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489336 h1) (fun h1 : term217 = True => @lem5489335)). Qed.
Lemma lem5489338 : term217 = True.
Proof. exact (EQ_MP (@lem5489337) (@lem5489335)). Qed.
Lemma lem5489339 : term211 = True.
Proof. exact (TRANS (@lem5489334) (@lem5489338)). Qed.
Lemma lem5489340 : True = term211.
Proof. exact (SYM (@lem5489339)). Qed.
Lemma lem5489341 : term211.
Proof. exact (EQ_MP (@lem5489340) (@lem0)). Qed.
Lemma lem5489342 : term942.
Proof. exact (@lem5489331 (@lem5489341)). Qed.
Lemma lem5489344 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489345 : term192 = term197.
Proof. exact (@lem5489344 term144 term144). Qed.
Lemma lem5489346 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489347 : term176 = term144.
Proof. exact (EQ_MP (@lem5489346) (@lem940073)). Qed.
Lemma lem5489348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489349 : term174 = term143.
Proof. exact (MK_COMB (@lem5489348) (@lem5489347)). Qed.
Lemma lem5489350 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489351 : term197 = term164.
Proof. exact (MK_COMB (@lem5489350) (@lem5489349)). Qed.
Lemma lem5489352 : term192 = term164.
Proof. exact (TRANS (@lem5489345) (@lem5489351)). Qed.
Lemma lem5489354 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489355 : term192 = term197.
Proof. exact (@lem5489354 term144 term144). Qed.
Lemma lem5489356 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489357 : term176 = term144.
Proof. exact (EQ_MP (@lem5489356) (@lem940073)). Qed.
Lemma lem5489358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489359 : term174 = term143.
Proof. exact (MK_COMB (@lem5489358) (@lem5489357)). Qed.
Lemma lem5489360 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489361 : term197 = term164.
Proof. exact (MK_COMB (@lem5489360) (@lem5489359)). Qed.
Lemma lem5489362 : term192 = term164.
Proof. exact (TRANS (@lem5489355) (@lem5489361)). Qed.
Lemma lem5489363 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489364 : term256 = term248.
Proof. exact (MK_COMB (@lem5489363) (@lem5489362)). Qed.
Lemma lem5489365 : term943 = term936.
Proof. exact (MK_COMB (@lem5489364) (@lem5489352)). Qed.
Lemma lem5489366 : term936 = term944.
Proof. exact (@lem1367763 term144 term144). Qed.
Lemma lem5489367 : term945 = term946.
Proof. exact (@lem706885). Qed.
Lemma lem5489368 : (term945 = term946) = (term947 = term948).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term946). Qed.
Lemma lem5489369 : term947 = term948.
Proof. exact (EQ_MP (@lem5489368) (@lem5489367)). Qed.
Lemma lem5489370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489371 : term949 = term950.
Proof. exact (MK_COMB (@lem5489370) (@lem5489369)). Qed.
Lemma lem5489372 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489373 : term944 = term939.
Proof. exact (MK_COMB (@lem5489372) (@lem5489371)). Qed.
Lemma lem5489374 : term936 = term939.
Proof. exact (TRANS (@lem5489366) (@lem5489373)). Qed.
Lemma lem5489375 : term943 = term939.
Proof. exact (TRANS (@lem5489365) (@lem5489374)). Qed.
Lemma lem5489376 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489377 : term951 = term952.
Proof. exact (MK_COMB (@lem5489376) (@lem5489375)). Qed.
Lemma lem5489378 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5489379 : term953 = term954.
Proof. exact (MK_COMB (@lem5489377) (@lem5489378)). Qed.
Lemma lem5489381 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489382 : term954 = term955.
Proof. exact (@lem5489381 term948 term144). Qed.
Lemma lem5489383 : term956 = term946.
Proof. exact (@lem996237 term946). Qed.
Lemma lem5489384 : (term956 = term946) = (term957 = term948).
Proof. exact (@lem1007663 term946 (BIT1 0) term946). Qed.
Lemma lem5489385 : term957 = term948.
Proof. exact (EQ_MP (@lem5489384) (@lem5489383)). Qed.
Lemma lem5489386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489387 : term958 = term950.
Proof. exact (MK_COMB (@lem5489386) (@lem5489385)). Qed.
Lemma lem5489388 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489389 : term955 = term939.
Proof. exact (MK_COMB (@lem5489388) (@lem5489387)). Qed.
Lemma lem5489390 : term954 = term939.
Proof. exact (TRANS (@lem5489382) (@lem5489389)). Qed.
Lemma lem5489391 : term953 = term939.
Proof. exact (TRANS (@lem5489379) (@lem5489390)). Qed.
Lemma lem5489393 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489394 : term173 = term174.
Proof. exact (@lem5489393 term144 term144). Qed.
Lemma lem5489395 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489396 : term176 = term144.
Proof. exact (EQ_MP (@lem5489395) (@lem940073)). Qed.
Lemma lem5489397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489398 : term174 = term143.
Proof. exact (MK_COMB (@lem5489397) (@lem5489396)). Qed.
Lemma lem5489399 : term173 = term143.
Proof. exact (TRANS (@lem5489394) (@lem5489398)). Qed.
Lemma lem5489400 : term952 = term952.
Proof. exact (eq_refl term952). Qed.
Lemma lem5489401 : term959 = term954.
Proof. exact (MK_COMB (@lem5489400) (@lem5489399)). Qed.
Lemma lem5489403 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489404 : term954 = term955.
Proof. exact (@lem5489403 term948 term144). Qed.
Lemma lem5489405 : term956 = term946.
Proof. exact (@lem996237 term946). Qed.
Lemma lem5489406 : (term956 = term946) = (term957 = term948).
Proof. exact (@lem1007663 term946 (BIT1 0) term946). Qed.
Lemma lem5489407 : term957 = term948.
Proof. exact (EQ_MP (@lem5489406) (@lem5489405)). Qed.
Lemma lem5489408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489409 : term958 = term950.
Proof. exact (MK_COMB (@lem5489408) (@lem5489407)). Qed.
Lemma lem5489410 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489411 : term955 = term939.
Proof. exact (MK_COMB (@lem5489410) (@lem5489409)). Qed.
Lemma lem5489412 : term954 = term939.
Proof. exact (TRANS (@lem5489404) (@lem5489411)). Qed.
Lemma lem5489413 : term959 = term939.
Proof. exact (TRANS (@lem5489401) (@lem5489412)). Qed.
Lemma lem5489414 : term939 = term959.
Proof. exact (SYM (@lem5489413)). Qed.
Lemma lem5489415 : term953 = term959.
Proof. exact (TRANS (@lem5489391) (@lem5489414)). Qed.
Lemma lem5489416 : term937 = term960.
Proof. exact (@lem5489342 (@lem5489415)). Qed.
Lemma lem5489417 : term936 = term960.
Proof. exact (TRANS (@lem5489308) (@lem5489416)). Qed.
Lemma lem5489419 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5489420 : term960 = term939.
Proof. exact (@lem5489419 term939). Qed.
Lemma lem5489421 : term936 = term939.
Proof. exact (TRANS (@lem5489417) (@lem5489420)). Qed.
Lemma lem5489422 (_70608 : int) : (term935 _70608) = term961.
Proof. exact (MK_COMB (@lem5489299 _70608) (@lem5489421)). Qed.
Lemma lem5489423 (_70608 : int) : (term934 _70608) = term961.
Proof. exact (TRANS (@lem5489191 _70608) (@lem5489422 _70608)). Qed.
Lemma lem5489424 : term961 = term939.
Proof. exact (@lem1982721 term939). Qed.
Lemma lem5489425 (_70608 : int) : (term934 _70608) = term939.
Proof. exact (TRANS (@lem5489423 _70608) (@lem5489424)). Qed.
Lemma lem5489426 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5489427 (_70608 : int) (_70607 : int) : (term933 _70607 _70608) = (term962 _70607).
Proof. exact (MK_COMB (@lem5489426 _70607) (@lem5489425 _70608)). Qed.
Lemma lem5489428 (_70608 : int) (_70607 : int) : (term932 _70607 _70608) = (term962 _70607).
Proof. exact (TRANS (@lem5489190 _70607 _70608) (@lem5489427 _70608 _70607)). Qed.
Lemma lem5489429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489430 (_70608 : int) (_70607 : int) : (term963 _70607 _70608) = (term964 _70607).
Proof. exact (MK_COMB (@lem5489429) (@lem5489428 _70608 _70607)). Qed.
Lemma lem5489431 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489432 (_70608 : int) (_70607 : int) : (term931 _70607 _70608) = (term965 _70607).
Proof. exact (MK_COMB (@lem5489430 _70608 _70607) (@lem5489431)). Qed.
Lemma lem5489433 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term965 _70607.
Proof. exact (EQ_MP (@lem5489432 _70608 _70607) (@lem5489189 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489435 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5489436 : term210 = term211.
Proof. exact (@lem5489435 term129 term143). Qed.
Lemma lem5489438 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489439 : term143 = term191.
Proof. exact (@lem5489438 term144). Qed.
Lemma lem5489441 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489442 : term129 = term161.
Proof. exact (@lem5489441 (NUMERAL 0)). Qed.
Lemma lem5489443 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489444 : term212 = term213.
Proof. exact (MK_COMB (@lem5489443) (@lem5489442)). Qed.
Lemma lem5489445 : term211 = term214.
Proof. exact (MK_COMB (@lem5489444) (@lem5489439)). Qed.
Lemma lem5489446 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5489448 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489449 : term211 = term217.
Proof. exact (@lem5489448 (NUMERAL 0) term144). Qed.
Lemma lem5489450 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489451 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489452 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489451 h1) (fun h1 : term217 = True => @lem5489450)). Qed.
Lemma lem5489453 : term217 = True.
Proof. exact (EQ_MP (@lem5489452) (@lem5489450)). Qed.
Lemma lem5489454 : term211 = True.
Proof. exact (TRANS (@lem5489449) (@lem5489453)). Qed.
Lemma lem5489455 : True = term211.
Proof. exact (SYM (@lem5489454)). Qed.
Lemma lem5489456 : term211.
Proof. exact (EQ_MP (@lem5489455) (@lem0)). Qed.
Lemma lem5489457 : term219.
Proof. exact (@lem5489446 (@lem5489456)). Qed.
Lemma lem5489459 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489460 : term211 = term217.
Proof. exact (@lem5489459 (NUMERAL 0) term144). Qed.
Lemma lem5489461 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489462 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489463 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489462 h1) (fun h1 : term217 = True => @lem5489461)). Qed.
Lemma lem5489464 : term217 = True.
Proof. exact (EQ_MP (@lem5489463) (@lem5489461)). Qed.
Lemma lem5489465 : term211 = True.
Proof. exact (TRANS (@lem5489460) (@lem5489464)). Qed.
Lemma lem5489466 : True = term211.
Proof. exact (SYM (@lem5489465)). Qed.
Lemma lem5489467 : term211.
Proof. exact (EQ_MP (@lem5489466) (@lem0)). Qed.
Lemma lem5489468 : term214 = term220.
Proof. exact (@lem5489457 (@lem5489467)). Qed.
Lemma lem5489470 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489471 : term173 = term174.
Proof. exact (@lem5489470 term144 term144). Qed.
Lemma lem5489472 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489473 : term176 = term144.
Proof. exact (EQ_MP (@lem5489472) (@lem940073)). Qed.
Lemma lem5489474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489475 : term174 = term143.
Proof. exact (MK_COMB (@lem5489474) (@lem5489473)). Qed.
Lemma lem5489476 : term173 = term143.
Proof. exact (TRANS (@lem5489471) (@lem5489475)). Qed.
Lemma lem5489478 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489479 : term222 = term129.
Proof. exact (@lem5489478 term144). Qed.
Lemma lem5489480 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489481 : term223 = term212.
Proof. exact (MK_COMB (@lem5489480) (@lem5489479)). Qed.
Lemma lem5489482 : term220 = term211.
Proof. exact (MK_COMB (@lem5489481) (@lem5489476)). Qed.
Lemma lem5489484 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489485 : term211 = term217.
Proof. exact (@lem5489484 (NUMERAL 0) term144). Qed.
Lemma lem5489486 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489487 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489488 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489487 h1) (fun h1 : term217 = True => @lem5489486)). Qed.
Lemma lem5489489 : term217 = True.
Proof. exact (EQ_MP (@lem5489488) (@lem5489486)). Qed.
Lemma lem5489490 : term211 = True.
Proof. exact (TRANS (@lem5489485) (@lem5489489)). Qed.
Lemma lem5489491 : term220 = True.
Proof. exact (TRANS (@lem5489482) (@lem5489490)). Qed.
Lemma lem5489492 : term214 = True.
Proof. exact (TRANS (@lem5489468) (@lem5489491)). Qed.
Lemma lem5489493 : term211 = True.
Proof. exact (TRANS (@lem5489445) (@lem5489492)). Qed.
Lemma lem5489494 : term210 = True.
Proof. exact (TRANS (@lem5489436) (@lem5489493)). Qed.
Lemma lem5489495 : True = term210.
Proof. exact (SYM (@lem5489494)). Qed.
Lemma lem5489496 : term210.
Proof. exact (EQ_MP (@lem5489495) (@lem0)). Qed.
Lemma lem5489497 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term966 _70607.
Proof. exact (conj (@lem5489496) (@lem5489433 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489499 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5489500 (_70607 : int) : term967 _70607.
Proof. exact (@lem5489499 term143 (term962 _70607)). Qed.
Lemma lem5489501 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term968 _70607.
Proof. exact (@lem5489500 _70607 (@lem5489497 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489502 (_70607 : int) : (term969 _70607) = (term962 _70607).
Proof. exact (@lem1982733 (term962 _70607)). Qed.
Lemma lem5489503 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489504 (_70607 : int) : (term970 _70607) = (term964 _70607).
Proof. exact (MK_COMB (@lem5489503) (@lem5489502 _70607)). Qed.
Lemma lem5489505 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489506 (_70607 : int) : (term968 _70607) = (term965 _70607).
Proof. exact (MK_COMB (@lem5489504 _70607) (@lem5489505)). Qed.
Lemma lem5489507 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term965 _70607.
Proof. exact (EQ_MP (@lem5489506 _70607) (@lem5489501 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489509 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5489510 : term210 = term211.
Proof. exact (@lem5489509 term129 term143). Qed.
Lemma lem5489512 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489513 : term143 = term191.
Proof. exact (@lem5489512 term144). Qed.
Lemma lem5489515 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489516 : term129 = term161.
Proof. exact (@lem5489515 (NUMERAL 0)). Qed.
Lemma lem5489517 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489518 : term212 = term213.
Proof. exact (MK_COMB (@lem5489517) (@lem5489516)). Qed.
Lemma lem5489519 : term211 = term214.
Proof. exact (MK_COMB (@lem5489518) (@lem5489513)). Qed.
Lemma lem5489520 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5489522 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489523 : term211 = term217.
Proof. exact (@lem5489522 (NUMERAL 0) term144). Qed.
Lemma lem5489524 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489525 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489526 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489525 h1) (fun h1 : term217 = True => @lem5489524)). Qed.
Lemma lem5489527 : term217 = True.
Proof. exact (EQ_MP (@lem5489526) (@lem5489524)). Qed.
Lemma lem5489528 : term211 = True.
Proof. exact (TRANS (@lem5489523) (@lem5489527)). Qed.
Lemma lem5489529 : True = term211.
Proof. exact (SYM (@lem5489528)). Qed.
Lemma lem5489530 : term211.
Proof. exact (EQ_MP (@lem5489529) (@lem0)). Qed.
Lemma lem5489531 : term219.
Proof. exact (@lem5489520 (@lem5489530)). Qed.
Lemma lem5489533 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489534 : term211 = term217.
Proof. exact (@lem5489533 (NUMERAL 0) term144). Qed.
Lemma lem5489535 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489536 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489537 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489536 h1) (fun h1 : term217 = True => @lem5489535)). Qed.
Lemma lem5489538 : term217 = True.
Proof. exact (EQ_MP (@lem5489537) (@lem5489535)). Qed.
Lemma lem5489539 : term211 = True.
Proof. exact (TRANS (@lem5489534) (@lem5489538)). Qed.
Lemma lem5489540 : True = term211.
Proof. exact (SYM (@lem5489539)). Qed.
Lemma lem5489541 : term211.
Proof. exact (EQ_MP (@lem5489540) (@lem0)). Qed.
Lemma lem5489542 : term214 = term220.
Proof. exact (@lem5489531 (@lem5489541)). Qed.
Lemma lem5489544 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489545 : term173 = term174.
Proof. exact (@lem5489544 term144 term144). Qed.
Lemma lem5489546 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489547 : term176 = term144.
Proof. exact (EQ_MP (@lem5489546) (@lem940073)). Qed.
Lemma lem5489548 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489549 : term174 = term143.
Proof. exact (MK_COMB (@lem5489548) (@lem5489547)). Qed.
Lemma lem5489550 : term173 = term143.
Proof. exact (TRANS (@lem5489545) (@lem5489549)). Qed.
Lemma lem5489552 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489553 : term222 = term129.
Proof. exact (@lem5489552 term144). Qed.
Lemma lem5489554 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489555 : term223 = term212.
Proof. exact (MK_COMB (@lem5489554) (@lem5489553)). Qed.
Lemma lem5489556 : term220 = term211.
Proof. exact (MK_COMB (@lem5489555) (@lem5489550)). Qed.
Lemma lem5489558 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489559 : term211 = term217.
Proof. exact (@lem5489558 (NUMERAL 0) term144). Qed.
Lemma lem5489560 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489561 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489562 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489561 h1) (fun h1 : term217 = True => @lem5489560)). Qed.
Lemma lem5489563 : term217 = True.
Proof. exact (EQ_MP (@lem5489562) (@lem5489560)). Qed.
Lemma lem5489564 : term211 = True.
Proof. exact (TRANS (@lem5489559) (@lem5489563)). Qed.
Lemma lem5489565 : term220 = True.
Proof. exact (TRANS (@lem5489556) (@lem5489564)). Qed.
Lemma lem5489566 : term214 = True.
Proof. exact (TRANS (@lem5489542) (@lem5489565)). Qed.
Lemma lem5489567 : term211 = True.
Proof. exact (TRANS (@lem5489519) (@lem5489566)). Qed.
Lemma lem5489568 : term210 = True.
Proof. exact (TRANS (@lem5489510) (@lem5489567)). Qed.
Lemma lem5489569 : True = term210.
Proof. exact (SYM (@lem5489568)). Qed.
Lemma lem5489570 : term210.
Proof. exact (EQ_MP (@lem5489569) (@lem0)). Qed.
Lemma lem5489571 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term871 _70607.
Proof. exact (conj (@lem5489570) (@lem5488823 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489573 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5489574 (_70607 : int) : term872 _70607.
Proof. exact (@lem5489573 term143 (term239 _70607)). Qed.
Lemma lem5489575 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term873 _70607.
Proof. exact (@lem5489574 _70607 (@lem5489571 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489576 (_70607 : int) : (term874 _70607) = (term239 _70607).
Proof. exact (@lem1982733 (term239 _70607)). Qed.
Lemma lem5489577 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489578 (_70607 : int) : (term875 _70607) = (term575 _70607).
Proof. exact (MK_COMB (@lem5489577) (@lem5489576 _70607)). Qed.
Lemma lem5489579 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489580 (_70607 : int) : (term873 _70607) = (term576 _70607).
Proof. exact (MK_COMB (@lem5489578 _70607) (@lem5489579)). Qed.
Lemma lem5489581 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term576 _70607.
Proof. exact (EQ_MP (@lem5489580 _70607) (@lem5489575 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489582 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term971 _70607.
Proof. exact (conj (@lem5489581 _70607 _70606 _70608 h1) (@lem5489507 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489584 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5489585 (_70607 : int) : term972 _70607.
Proof. exact (@lem5489584 (term239 _70607) (term962 _70607)). Qed.
Lemma lem5489586 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term973 _70607.
Proof. exact (@lem5489585 _70607 (@lem5489582 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489587 (_70607 : int) : (term974 _70607) = (term975 _70607).
Proof. exact (@lem1982763 (term239 _70607) (real_of_int _70607) term939). Qed.
Lemma lem5489588 (_70607 : int) : (term246 _70607) = (term247 _70607).
Proof. exact (@lem1982713 term164 (real_of_int _70607)). Qed.
Lemma lem5489590 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489591 : term143 = term191.
Proof. exact (@lem5489590 term144). Qed.
Lemma lem5489593 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5489594 : term164 = term165.
Proof. exact (@lem5489593 term144). Qed.
Lemma lem5489595 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489596 : term248 = term249.
Proof. exact (MK_COMB (@lem5489595) (@lem5489594)). Qed.
Lemma lem5489597 : term250 = term251.
Proof. exact (MK_COMB (@lem5489596) (@lem5489591)). Qed.
Lemma lem5489598 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5489600 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489601 : term211 = term217.
Proof. exact (@lem5489600 (NUMERAL 0) term144). Qed.
Lemma lem5489602 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489603 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489604 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489603 h1) (fun h1 : term217 = True => @lem5489602)). Qed.
Lemma lem5489605 : term217 = True.
Proof. exact (EQ_MP (@lem5489604) (@lem5489602)). Qed.
Lemma lem5489606 : term211 = True.
Proof. exact (TRANS (@lem5489601) (@lem5489605)). Qed.
Lemma lem5489607 : True = term211.
Proof. exact (SYM (@lem5489606)). Qed.
Lemma lem5489608 : term211.
Proof. exact (EQ_MP (@lem5489607) (@lem0)). Qed.
Lemma lem5489609 : term253.
Proof. exact (@lem5489598 (@lem5489608)). Qed.
Lemma lem5489611 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489612 : term211 = term217.
Proof. exact (@lem5489611 (NUMERAL 0) term144). Qed.
Lemma lem5489613 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489614 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489615 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489614 h1) (fun h1 : term217 = True => @lem5489613)). Qed.
Lemma lem5489616 : term217 = True.
Proof. exact (EQ_MP (@lem5489615) (@lem5489613)). Qed.
Lemma lem5489617 : term211 = True.
Proof. exact (TRANS (@lem5489612) (@lem5489616)). Qed.
Lemma lem5489618 : True = term211.
Proof. exact (SYM (@lem5489617)). Qed.
Lemma lem5489619 : term211.
Proof. exact (EQ_MP (@lem5489618) (@lem0)). Qed.
Lemma lem5489620 : term254.
Proof. exact (@lem5489609 (@lem5489619)). Qed.
Lemma lem5489622 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489623 : term211 = term217.
Proof. exact (@lem5489622 (NUMERAL 0) term144). Qed.
Lemma lem5489624 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489625 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489626 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489625 h1) (fun h1 : term217 = True => @lem5489624)). Qed.
Lemma lem5489627 : term217 = True.
Proof. exact (EQ_MP (@lem5489626) (@lem5489624)). Qed.
Lemma lem5489628 : term211 = True.
Proof. exact (TRANS (@lem5489623) (@lem5489627)). Qed.
Lemma lem5489629 : True = term211.
Proof. exact (SYM (@lem5489628)). Qed.
Lemma lem5489630 : term211.
Proof. exact (EQ_MP (@lem5489629) (@lem0)). Qed.
Lemma lem5489631 : term255.
Proof. exact (@lem5489620 (@lem5489630)). Qed.
Lemma lem5489633 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489634 : term173 = term174.
Proof. exact (@lem5489633 term144 term144). Qed.
Lemma lem5489635 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489636 : term176 = term144.
Proof. exact (EQ_MP (@lem5489635) (@lem940073)). Qed.
Lemma lem5489637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489638 : term174 = term143.
Proof. exact (MK_COMB (@lem5489637) (@lem5489636)). Qed.
Lemma lem5489639 : term173 = term143.
Proof. exact (TRANS (@lem5489634) (@lem5489638)). Qed.
Lemma lem5489641 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489642 : term192 = term197.
Proof. exact (@lem5489641 term144 term144). Qed.
Lemma lem5489643 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489644 : term176 = term144.
Proof. exact (EQ_MP (@lem5489643) (@lem940073)). Qed.
Lemma lem5489645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489646 : term174 = term143.
Proof. exact (MK_COMB (@lem5489645) (@lem5489644)). Qed.
Lemma lem5489647 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489648 : term197 = term164.
Proof. exact (MK_COMB (@lem5489647) (@lem5489646)). Qed.
Lemma lem5489649 : term192 = term164.
Proof. exact (TRANS (@lem5489642) (@lem5489648)). Qed.
Lemma lem5489650 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489651 : term256 = term248.
Proof. exact (MK_COMB (@lem5489650) (@lem5489649)). Qed.
Lemma lem5489652 : term257 = term250.
Proof. exact (MK_COMB (@lem5489651) (@lem5489639)). Qed.
Lemma lem5489654 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5489655 : term250 = term129.
Proof. exact (@lem5489654 term144). Qed.
Lemma lem5489656 : term257 = term129.
Proof. exact (TRANS (@lem5489652) (@lem5489655)). Qed.
Lemma lem5489657 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489658 : term259 = term260.
Proof. exact (MK_COMB (@lem5489657) (@lem5489656)). Qed.
Lemma lem5489659 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5489660 : term261 = term222.
Proof. exact (MK_COMB (@lem5489658) (@lem5489659)). Qed.
Lemma lem5489662 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489663 : term222 = term129.
Proof. exact (@lem5489662 term144). Qed.
Lemma lem5489664 : term261 = term129.
Proof. exact (TRANS (@lem5489660) (@lem5489663)). Qed.
Lemma lem5489666 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489667 : term173 = term174.
Proof. exact (@lem5489666 term144 term144). Qed.
Lemma lem5489668 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489669 : term176 = term144.
Proof. exact (EQ_MP (@lem5489668) (@lem940073)). Qed.
Lemma lem5489670 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489671 : term174 = term143.
Proof. exact (MK_COMB (@lem5489670) (@lem5489669)). Qed.
Lemma lem5489672 : term173 = term143.
Proof. exact (TRANS (@lem5489667) (@lem5489671)). Qed.
Lemma lem5489673 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5489674 : term262 = term222.
Proof. exact (MK_COMB (@lem5489673) (@lem5489672)). Qed.
Lemma lem5489676 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489677 : term222 = term129.
Proof. exact (@lem5489676 term144). Qed.
Lemma lem5489678 : term262 = term129.
Proof. exact (TRANS (@lem5489674) (@lem5489677)). Qed.
Lemma lem5489679 : term129 = term262.
Proof. exact (SYM (@lem5489678)). Qed.
Lemma lem5489680 : term261 = term262.
Proof. exact (TRANS (@lem5489664) (@lem5489679)). Qed.
Lemma lem5489681 : term251 = term161.
Proof. exact (@lem5489631 (@lem5489680)). Qed.
Lemma lem5489682 : term250 = term161.
Proof. exact (TRANS (@lem5489597) (@lem5489681)). Qed.
Lemma lem5489684 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5489685 : term161 = term129.
Proof. exact (@lem5489684 term129). Qed.
Lemma lem5489686 : term250 = term129.
Proof. exact (TRANS (@lem5489682) (@lem5489685)). Qed.
Lemma lem5489687 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489688 : term263 = term260.
Proof. exact (MK_COMB (@lem5489687) (@lem5489686)). Qed.
Lemma lem5489689 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5489690 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5489688) (@lem5489689 _70607)). Qed.
Lemma lem5489691 (_70607 : int) : (term246 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5489588 _70607) (@lem5489690 _70607)). Qed.
Lemma lem5489692 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5489693 (_70607 : int) : (term246 _70607) = term129.
Proof. exact (TRANS (@lem5489691 _70607) (@lem5489692 _70607)). Qed.
Lemma lem5489694 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489695 (_70607 : int) : (term265 _70607) = term266.
Proof. exact (MK_COMB (@lem5489694) (@lem5489693 _70607)). Qed.
Lemma lem5489696 : term939 = term939.
Proof. exact (eq_refl term939). Qed.
Lemma lem5489697 (_70607 : int) : (term975 _70607) = term961.
Proof. exact (MK_COMB (@lem5489695 _70607) (@lem5489696)). Qed.
Lemma lem5489698 (_70607 : int) : (term974 _70607) = term961.
Proof. exact (TRANS (@lem5489587 _70607) (@lem5489697 _70607)). Qed.
Lemma lem5489699 : term961 = term939.
Proof. exact (@lem1982721 term939). Qed.
Lemma lem5489700 (_70607 : int) : (term974 _70607) = term939.
Proof. exact (TRANS (@lem5489698 _70607) (@lem5489699)). Qed.
Lemma lem5489701 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489702 (_70607 : int) : (term976 _70607) = term977.
Proof. exact (MK_COMB (@lem5489701) (@lem5489700 _70607)). Qed.
Lemma lem5489703 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489704 (_70607 : int) : (term973 _70607) = term978.
Proof. exact (MK_COMB (@lem5489702 _70607) (@lem5489703)). Qed.
Lemma lem5489705 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : term978.
Proof. exact (EQ_MP (@lem5489704 _70607) (@lem5489586 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489707 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5489708 : term978 = term979.
Proof. exact (@lem5489707 term129 term939). Qed.
Lemma lem5489710 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5489711 : term939 = term960.
Proof. exact (@lem5489710 term948). Qed.
Lemma lem5489713 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489714 : term129 = term161.
Proof. exact (@lem5489713 (NUMERAL 0)). Qed.
Lemma lem5489715 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5489716 : term131 = term287.
Proof. exact (MK_COMB (@lem5489715) (@lem5489714)). Qed.
Lemma lem5489717 : term979 = term980.
Proof. exact (MK_COMB (@lem5489716) (@lem5489711)). Qed.
Lemma lem5489718 : term981.
Proof. exact (@lem1980026 term129 term143 term939 term143). Qed.
Lemma lem5489720 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489721 : term211 = term217.
Proof. exact (@lem5489720 (NUMERAL 0) term144). Qed.
Lemma lem5489722 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489723 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489724 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489723 h1) (fun h1 : term217 = True => @lem5489722)). Qed.
Lemma lem5489725 : term217 = True.
Proof. exact (EQ_MP (@lem5489724) (@lem5489722)). Qed.
Lemma lem5489726 : term211 = True.
Proof. exact (TRANS (@lem5489721) (@lem5489725)). Qed.
Lemma lem5489727 : True = term211.
Proof. exact (SYM (@lem5489726)). Qed.
Lemma lem5489728 : term211.
Proof. exact (EQ_MP (@lem5489727) (@lem0)). Qed.
Lemma lem5489729 : term982.
Proof. exact (@lem5489718 (@lem5489728)). Qed.
Lemma lem5489731 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489732 : term211 = term217.
Proof. exact (@lem5489731 (NUMERAL 0) term144). Qed.
Lemma lem5489733 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489734 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489735 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489734 h1) (fun h1 : term217 = True => @lem5489733)). Qed.
Lemma lem5489736 : term217 = True.
Proof. exact (EQ_MP (@lem5489735) (@lem5489733)). Qed.
Lemma lem5489737 : term211 = True.
Proof. exact (TRANS (@lem5489732) (@lem5489736)). Qed.
Lemma lem5489738 : True = term211.
Proof. exact (SYM (@lem5489737)). Qed.
Lemma lem5489739 : term211.
Proof. exact (EQ_MP (@lem5489738) (@lem0)). Qed.
Lemma lem5489740 : term980 = term983.
Proof. exact (@lem5489729 (@lem5489739)). Qed.
Lemma lem5489742 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489743 : term954 = term955.
Proof. exact (@lem5489742 term948 term144). Qed.
Lemma lem5489744 : term956 = term946.
Proof. exact (@lem996237 term946). Qed.
Lemma lem5489745 : (term956 = term946) = (term957 = term948).
Proof. exact (@lem1007663 term946 (BIT1 0) term946). Qed.
Lemma lem5489746 : term957 = term948.
Proof. exact (EQ_MP (@lem5489745) (@lem5489744)). Qed.
Lemma lem5489747 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489748 : term958 = term950.
Proof. exact (MK_COMB (@lem5489747) (@lem5489746)). Qed.
Lemma lem5489749 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489750 : term955 = term939.
Proof. exact (MK_COMB (@lem5489749) (@lem5489748)). Qed.
Lemma lem5489751 : term954 = term939.
Proof. exact (TRANS (@lem5489743) (@lem5489750)). Qed.
Lemma lem5489753 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489754 : term222 = term129.
Proof. exact (@lem5489753 term144). Qed.
Lemma lem5489755 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5489756 : term292 = term131.
Proof. exact (MK_COMB (@lem5489755) (@lem5489754)). Qed.
Lemma lem5489757 : term983 = term979.
Proof. exact (MK_COMB (@lem5489756) (@lem5489751)). Qed.
Lemma lem5489759 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5489760 : term979 = term984.
Proof. exact (@lem5489759 (NUMERAL 0) term948). Qed.
Lemma lem5489761 : term985 = term946.
Proof. exact (@lem912803). Qed.
Lemma lem5489762 (h1 : term985 = term946) : (term948 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term946 h1). Qed.
Lemma lem5489763 : (term985 = term946) = ((term948 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term985 = term946 => @lem5489762 h1) (fun h1 : (term948 = (NUMERAL 0)) = False => @lem5489761)). Qed.
Lemma lem5489764 : (term948 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5489763) (@lem5489761)). Qed.
Lemma lem5489765 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5489766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5489767 : term296 = (and True).
Proof. exact (MK_COMB (@lem5489766) (@lem5489765)). Qed.
Lemma lem5489768 : term984 = (True /\ False).
Proof. exact (MK_COMB (@lem5489767) (@lem5489764)). Qed.
Lemma lem5489770 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5489771 : term984 = False.
Proof. exact (TRANS (@lem5489768) (@lem5489770)). Qed.
Lemma lem5489772 : term979 = False.
Proof. exact (TRANS (@lem5489760) (@lem5489771)). Qed.
Lemma lem5489773 : term983 = False.
Proof. exact (TRANS (@lem5489757) (@lem5489772)). Qed.
Lemma lem5489774 : term980 = False.
Proof. exact (TRANS (@lem5489740) (@lem5489773)). Qed.
Lemma lem5489775 : term979 = False.
Proof. exact (TRANS (@lem5489717) (@lem5489774)). Qed.
Lemma lem5489776 : term978 = False.
Proof. exact (TRANS (@lem5489708) (@lem5489775)). Qed.
Lemma lem5489777 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term920 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5489776) (@lem5489705 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489778 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term986 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5489779 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term777 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5489778 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489781 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term728 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5489779 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489783 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term679 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5489781 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489785 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term634 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5489783 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489787 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term614 _70607 _70606 _70608.
Proof. exact (proj2 (@lem5489785 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489788 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term578 _70607 _70606.
Proof. exact (proj1 (@lem5489785 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489789 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : (real_of_int _70606) = term129.
Proof. exact (proj2 (@lem5489788 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489790 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term576 _70607.
Proof. exact (proj1 (@lem5489788 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489791 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (proj2 (@lem5489787 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489792 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (proj1 (@lem5489787 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489794 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5489795 : term210 = term211.
Proof. exact (@lem5489794 term129 term143). Qed.
Lemma lem5489797 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489798 : term143 = term191.
Proof. exact (@lem5489797 term144). Qed.
Lemma lem5489800 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489801 : term129 = term161.
Proof. exact (@lem5489800 (NUMERAL 0)). Qed.
Lemma lem5489802 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489803 : term212 = term213.
Proof. exact (MK_COMB (@lem5489802) (@lem5489801)). Qed.
Lemma lem5489804 : term211 = term214.
Proof. exact (MK_COMB (@lem5489803) (@lem5489798)). Qed.
Lemma lem5489805 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5489807 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489808 : term211 = term217.
Proof. exact (@lem5489807 (NUMERAL 0) term144). Qed.
Lemma lem5489809 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489810 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489811 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489810 h1) (fun h1 : term217 = True => @lem5489809)). Qed.
Lemma lem5489812 : term217 = True.
Proof. exact (EQ_MP (@lem5489811) (@lem5489809)). Qed.
Lemma lem5489813 : term211 = True.
Proof. exact (TRANS (@lem5489808) (@lem5489812)). Qed.
Lemma lem5489814 : True = term211.
Proof. exact (SYM (@lem5489813)). Qed.
Lemma lem5489815 : term211.
Proof. exact (EQ_MP (@lem5489814) (@lem0)). Qed.
Lemma lem5489816 : term219.
Proof. exact (@lem5489805 (@lem5489815)). Qed.
Lemma lem5489818 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489819 : term211 = term217.
Proof. exact (@lem5489818 (NUMERAL 0) term144). Qed.
Lemma lem5489820 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489821 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489822 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489821 h1) (fun h1 : term217 = True => @lem5489820)). Qed.
Lemma lem5489823 : term217 = True.
Proof. exact (EQ_MP (@lem5489822) (@lem5489820)). Qed.
Lemma lem5489824 : term211 = True.
Proof. exact (TRANS (@lem5489819) (@lem5489823)). Qed.
Lemma lem5489825 : True = term211.
Proof. exact (SYM (@lem5489824)). Qed.
Lemma lem5489826 : term211.
Proof. exact (EQ_MP (@lem5489825) (@lem0)). Qed.
Lemma lem5489827 : term214 = term220.
Proof. exact (@lem5489816 (@lem5489826)). Qed.
Lemma lem5489829 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489830 : term173 = term174.
Proof. exact (@lem5489829 term144 term144). Qed.
Lemma lem5489831 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489832 : term176 = term144.
Proof. exact (EQ_MP (@lem5489831) (@lem940073)). Qed.
Lemma lem5489833 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489834 : term174 = term143.
Proof. exact (MK_COMB (@lem5489833) (@lem5489832)). Qed.
Lemma lem5489835 : term173 = term143.
Proof. exact (TRANS (@lem5489830) (@lem5489834)). Qed.
Lemma lem5489837 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489838 : term222 = term129.
Proof. exact (@lem5489837 term144). Qed.
Lemma lem5489839 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5489840 : term223 = term212.
Proof. exact (MK_COMB (@lem5489839) (@lem5489838)). Qed.
Lemma lem5489841 : term220 = term211.
Proof. exact (MK_COMB (@lem5489840) (@lem5489835)). Qed.
Lemma lem5489843 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489844 : term211 = term217.
Proof. exact (@lem5489843 (NUMERAL 0) term144). Qed.
Lemma lem5489845 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489846 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489847 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489846 h1) (fun h1 : term217 = True => @lem5489845)). Qed.
Lemma lem5489848 : term217 = True.
Proof. exact (EQ_MP (@lem5489847) (@lem5489845)). Qed.
Lemma lem5489849 : term211 = True.
Proof. exact (TRANS (@lem5489844) (@lem5489848)). Qed.
Lemma lem5489850 : term220 = True.
Proof. exact (TRANS (@lem5489841) (@lem5489849)). Qed.
Lemma lem5489851 : term214 = True.
Proof. exact (TRANS (@lem5489827) (@lem5489850)). Qed.
Lemma lem5489852 : term211 = True.
Proof. exact (TRANS (@lem5489804) (@lem5489851)). Qed.
Lemma lem5489853 : term210 = True.
Proof. exact (TRANS (@lem5489795) (@lem5489852)). Qed.
Lemma lem5489854 : True = term210.
Proof. exact (SYM (@lem5489853)). Qed.
Lemma lem5489855 : term210.
Proof. exact (EQ_MP (@lem5489854) (@lem0)). Qed.
Lemma lem5489856 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term840 _70606 _70608.
Proof. exact (conj (@lem5489855) (@lem5489791 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489858 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5489859 (_70606 : int) (_70608 : int) : term841 _70606 _70608.
Proof. exact (@lem5489858 term143 (term552 _70606 _70608)). Qed.
Lemma lem5489860 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term842 _70606 _70608.
Proof. exact (@lem5489859 _70606 _70608 (@lem5489856 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489861 (_70606 : int) (_70608 : int) : (term826 _70606 _70608) = (term552 _70606 _70608).
Proof. exact (@lem1982733 (term552 _70606 _70608)). Qed.
Lemma lem5489862 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5489863 (_70606 : int) (_70608 : int) : (term843 _70606 _70608) = (term593 _70606 _70608).
Proof. exact (MK_COMB (@lem5489862) (@lem5489861 _70606 _70608)). Qed.
Lemma lem5489864 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489865 (_70606 : int) (_70608 : int) : (term842 _70606 _70608) = (term594 _70606 _70608).
Proof. exact (MK_COMB (@lem5489863 _70606 _70608) (@lem5489864)). Qed.
Lemma lem5489866 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term594 _70606 _70608.
Proof. exact (EQ_MP (@lem5489865 _70606 _70608) (@lem5489860 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489868 (y : real) : term235 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5489869 (_70606 : int) : term236 _70606.
Proof. exact (@lem5489868 (real_of_int _70606)). Qed.
Lemma lem5489870 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term237 _70606.
Proof. exact (@lem5489869 _70606 (@lem5489789 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489871 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term921 _70606.
Proof. exact (@lem5489870 _70607 _70606 _70608 h1 term143). Qed.
Lemma lem5489872 (_70606 : int) : (term921 _70606) = ((term228 _70606) = term129).
Proof. exact (eq_refl (term921 _70606)). Qed.
Lemma lem5489873 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : (term228 _70606) = term129.
Proof. exact (EQ_MP (@lem5489872 _70606) (@lem5489871 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489874 (_70606 : int) : (term228 _70606) = (real_of_int _70606).
Proof. exact (@lem1982733 (real_of_int _70606)). Qed.
Lemma lem5489875 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5489876 (_70606 : int) : (term922 _70606) = (term133 _70606).
Proof. exact (MK_COMB (@lem5489875) (@lem5489874 _70606)). Qed.
Lemma lem5489877 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5489878 (_70606 : int) : ((term228 _70606) = term129) = ((real_of_int _70606) = term129).
Proof. exact (MK_COMB (@lem5489876 _70606) (@lem5489877)). Qed.
Lemma lem5489879 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : (real_of_int _70606) = term129.
Proof. exact (EQ_MP (@lem5489878 _70606) (@lem5489873 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489880 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term923 _70606 _70608.
Proof. exact (conj (@lem5489879 _70607 _70606 _70608 h1) (@lem5489866 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489882 (x : real) (y : real) : term241 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5489883 (_70606 : int) (_70608 : int) : term924 _70606 _70608.
Proof. exact (@lem5489882 (real_of_int _70606) (term552 _70606 _70608)). Qed.
Lemma lem5489884 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term925 _70606 _70608.
Proof. exact (@lem5489883 _70606 _70608 (@lem5489880 _70607 _70606 _70608 h1)). Qed.
Lemma lem5489885 (_70606 : int) (_70608 : int) : (term926 _70606 _70608) = (term927 _70606 _70608).
Proof. exact (@lem1982763 (real_of_int _70606) (term239 _70606) (term546 _70608)). Qed.
Lemma lem5489886 (_70606 : int) : (term835 _70606) = (term247 _70606).
Proof. exact (@lem1982715 term164 (real_of_int _70606)). Qed.
Lemma lem5489888 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5489889 : term143 = term191.
Proof. exact (@lem5489888 term144). Qed.
Lemma lem5489891 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5489892 : term164 = term165.
Proof. exact (@lem5489891 term144). Qed.
Lemma lem5489893 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489894 : term248 = term249.
Proof. exact (MK_COMB (@lem5489893) (@lem5489892)). Qed.
Lemma lem5489895 : term250 = term251.
Proof. exact (MK_COMB (@lem5489894) (@lem5489889)). Qed.
Lemma lem5489896 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5489898 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489899 : term211 = term217.
Proof. exact (@lem5489898 (NUMERAL 0) term144). Qed.
Lemma lem5489900 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489901 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489902 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489901 h1) (fun h1 : term217 = True => @lem5489900)). Qed.
Lemma lem5489903 : term217 = True.
Proof. exact (EQ_MP (@lem5489902) (@lem5489900)). Qed.
Lemma lem5489904 : term211 = True.
Proof. exact (TRANS (@lem5489899) (@lem5489903)). Qed.
Lemma lem5489905 : True = term211.
Proof. exact (SYM (@lem5489904)). Qed.
Lemma lem5489906 : term211.
Proof. exact (EQ_MP (@lem5489905) (@lem0)). Qed.
Lemma lem5489907 : term253.
Proof. exact (@lem5489896 (@lem5489906)). Qed.
Lemma lem5489909 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489910 : term211 = term217.
Proof. exact (@lem5489909 (NUMERAL 0) term144). Qed.
Lemma lem5489911 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489912 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489913 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489912 h1) (fun h1 : term217 = True => @lem5489911)). Qed.
Lemma lem5489914 : term217 = True.
Proof. exact (EQ_MP (@lem5489913) (@lem5489911)). Qed.
Lemma lem5489915 : term211 = True.
Proof. exact (TRANS (@lem5489910) (@lem5489914)). Qed.
Lemma lem5489916 : True = term211.
Proof. exact (SYM (@lem5489915)). Qed.
Lemma lem5489917 : term211.
Proof. exact (EQ_MP (@lem5489916) (@lem0)). Qed.
Lemma lem5489918 : term254.
Proof. exact (@lem5489907 (@lem5489917)). Qed.
Lemma lem5489920 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5489921 : term211 = term217.
Proof. exact (@lem5489920 (NUMERAL 0) term144). Qed.
Lemma lem5489922 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5489923 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5489924 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5489923 h1) (fun h1 : term217 = True => @lem5489922)). Qed.
Lemma lem5489925 : term217 = True.
Proof. exact (EQ_MP (@lem5489924) (@lem5489922)). Qed.
Lemma lem5489926 : term211 = True.
Proof. exact (TRANS (@lem5489921) (@lem5489925)). Qed.
Lemma lem5489927 : True = term211.
Proof. exact (SYM (@lem5489926)). Qed.
Lemma lem5489928 : term211.
Proof. exact (EQ_MP (@lem5489927) (@lem0)). Qed.
Lemma lem5489929 : term255.
Proof. exact (@lem5489918 (@lem5489928)). Qed.
Lemma lem5489931 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489932 : term173 = term174.
Proof. exact (@lem5489931 term144 term144). Qed.
Lemma lem5489933 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489934 : term176 = term144.
Proof. exact (EQ_MP (@lem5489933) (@lem940073)). Qed.
Lemma lem5489935 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489936 : term174 = term143.
Proof. exact (MK_COMB (@lem5489935) (@lem5489934)). Qed.
Lemma lem5489937 : term173 = term143.
Proof. exact (TRANS (@lem5489932) (@lem5489936)). Qed.
Lemma lem5489939 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5489940 : term192 = term197.
Proof. exact (@lem5489939 term144 term144). Qed.
Lemma lem5489941 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489942 : term176 = term144.
Proof. exact (EQ_MP (@lem5489941) (@lem940073)). Qed.
Lemma lem5489943 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489944 : term174 = term143.
Proof. exact (MK_COMB (@lem5489943) (@lem5489942)). Qed.
Lemma lem5489945 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5489946 : term197 = term164.
Proof. exact (MK_COMB (@lem5489945) (@lem5489944)). Qed.
Lemma lem5489947 : term192 = term164.
Proof. exact (TRANS (@lem5489940) (@lem5489946)). Qed.
Lemma lem5489948 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489949 : term256 = term248.
Proof. exact (MK_COMB (@lem5489948) (@lem5489947)). Qed.
Lemma lem5489950 : term257 = term250.
Proof. exact (MK_COMB (@lem5489949) (@lem5489937)). Qed.
Lemma lem5489952 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5489953 : term250 = term129.
Proof. exact (@lem5489952 term144). Qed.
Lemma lem5489954 : term257 = term129.
Proof. exact (TRANS (@lem5489950) (@lem5489953)). Qed.
Lemma lem5489955 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489956 : term259 = term260.
Proof. exact (MK_COMB (@lem5489955) (@lem5489954)). Qed.
Lemma lem5489957 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5489958 : term261 = term222.
Proof. exact (MK_COMB (@lem5489956) (@lem5489957)). Qed.
Lemma lem5489960 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489961 : term222 = term129.
Proof. exact (@lem5489960 term144). Qed.
Lemma lem5489962 : term261 = term129.
Proof. exact (TRANS (@lem5489958) (@lem5489961)). Qed.
Lemma lem5489964 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5489965 : term173 = term174.
Proof. exact (@lem5489964 term144 term144). Qed.
Lemma lem5489966 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5489967 : term176 = term144.
Proof. exact (EQ_MP (@lem5489966) (@lem940073)). Qed.
Lemma lem5489968 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5489969 : term174 = term143.
Proof. exact (MK_COMB (@lem5489968) (@lem5489967)). Qed.
Lemma lem5489970 : term173 = term143.
Proof. exact (TRANS (@lem5489965) (@lem5489969)). Qed.
Lemma lem5489971 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5489972 : term262 = term222.
Proof. exact (MK_COMB (@lem5489971) (@lem5489970)). Qed.
Lemma lem5489974 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5489975 : term222 = term129.
Proof. exact (@lem5489974 term144). Qed.
Lemma lem5489976 : term262 = term129.
Proof. exact (TRANS (@lem5489972) (@lem5489975)). Qed.
Lemma lem5489977 : term129 = term262.
Proof. exact (SYM (@lem5489976)). Qed.
Lemma lem5489978 : term261 = term262.
Proof. exact (TRANS (@lem5489962) (@lem5489977)). Qed.
Lemma lem5489979 : term251 = term161.
Proof. exact (@lem5489929 (@lem5489978)). Qed.
Lemma lem5489980 : term250 = term161.
Proof. exact (TRANS (@lem5489895) (@lem5489979)). Qed.
Lemma lem5489982 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5489983 : term161 = term129.
Proof. exact (@lem5489982 term129). Qed.
Lemma lem5489984 : term250 = term129.
Proof. exact (TRANS (@lem5489980) (@lem5489983)). Qed.
Lemma lem5489985 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5489986 : term263 = term260.
Proof. exact (MK_COMB (@lem5489985) (@lem5489984)). Qed.
Lemma lem5489987 (_70606 : int) : (real_of_int _70606) = (real_of_int _70606).
Proof. exact (eq_refl (real_of_int _70606)). Qed.
Lemma lem5489988 (_70606 : int) : (term247 _70606) = (term264 _70606).
Proof. exact (MK_COMB (@lem5489986) (@lem5489987 _70606)). Qed.
Lemma lem5489989 (_70606 : int) : (term835 _70606) = (term264 _70606).
Proof. exact (TRANS (@lem5489886 _70606) (@lem5489988 _70606)). Qed.
Lemma lem5489990 (_70606 : int) : (term264 _70606) = term129.
Proof. exact (@lem1982719 (real_of_int _70606)). Qed.
Lemma lem5489991 (_70606 : int) : (term835 _70606) = term129.
Proof. exact (TRANS (@lem5489989 _70606) (@lem5489990 _70606)). Qed.
Lemma lem5489992 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5489993 (_70606 : int) : (term836 _70606) = term266.
Proof. exact (MK_COMB (@lem5489992) (@lem5489991 _70606)). Qed.
Lemma lem5489994 (_70608 : int) : (term546 _70608) = (term546 _70608).
Proof. exact (eq_refl (term546 _70608)). Qed.
Lemma lem5489995 (_70606 : int) (_70608 : int) : (term927 _70606 _70608) = (term838 _70608).
Proof. exact (MK_COMB (@lem5489993 _70606) (@lem5489994 _70608)). Qed.
Lemma lem5489996 (_70606 : int) (_70608 : int) : (term926 _70606 _70608) = (term838 _70608).
Proof. exact (TRANS (@lem5489885 _70606 _70608) (@lem5489995 _70606 _70608)). Qed.
Lemma lem5489997 (_70608 : int) : (term838 _70608) = (term546 _70608).
Proof. exact (@lem1982721 (term546 _70608)). Qed.
Lemma lem5489998 (_70606 : int) (_70608 : int) : (term926 _70606 _70608) = (term546 _70608).
Proof. exact (TRANS (@lem5489996 _70606 _70608) (@lem5489997 _70608)). Qed.
Lemma lem5489999 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5490000 (_70606 : int) (_70608 : int) : (term928 _70606 _70608) = (term548 _70608).
Proof. exact (MK_COMB (@lem5489999) (@lem5489998 _70606 _70608)). Qed.
Lemma lem5490001 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5490002 (_70606 : int) (_70608 : int) : (term925 _70606 _70608) = (term549 _70608).
Proof. exact (MK_COMB (@lem5490000 _70606 _70608) (@lem5490001)). Qed.
Lemma lem5490003 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term549 _70608.
Proof. exact (EQ_MP (@lem5490002 _70606 _70608) (@lem5489884 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490005 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5490006 : term210 = term211.
Proof. exact (@lem5490005 term129 term143). Qed.
Lemma lem5490008 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490009 : term143 = term191.
Proof. exact (@lem5490008 term144). Qed.
Lemma lem5490011 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490012 : term129 = term161.
Proof. exact (@lem5490011 (NUMERAL 0)). Qed.
Lemma lem5490013 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490014 : term212 = term213.
Proof. exact (MK_COMB (@lem5490013) (@lem5490012)). Qed.
Lemma lem5490015 : term211 = term214.
Proof. exact (MK_COMB (@lem5490014) (@lem5490009)). Qed.
Lemma lem5490016 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5490018 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490019 : term211 = term217.
Proof. exact (@lem5490018 (NUMERAL 0) term144). Qed.
Lemma lem5490020 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490021 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490022 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490021 h1) (fun h1 : term217 = True => @lem5490020)). Qed.
Lemma lem5490023 : term217 = True.
Proof. exact (EQ_MP (@lem5490022) (@lem5490020)). Qed.
Lemma lem5490024 : term211 = True.
Proof. exact (TRANS (@lem5490019) (@lem5490023)). Qed.
Lemma lem5490025 : True = term211.
Proof. exact (SYM (@lem5490024)). Qed.
Lemma lem5490026 : term211.
Proof. exact (EQ_MP (@lem5490025) (@lem0)). Qed.
Lemma lem5490027 : term219.
Proof. exact (@lem5490016 (@lem5490026)). Qed.
Lemma lem5490029 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490030 : term211 = term217.
Proof. exact (@lem5490029 (NUMERAL 0) term144). Qed.
Lemma lem5490031 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490032 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490033 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490032 h1) (fun h1 : term217 = True => @lem5490031)). Qed.
Lemma lem5490034 : term217 = True.
Proof. exact (EQ_MP (@lem5490033) (@lem5490031)). Qed.
Lemma lem5490035 : term211 = True.
Proof. exact (TRANS (@lem5490030) (@lem5490034)). Qed.
Lemma lem5490036 : True = term211.
Proof. exact (SYM (@lem5490035)). Qed.
Lemma lem5490037 : term211.
Proof. exact (EQ_MP (@lem5490036) (@lem0)). Qed.
Lemma lem5490038 : term214 = term220.
Proof. exact (@lem5490027 (@lem5490037)). Qed.
Lemma lem5490040 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490041 : term173 = term174.
Proof. exact (@lem5490040 term144 term144). Qed.
Lemma lem5490042 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490043 : term176 = term144.
Proof. exact (EQ_MP (@lem5490042) (@lem940073)). Qed.
Lemma lem5490044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490045 : term174 = term143.
Proof. exact (MK_COMB (@lem5490044) (@lem5490043)). Qed.
Lemma lem5490046 : term173 = term143.
Proof. exact (TRANS (@lem5490041) (@lem5490045)). Qed.
Lemma lem5490048 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490049 : term222 = term129.
Proof. exact (@lem5490048 term144). Qed.
Lemma lem5490050 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490051 : term223 = term212.
Proof. exact (MK_COMB (@lem5490050) (@lem5490049)). Qed.
Lemma lem5490052 : term220 = term211.
Proof. exact (MK_COMB (@lem5490051) (@lem5490046)). Qed.
Lemma lem5490054 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490055 : term211 = term217.
Proof. exact (@lem5490054 (NUMERAL 0) term144). Qed.
Lemma lem5490056 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490057 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490058 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490057 h1) (fun h1 : term217 = True => @lem5490056)). Qed.
Lemma lem5490059 : term217 = True.
Proof. exact (EQ_MP (@lem5490058) (@lem5490056)). Qed.
Lemma lem5490060 : term211 = True.
Proof. exact (TRANS (@lem5490055) (@lem5490059)). Qed.
Lemma lem5490061 : term220 = True.
Proof. exact (TRANS (@lem5490052) (@lem5490060)). Qed.
Lemma lem5490062 : term214 = True.
Proof. exact (TRANS (@lem5490038) (@lem5490061)). Qed.
Lemma lem5490063 : term211 = True.
Proof. exact (TRANS (@lem5490015) (@lem5490062)). Qed.
Lemma lem5490064 : term210 = True.
Proof. exact (TRANS (@lem5490006) (@lem5490063)). Qed.
Lemma lem5490065 : True = term210.
Proof. exact (SYM (@lem5490064)). Qed.
Lemma lem5490066 : term210.
Proof. exact (EQ_MP (@lem5490065) (@lem0)). Qed.
Lemma lem5490067 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term859 _70608.
Proof. exact (conj (@lem5490066) (@lem5490003 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490069 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5490070 (_70608 : int) : term860 _70608.
Proof. exact (@lem5490069 term143 (term546 _70608)). Qed.
Lemma lem5490071 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term861 _70608.
Proof. exact (@lem5490070 _70608 (@lem5490067 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490072 (_70608 : int) : (term862 _70608) = (term546 _70608).
Proof. exact (@lem1982733 (term546 _70608)). Qed.
Lemma lem5490073 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5490074 (_70608 : int) : (term863 _70608) = (term548 _70608).
Proof. exact (MK_COMB (@lem5490073) (@lem5490072 _70608)). Qed.
Lemma lem5490075 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5490076 (_70608 : int) : (term861 _70608) = (term549 _70608).
Proof. exact (MK_COMB (@lem5490074 _70608) (@lem5490075)). Qed.
Lemma lem5490077 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term549 _70608.
Proof. exact (EQ_MP (@lem5490076 _70608) (@lem5490071 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490079 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5490080 : term210 = term211.
Proof. exact (@lem5490079 term129 term143). Qed.
Lemma lem5490082 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490083 : term143 = term191.
Proof. exact (@lem5490082 term144). Qed.
Lemma lem5490085 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490086 : term129 = term161.
Proof. exact (@lem5490085 (NUMERAL 0)). Qed.
Lemma lem5490087 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490088 : term212 = term213.
Proof. exact (MK_COMB (@lem5490087) (@lem5490086)). Qed.
Lemma lem5490089 : term211 = term214.
Proof. exact (MK_COMB (@lem5490088) (@lem5490083)). Qed.
Lemma lem5490090 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5490092 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490093 : term211 = term217.
Proof. exact (@lem5490092 (NUMERAL 0) term144). Qed.
Lemma lem5490094 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490095 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490096 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490095 h1) (fun h1 : term217 = True => @lem5490094)). Qed.
Lemma lem5490097 : term217 = True.
Proof. exact (EQ_MP (@lem5490096) (@lem5490094)). Qed.
Lemma lem5490098 : term211 = True.
Proof. exact (TRANS (@lem5490093) (@lem5490097)). Qed.
Lemma lem5490099 : True = term211.
Proof. exact (SYM (@lem5490098)). Qed.
Lemma lem5490100 : term211.
Proof. exact (EQ_MP (@lem5490099) (@lem0)). Qed.
Lemma lem5490101 : term219.
Proof. exact (@lem5490090 (@lem5490100)). Qed.
Lemma lem5490103 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490104 : term211 = term217.
Proof. exact (@lem5490103 (NUMERAL 0) term144). Qed.
Lemma lem5490105 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490106 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490107 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490106 h1) (fun h1 : term217 = True => @lem5490105)). Qed.
Lemma lem5490108 : term217 = True.
Proof. exact (EQ_MP (@lem5490107) (@lem5490105)). Qed.
Lemma lem5490109 : term211 = True.
Proof. exact (TRANS (@lem5490104) (@lem5490108)). Qed.
Lemma lem5490110 : True = term211.
Proof. exact (SYM (@lem5490109)). Qed.
Lemma lem5490111 : term211.
Proof. exact (EQ_MP (@lem5490110) (@lem0)). Qed.
Lemma lem5490112 : term214 = term220.
Proof. exact (@lem5490101 (@lem5490111)). Qed.
Lemma lem5490114 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490115 : term173 = term174.
Proof. exact (@lem5490114 term144 term144). Qed.
Lemma lem5490116 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490117 : term176 = term144.
Proof. exact (EQ_MP (@lem5490116) (@lem940073)). Qed.
Lemma lem5490118 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490119 : term174 = term143.
Proof. exact (MK_COMB (@lem5490118) (@lem5490117)). Qed.
Lemma lem5490120 : term173 = term143.
Proof. exact (TRANS (@lem5490115) (@lem5490119)). Qed.
Lemma lem5490122 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490123 : term222 = term129.
Proof. exact (@lem5490122 term144). Qed.
Lemma lem5490124 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490125 : term223 = term212.
Proof. exact (MK_COMB (@lem5490124) (@lem5490123)). Qed.
Lemma lem5490126 : term220 = term211.
Proof. exact (MK_COMB (@lem5490125) (@lem5490120)). Qed.
Lemma lem5490128 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490129 : term211 = term217.
Proof. exact (@lem5490128 (NUMERAL 0) term144). Qed.
Lemma lem5490130 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490131 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490132 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490131 h1) (fun h1 : term217 = True => @lem5490130)). Qed.
Lemma lem5490133 : term217 = True.
Proof. exact (EQ_MP (@lem5490132) (@lem5490130)). Qed.
Lemma lem5490134 : term211 = True.
Proof. exact (TRANS (@lem5490129) (@lem5490133)). Qed.
Lemma lem5490135 : term220 = True.
Proof. exact (TRANS (@lem5490126) (@lem5490134)). Qed.
Lemma lem5490136 : term214 = True.
Proof. exact (TRANS (@lem5490112) (@lem5490135)). Qed.
Lemma lem5490137 : term211 = True.
Proof. exact (TRANS (@lem5490089) (@lem5490136)). Qed.
Lemma lem5490138 : term210 = True.
Proof. exact (TRANS (@lem5490080) (@lem5490137)). Qed.
Lemma lem5490139 : True = term210.
Proof. exact (SYM (@lem5490138)). Qed.
Lemma lem5490140 : term210.
Proof. exact (EQ_MP (@lem5490139) (@lem0)). Qed.
Lemma lem5490141 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term230 _70607 _70608.
Proof. exact (conj (@lem5490140) (@lem5489792 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490143 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5490144 (_70607 : int) (_70608 : int) : term231 _70607 _70608.
Proof. exact (@lem5490143 term143 (term202 _70607 _70608)). Qed.
Lemma lem5490145 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term232 _70607 _70608.
Proof. exact (@lem5490144 _70607 _70608 (@lem5490141 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490146 (_70607 : int) (_70608 : int) : (term233 _70607 _70608) = (term202 _70607 _70608).
Proof. exact (@lem1982733 (term202 _70607 _70608)). Qed.
Lemma lem5490147 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5490148 (_70607 : int) (_70608 : int) : (term234 _70607 _70608) = (term204 _70607 _70608).
Proof. exact (MK_COMB (@lem5490147) (@lem5490146 _70607 _70608)). Qed.
Lemma lem5490149 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5490150 (_70607 : int) (_70608 : int) : (term232 _70607 _70608) = (term205 _70607 _70608).
Proof. exact (MK_COMB (@lem5490148 _70607 _70608) (@lem5490149)). Qed.
Lemma lem5490151 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term205 _70607 _70608.
Proof. exact (EQ_MP (@lem5490150 _70607 _70608) (@lem5490145 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490152 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term929 _70607 _70608.
Proof. exact (conj (@lem5490151 _70607 _70606 _70608 h1) (@lem5490077 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490154 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5490155 (_70607 : int) (_70608 : int) : term930 _70607 _70608.
Proof. exact (@lem5490154 (term202 _70607 _70608) (term546 _70608)). Qed.
Lemma lem5490156 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term931 _70607 _70608.
Proof. exact (@lem5490155 _70607 _70608 (@lem5490152 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490157 (_70607 : int) (_70608 : int) : (term932 _70607 _70608) = (term933 _70607 _70608).
Proof. exact (@lem1982755 (real_of_int _70607) (term201 _70608) (term546 _70608)). Qed.
Lemma lem5490158 (_70608 : int) : (term934 _70608) = (term935 _70608).
Proof. exact (@lem1982753 (term239 _70608) (real_of_int _70608) term164 term164). Qed.
Lemma lem5490159 (_70608 : int) : (term246 _70608) = (term247 _70608).
Proof. exact (@lem1982713 term164 (real_of_int _70608)). Qed.
Lemma lem5490161 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490162 : term143 = term191.
Proof. exact (@lem5490161 term144). Qed.
Lemma lem5490164 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5490165 : term164 = term165.
Proof. exact (@lem5490164 term144). Qed.
Lemma lem5490166 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490167 : term248 = term249.
Proof. exact (MK_COMB (@lem5490166) (@lem5490165)). Qed.
Lemma lem5490168 : term250 = term251.
Proof. exact (MK_COMB (@lem5490167) (@lem5490162)). Qed.
Lemma lem5490169 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5490171 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490172 : term211 = term217.
Proof. exact (@lem5490171 (NUMERAL 0) term144). Qed.
Lemma lem5490173 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490174 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490175 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490174 h1) (fun h1 : term217 = True => @lem5490173)). Qed.
Lemma lem5490176 : term217 = True.
Proof. exact (EQ_MP (@lem5490175) (@lem5490173)). Qed.
Lemma lem5490177 : term211 = True.
Proof. exact (TRANS (@lem5490172) (@lem5490176)). Qed.
Lemma lem5490178 : True = term211.
Proof. exact (SYM (@lem5490177)). Qed.
Lemma lem5490179 : term211.
Proof. exact (EQ_MP (@lem5490178) (@lem0)). Qed.
Lemma lem5490180 : term253.
Proof. exact (@lem5490169 (@lem5490179)). Qed.
Lemma lem5490182 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490183 : term211 = term217.
Proof. exact (@lem5490182 (NUMERAL 0) term144). Qed.
Lemma lem5490184 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490185 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490186 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490185 h1) (fun h1 : term217 = True => @lem5490184)). Qed.
Lemma lem5490187 : term217 = True.
Proof. exact (EQ_MP (@lem5490186) (@lem5490184)). Qed.
Lemma lem5490188 : term211 = True.
Proof. exact (TRANS (@lem5490183) (@lem5490187)). Qed.
Lemma lem5490189 : True = term211.
Proof. exact (SYM (@lem5490188)). Qed.
Lemma lem5490190 : term211.
Proof. exact (EQ_MP (@lem5490189) (@lem0)). Qed.
Lemma lem5490191 : term254.
Proof. exact (@lem5490180 (@lem5490190)). Qed.
Lemma lem5490193 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490194 : term211 = term217.
Proof. exact (@lem5490193 (NUMERAL 0) term144). Qed.
Lemma lem5490195 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490196 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490197 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490196 h1) (fun h1 : term217 = True => @lem5490195)). Qed.
Lemma lem5490198 : term217 = True.
Proof. exact (EQ_MP (@lem5490197) (@lem5490195)). Qed.
Lemma lem5490199 : term211 = True.
Proof. exact (TRANS (@lem5490194) (@lem5490198)). Qed.
Lemma lem5490200 : True = term211.
Proof. exact (SYM (@lem5490199)). Qed.
Lemma lem5490201 : term211.
Proof. exact (EQ_MP (@lem5490200) (@lem0)). Qed.
Lemma lem5490202 : term255.
Proof. exact (@lem5490191 (@lem5490201)). Qed.
Lemma lem5490204 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490205 : term173 = term174.
Proof. exact (@lem5490204 term144 term144). Qed.
Lemma lem5490206 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490207 : term176 = term144.
Proof. exact (EQ_MP (@lem5490206) (@lem940073)). Qed.
Lemma lem5490208 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490209 : term174 = term143.
Proof. exact (MK_COMB (@lem5490208) (@lem5490207)). Qed.
Lemma lem5490210 : term173 = term143.
Proof. exact (TRANS (@lem5490205) (@lem5490209)). Qed.
Lemma lem5490212 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5490213 : term192 = term197.
Proof. exact (@lem5490212 term144 term144). Qed.
Lemma lem5490214 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490215 : term176 = term144.
Proof. exact (EQ_MP (@lem5490214) (@lem940073)). Qed.
Lemma lem5490216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490217 : term174 = term143.
Proof. exact (MK_COMB (@lem5490216) (@lem5490215)). Qed.
Lemma lem5490218 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490219 : term197 = term164.
Proof. exact (MK_COMB (@lem5490218) (@lem5490217)). Qed.
Lemma lem5490220 : term192 = term164.
Proof. exact (TRANS (@lem5490213) (@lem5490219)). Qed.
Lemma lem5490221 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490222 : term256 = term248.
Proof. exact (MK_COMB (@lem5490221) (@lem5490220)). Qed.
Lemma lem5490223 : term257 = term250.
Proof. exact (MK_COMB (@lem5490222) (@lem5490210)). Qed.
Lemma lem5490225 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5490226 : term250 = term129.
Proof. exact (@lem5490225 term144). Qed.
Lemma lem5490227 : term257 = term129.
Proof. exact (TRANS (@lem5490223) (@lem5490226)). Qed.
Lemma lem5490228 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5490229 : term259 = term260.
Proof. exact (MK_COMB (@lem5490228) (@lem5490227)). Qed.
Lemma lem5490230 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5490231 : term261 = term222.
Proof. exact (MK_COMB (@lem5490229) (@lem5490230)). Qed.
Lemma lem5490233 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490234 : term222 = term129.
Proof. exact (@lem5490233 term144). Qed.
Lemma lem5490235 : term261 = term129.
Proof. exact (TRANS (@lem5490231) (@lem5490234)). Qed.
Lemma lem5490237 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490238 : term173 = term174.
Proof. exact (@lem5490237 term144 term144). Qed.
Lemma lem5490239 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490240 : term176 = term144.
Proof. exact (EQ_MP (@lem5490239) (@lem940073)). Qed.
Lemma lem5490241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490242 : term174 = term143.
Proof. exact (MK_COMB (@lem5490241) (@lem5490240)). Qed.
Lemma lem5490243 : term173 = term143.
Proof. exact (TRANS (@lem5490238) (@lem5490242)). Qed.
Lemma lem5490244 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5490245 : term262 = term222.
Proof. exact (MK_COMB (@lem5490244) (@lem5490243)). Qed.
Lemma lem5490247 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490248 : term222 = term129.
Proof. exact (@lem5490247 term144). Qed.
Lemma lem5490249 : term262 = term129.
Proof. exact (TRANS (@lem5490245) (@lem5490248)). Qed.
Lemma lem5490250 : term129 = term262.
Proof. exact (SYM (@lem5490249)). Qed.
Lemma lem5490251 : term261 = term262.
Proof. exact (TRANS (@lem5490235) (@lem5490250)). Qed.
Lemma lem5490252 : term251 = term161.
Proof. exact (@lem5490202 (@lem5490251)). Qed.
Lemma lem5490253 : term250 = term161.
Proof. exact (TRANS (@lem5490168) (@lem5490252)). Qed.
Lemma lem5490255 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5490256 : term161 = term129.
Proof. exact (@lem5490255 term129). Qed.
Lemma lem5490257 : term250 = term129.
Proof. exact (TRANS (@lem5490253) (@lem5490256)). Qed.
Lemma lem5490258 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5490259 : term263 = term260.
Proof. exact (MK_COMB (@lem5490258) (@lem5490257)). Qed.
Lemma lem5490260 (_70608 : int) : (real_of_int _70608) = (real_of_int _70608).
Proof. exact (eq_refl (real_of_int _70608)). Qed.
Lemma lem5490261 (_70608 : int) : (term247 _70608) = (term264 _70608).
Proof. exact (MK_COMB (@lem5490259) (@lem5490260 _70608)). Qed.
Lemma lem5490262 (_70608 : int) : (term246 _70608) = (term264 _70608).
Proof. exact (TRANS (@lem5490159 _70608) (@lem5490261 _70608)). Qed.
Lemma lem5490263 (_70608 : int) : (term264 _70608) = term129.
Proof. exact (@lem1982719 (real_of_int _70608)). Qed.
Lemma lem5490264 (_70608 : int) : (term246 _70608) = term129.
Proof. exact (TRANS (@lem5490262 _70608) (@lem5490263 _70608)). Qed.
Lemma lem5490265 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490266 (_70608 : int) : (term265 _70608) = term266.
Proof. exact (MK_COMB (@lem5490265) (@lem5490264 _70608)). Qed.
Lemma lem5490268 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5490269 : term164 = term165.
Proof. exact (@lem5490268 term144). Qed.
Lemma lem5490271 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5490272 : term164 = term165.
Proof. exact (@lem5490271 term144). Qed.
Lemma lem5490273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490274 : term248 = term249.
Proof. exact (MK_COMB (@lem5490273) (@lem5490272)). Qed.
Lemma lem5490275 : term936 = term937.
Proof. exact (MK_COMB (@lem5490274) (@lem5490269)). Qed.
Lemma lem5490276 : term938.
Proof. exact (@lem1981473 term164 term143 term164 term143 term939 term143). Qed.
Lemma lem5490278 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490279 : term211 = term217.
Proof. exact (@lem5490278 (NUMERAL 0) term144). Qed.
Lemma lem5490280 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490281 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490282 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490281 h1) (fun h1 : term217 = True => @lem5490280)). Qed.
Lemma lem5490283 : term217 = True.
Proof. exact (EQ_MP (@lem5490282) (@lem5490280)). Qed.
Lemma lem5490284 : term211 = True.
Proof. exact (TRANS (@lem5490279) (@lem5490283)). Qed.
Lemma lem5490285 : True = term211.
Proof. exact (SYM (@lem5490284)). Qed.
Lemma lem5490286 : term211.
Proof. exact (EQ_MP (@lem5490285) (@lem0)). Qed.
Lemma lem5490287 : term940.
Proof. exact (@lem5490276 (@lem5490286)). Qed.
Lemma lem5490289 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490290 : term211 = term217.
Proof. exact (@lem5490289 (NUMERAL 0) term144). Qed.
Lemma lem5490291 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490292 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490293 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490292 h1) (fun h1 : term217 = True => @lem5490291)). Qed.
Lemma lem5490294 : term217 = True.
Proof. exact (EQ_MP (@lem5490293) (@lem5490291)). Qed.
Lemma lem5490295 : term211 = True.
Proof. exact (TRANS (@lem5490290) (@lem5490294)). Qed.
Lemma lem5490296 : True = term211.
Proof. exact (SYM (@lem5490295)). Qed.
Lemma lem5490297 : term211.
Proof. exact (EQ_MP (@lem5490296) (@lem0)). Qed.
Lemma lem5490298 : term941.
Proof. exact (@lem5490287 (@lem5490297)). Qed.
Lemma lem5490300 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490301 : term211 = term217.
Proof. exact (@lem5490300 (NUMERAL 0) term144). Qed.
Lemma lem5490302 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490303 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490304 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490303 h1) (fun h1 : term217 = True => @lem5490302)). Qed.
Lemma lem5490305 : term217 = True.
Proof. exact (EQ_MP (@lem5490304) (@lem5490302)). Qed.
Lemma lem5490306 : term211 = True.
Proof. exact (TRANS (@lem5490301) (@lem5490305)). Qed.
Lemma lem5490307 : True = term211.
Proof. exact (SYM (@lem5490306)). Qed.
Lemma lem5490308 : term211.
Proof. exact (EQ_MP (@lem5490307) (@lem0)). Qed.
Lemma lem5490309 : term942.
Proof. exact (@lem5490298 (@lem5490308)). Qed.
Lemma lem5490311 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5490312 : term192 = term197.
Proof. exact (@lem5490311 term144 term144). Qed.
Lemma lem5490313 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490314 : term176 = term144.
Proof. exact (EQ_MP (@lem5490313) (@lem940073)). Qed.
Lemma lem5490315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490316 : term174 = term143.
Proof. exact (MK_COMB (@lem5490315) (@lem5490314)). Qed.
Lemma lem5490317 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490318 : term197 = term164.
Proof. exact (MK_COMB (@lem5490317) (@lem5490316)). Qed.
Lemma lem5490319 : term192 = term164.
Proof. exact (TRANS (@lem5490312) (@lem5490318)). Qed.
Lemma lem5490321 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5490322 : term192 = term197.
Proof. exact (@lem5490321 term144 term144). Qed.
Lemma lem5490323 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490324 : term176 = term144.
Proof. exact (EQ_MP (@lem5490323) (@lem940073)). Qed.
Lemma lem5490325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490326 : term174 = term143.
Proof. exact (MK_COMB (@lem5490325) (@lem5490324)). Qed.
Lemma lem5490327 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490328 : term197 = term164.
Proof. exact (MK_COMB (@lem5490327) (@lem5490326)). Qed.
Lemma lem5490329 : term192 = term164.
Proof. exact (TRANS (@lem5490322) (@lem5490328)). Qed.
Lemma lem5490330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490331 : term256 = term248.
Proof. exact (MK_COMB (@lem5490330) (@lem5490329)). Qed.
Lemma lem5490332 : term943 = term936.
Proof. exact (MK_COMB (@lem5490331) (@lem5490319)). Qed.
Lemma lem5490333 : term936 = term944.
Proof. exact (@lem1367763 term144 term144). Qed.
Lemma lem5490334 : term945 = term946.
Proof. exact (@lem706885). Qed.
Lemma lem5490335 : (term945 = term946) = (term947 = term948).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term946). Qed.
Lemma lem5490336 : term947 = term948.
Proof. exact (EQ_MP (@lem5490335) (@lem5490334)). Qed.
Lemma lem5490337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490338 : term949 = term950.
Proof. exact (MK_COMB (@lem5490337) (@lem5490336)). Qed.
Lemma lem5490339 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490340 : term944 = term939.
Proof. exact (MK_COMB (@lem5490339) (@lem5490338)). Qed.
Lemma lem5490341 : term936 = term939.
Proof. exact (TRANS (@lem5490333) (@lem5490340)). Qed.
Lemma lem5490342 : term943 = term939.
Proof. exact (TRANS (@lem5490332) (@lem5490341)). Qed.
Lemma lem5490343 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5490344 : term951 = term952.
Proof. exact (MK_COMB (@lem5490343) (@lem5490342)). Qed.
Lemma lem5490345 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5490346 : term953 = term954.
Proof. exact (MK_COMB (@lem5490344) (@lem5490345)). Qed.
Lemma lem5490348 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5490349 : term954 = term955.
Proof. exact (@lem5490348 term948 term144). Qed.
Lemma lem5490350 : term956 = term946.
Proof. exact (@lem996237 term946). Qed.
Lemma lem5490351 : (term956 = term946) = (term957 = term948).
Proof. exact (@lem1007663 term946 (BIT1 0) term946). Qed.
Lemma lem5490352 : term957 = term948.
Proof. exact (EQ_MP (@lem5490351) (@lem5490350)). Qed.
Lemma lem5490353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490354 : term958 = term950.
Proof. exact (MK_COMB (@lem5490353) (@lem5490352)). Qed.
Lemma lem5490355 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490356 : term955 = term939.
Proof. exact (MK_COMB (@lem5490355) (@lem5490354)). Qed.
Lemma lem5490357 : term954 = term939.
Proof. exact (TRANS (@lem5490349) (@lem5490356)). Qed.
Lemma lem5490358 : term953 = term939.
Proof. exact (TRANS (@lem5490346) (@lem5490357)). Qed.
Lemma lem5490360 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490361 : term173 = term174.
Proof. exact (@lem5490360 term144 term144). Qed.
Lemma lem5490362 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490363 : term176 = term144.
Proof. exact (EQ_MP (@lem5490362) (@lem940073)). Qed.
Lemma lem5490364 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490365 : term174 = term143.
Proof. exact (MK_COMB (@lem5490364) (@lem5490363)). Qed.
Lemma lem5490366 : term173 = term143.
Proof. exact (TRANS (@lem5490361) (@lem5490365)). Qed.
Lemma lem5490367 : term952 = term952.
Proof. exact (eq_refl term952). Qed.
Lemma lem5490368 : term959 = term954.
Proof. exact (MK_COMB (@lem5490367) (@lem5490366)). Qed.
Lemma lem5490370 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5490371 : term954 = term955.
Proof. exact (@lem5490370 term948 term144). Qed.
Lemma lem5490372 : term956 = term946.
Proof. exact (@lem996237 term946). Qed.
Lemma lem5490373 : (term956 = term946) = (term957 = term948).
Proof. exact (@lem1007663 term946 (BIT1 0) term946). Qed.
Lemma lem5490374 : term957 = term948.
Proof. exact (EQ_MP (@lem5490373) (@lem5490372)). Qed.
Lemma lem5490375 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490376 : term958 = term950.
Proof. exact (MK_COMB (@lem5490375) (@lem5490374)). Qed.
Lemma lem5490377 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490378 : term955 = term939.
Proof. exact (MK_COMB (@lem5490377) (@lem5490376)). Qed.
Lemma lem5490379 : term954 = term939.
Proof. exact (TRANS (@lem5490371) (@lem5490378)). Qed.
Lemma lem5490380 : term959 = term939.
Proof. exact (TRANS (@lem5490368) (@lem5490379)). Qed.
Lemma lem5490381 : term939 = term959.
Proof. exact (SYM (@lem5490380)). Qed.
Lemma lem5490382 : term953 = term959.
Proof. exact (TRANS (@lem5490358) (@lem5490381)). Qed.
Lemma lem5490383 : term937 = term960.
Proof. exact (@lem5490309 (@lem5490382)). Qed.
Lemma lem5490384 : term936 = term960.
Proof. exact (TRANS (@lem5490275) (@lem5490383)). Qed.
Lemma lem5490386 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5490387 : term960 = term939.
Proof. exact (@lem5490386 term939). Qed.
Lemma lem5490388 : term936 = term939.
Proof. exact (TRANS (@lem5490384) (@lem5490387)). Qed.
Lemma lem5490389 (_70608 : int) : (term935 _70608) = term961.
Proof. exact (MK_COMB (@lem5490266 _70608) (@lem5490388)). Qed.
Lemma lem5490390 (_70608 : int) : (term934 _70608) = term961.
Proof. exact (TRANS (@lem5490158 _70608) (@lem5490389 _70608)). Qed.
Lemma lem5490391 : term961 = term939.
Proof. exact (@lem1982721 term939). Qed.
Lemma lem5490392 (_70608 : int) : (term934 _70608) = term939.
Proof. exact (TRANS (@lem5490390 _70608) (@lem5490391)). Qed.
Lemma lem5490393 (_70607 : int) : (term145 _70607) = (term145 _70607).
Proof. exact (eq_refl (term145 _70607)). Qed.
Lemma lem5490394 (_70608 : int) (_70607 : int) : (term933 _70607 _70608) = (term962 _70607).
Proof. exact (MK_COMB (@lem5490393 _70607) (@lem5490392 _70608)). Qed.
Lemma lem5490395 (_70608 : int) (_70607 : int) : (term932 _70607 _70608) = (term962 _70607).
Proof. exact (TRANS (@lem5490157 _70607 _70608) (@lem5490394 _70608 _70607)). Qed.
Lemma lem5490396 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5490397 (_70608 : int) (_70607 : int) : (term963 _70607 _70608) = (term964 _70607).
Proof. exact (MK_COMB (@lem5490396) (@lem5490395 _70608 _70607)). Qed.
Lemma lem5490398 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5490399 (_70608 : int) (_70607 : int) : (term931 _70607 _70608) = (term965 _70607).
Proof. exact (MK_COMB (@lem5490397 _70608 _70607) (@lem5490398)). Qed.
Lemma lem5490400 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term965 _70607.
Proof. exact (EQ_MP (@lem5490399 _70608 _70607) (@lem5490156 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490402 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5490403 : term210 = term211.
Proof. exact (@lem5490402 term129 term143). Qed.
Lemma lem5490405 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490406 : term143 = term191.
Proof. exact (@lem5490405 term144). Qed.
Lemma lem5490408 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490409 : term129 = term161.
Proof. exact (@lem5490408 (NUMERAL 0)). Qed.
Lemma lem5490410 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490411 : term212 = term213.
Proof. exact (MK_COMB (@lem5490410) (@lem5490409)). Qed.
Lemma lem5490412 : term211 = term214.
Proof. exact (MK_COMB (@lem5490411) (@lem5490406)). Qed.
Lemma lem5490413 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5490415 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490416 : term211 = term217.
Proof. exact (@lem5490415 (NUMERAL 0) term144). Qed.
Lemma lem5490417 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490418 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490419 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490418 h1) (fun h1 : term217 = True => @lem5490417)). Qed.
Lemma lem5490420 : term217 = True.
Proof. exact (EQ_MP (@lem5490419) (@lem5490417)). Qed.
Lemma lem5490421 : term211 = True.
Proof. exact (TRANS (@lem5490416) (@lem5490420)). Qed.
Lemma lem5490422 : True = term211.
Proof. exact (SYM (@lem5490421)). Qed.
Lemma lem5490423 : term211.
Proof. exact (EQ_MP (@lem5490422) (@lem0)). Qed.
Lemma lem5490424 : term219.
Proof. exact (@lem5490413 (@lem5490423)). Qed.
Lemma lem5490426 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490427 : term211 = term217.
Proof. exact (@lem5490426 (NUMERAL 0) term144). Qed.
Lemma lem5490428 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490429 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490430 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490429 h1) (fun h1 : term217 = True => @lem5490428)). Qed.
Lemma lem5490431 : term217 = True.
Proof. exact (EQ_MP (@lem5490430) (@lem5490428)). Qed.
Lemma lem5490432 : term211 = True.
Proof. exact (TRANS (@lem5490427) (@lem5490431)). Qed.
Lemma lem5490433 : True = term211.
Proof. exact (SYM (@lem5490432)). Qed.
Lemma lem5490434 : term211.
Proof. exact (EQ_MP (@lem5490433) (@lem0)). Qed.
Lemma lem5490435 : term214 = term220.
Proof. exact (@lem5490424 (@lem5490434)). Qed.
Lemma lem5490437 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490438 : term173 = term174.
Proof. exact (@lem5490437 term144 term144). Qed.
Lemma lem5490439 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490440 : term176 = term144.
Proof. exact (EQ_MP (@lem5490439) (@lem940073)). Qed.
Lemma lem5490441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490442 : term174 = term143.
Proof. exact (MK_COMB (@lem5490441) (@lem5490440)). Qed.
Lemma lem5490443 : term173 = term143.
Proof. exact (TRANS (@lem5490438) (@lem5490442)). Qed.
Lemma lem5490445 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490446 : term222 = term129.
Proof. exact (@lem5490445 term144). Qed.
Lemma lem5490447 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490448 : term223 = term212.
Proof. exact (MK_COMB (@lem5490447) (@lem5490446)). Qed.
Lemma lem5490449 : term220 = term211.
Proof. exact (MK_COMB (@lem5490448) (@lem5490443)). Qed.
Lemma lem5490451 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490452 : term211 = term217.
Proof. exact (@lem5490451 (NUMERAL 0) term144). Qed.
Lemma lem5490453 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490454 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490455 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490454 h1) (fun h1 : term217 = True => @lem5490453)). Qed.
Lemma lem5490456 : term217 = True.
Proof. exact (EQ_MP (@lem5490455) (@lem5490453)). Qed.
Lemma lem5490457 : term211 = True.
Proof. exact (TRANS (@lem5490452) (@lem5490456)). Qed.
Lemma lem5490458 : term220 = True.
Proof. exact (TRANS (@lem5490449) (@lem5490457)). Qed.
Lemma lem5490459 : term214 = True.
Proof. exact (TRANS (@lem5490435) (@lem5490458)). Qed.
Lemma lem5490460 : term211 = True.
Proof. exact (TRANS (@lem5490412) (@lem5490459)). Qed.
Lemma lem5490461 : term210 = True.
Proof. exact (TRANS (@lem5490403) (@lem5490460)). Qed.
Lemma lem5490462 : True = term210.
Proof. exact (SYM (@lem5490461)). Qed.
Lemma lem5490463 : term210.
Proof. exact (EQ_MP (@lem5490462) (@lem0)). Qed.
Lemma lem5490464 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term966 _70607.
Proof. exact (conj (@lem5490463) (@lem5490400 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490466 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5490467 (_70607 : int) : term967 _70607.
Proof. exact (@lem5490466 term143 (term962 _70607)). Qed.
Lemma lem5490468 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term968 _70607.
Proof. exact (@lem5490467 _70607 (@lem5490464 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490469 (_70607 : int) : (term969 _70607) = (term962 _70607).
Proof. exact (@lem1982733 (term962 _70607)). Qed.
Lemma lem5490470 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5490471 (_70607 : int) : (term970 _70607) = (term964 _70607).
Proof. exact (MK_COMB (@lem5490470) (@lem5490469 _70607)). Qed.
Lemma lem5490472 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5490473 (_70607 : int) : (term968 _70607) = (term965 _70607).
Proof. exact (MK_COMB (@lem5490471 _70607) (@lem5490472)). Qed.
Lemma lem5490474 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term965 _70607.
Proof. exact (EQ_MP (@lem5490473 _70607) (@lem5490468 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490476 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5490477 : term210 = term211.
Proof. exact (@lem5490476 term129 term143). Qed.
Lemma lem5490479 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490480 : term143 = term191.
Proof. exact (@lem5490479 term144). Qed.
Lemma lem5490482 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490483 : term129 = term161.
Proof. exact (@lem5490482 (NUMERAL 0)). Qed.
Lemma lem5490484 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490485 : term212 = term213.
Proof. exact (MK_COMB (@lem5490484) (@lem5490483)). Qed.
Lemma lem5490486 : term211 = term214.
Proof. exact (MK_COMB (@lem5490485) (@lem5490480)). Qed.
Lemma lem5490487 : term215.
Proof. exact (@lem1980255 term129 term143 term143 term143). Qed.
Lemma lem5490489 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490490 : term211 = term217.
Proof. exact (@lem5490489 (NUMERAL 0) term144). Qed.
Lemma lem5490491 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490492 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490493 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490492 h1) (fun h1 : term217 = True => @lem5490491)). Qed.
Lemma lem5490494 : term217 = True.
Proof. exact (EQ_MP (@lem5490493) (@lem5490491)). Qed.
Lemma lem5490495 : term211 = True.
Proof. exact (TRANS (@lem5490490) (@lem5490494)). Qed.
Lemma lem5490496 : True = term211.
Proof. exact (SYM (@lem5490495)). Qed.
Lemma lem5490497 : term211.
Proof. exact (EQ_MP (@lem5490496) (@lem0)). Qed.
Lemma lem5490498 : term219.
Proof. exact (@lem5490487 (@lem5490497)). Qed.
Lemma lem5490500 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490501 : term211 = term217.
Proof. exact (@lem5490500 (NUMERAL 0) term144). Qed.
Lemma lem5490502 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490503 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490504 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490503 h1) (fun h1 : term217 = True => @lem5490502)). Qed.
Lemma lem5490505 : term217 = True.
Proof. exact (EQ_MP (@lem5490504) (@lem5490502)). Qed.
Lemma lem5490506 : term211 = True.
Proof. exact (TRANS (@lem5490501) (@lem5490505)). Qed.
Lemma lem5490507 : True = term211.
Proof. exact (SYM (@lem5490506)). Qed.
Lemma lem5490508 : term211.
Proof. exact (EQ_MP (@lem5490507) (@lem0)). Qed.
Lemma lem5490509 : term214 = term220.
Proof. exact (@lem5490498 (@lem5490508)). Qed.
Lemma lem5490511 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490512 : term173 = term174.
Proof. exact (@lem5490511 term144 term144). Qed.
Lemma lem5490513 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490514 : term176 = term144.
Proof. exact (EQ_MP (@lem5490513) (@lem940073)). Qed.
Lemma lem5490515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490516 : term174 = term143.
Proof. exact (MK_COMB (@lem5490515) (@lem5490514)). Qed.
Lemma lem5490517 : term173 = term143.
Proof. exact (TRANS (@lem5490512) (@lem5490516)). Qed.
Lemma lem5490519 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490520 : term222 = term129.
Proof. exact (@lem5490519 term144). Qed.
Lemma lem5490521 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5490522 : term223 = term212.
Proof. exact (MK_COMB (@lem5490521) (@lem5490520)). Qed.
Lemma lem5490523 : term220 = term211.
Proof. exact (MK_COMB (@lem5490522) (@lem5490517)). Qed.
Lemma lem5490525 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490526 : term211 = term217.
Proof. exact (@lem5490525 (NUMERAL 0) term144). Qed.
Lemma lem5490527 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490528 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490529 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490528 h1) (fun h1 : term217 = True => @lem5490527)). Qed.
Lemma lem5490530 : term217 = True.
Proof. exact (EQ_MP (@lem5490529) (@lem5490527)). Qed.
Lemma lem5490531 : term211 = True.
Proof. exact (TRANS (@lem5490526) (@lem5490530)). Qed.
Lemma lem5490532 : term220 = True.
Proof. exact (TRANS (@lem5490523) (@lem5490531)). Qed.
Lemma lem5490533 : term214 = True.
Proof. exact (TRANS (@lem5490509) (@lem5490532)). Qed.
Lemma lem5490534 : term211 = True.
Proof. exact (TRANS (@lem5490486) (@lem5490533)). Qed.
Lemma lem5490535 : term210 = True.
Proof. exact (TRANS (@lem5490477) (@lem5490534)). Qed.
Lemma lem5490536 : True = term210.
Proof. exact (SYM (@lem5490535)). Qed.
Lemma lem5490537 : term210.
Proof. exact (EQ_MP (@lem5490536) (@lem0)). Qed.
Lemma lem5490538 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term871 _70607.
Proof. exact (conj (@lem5490537) (@lem5489790 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490540 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5490541 (_70607 : int) : term872 _70607.
Proof. exact (@lem5490540 term143 (term239 _70607)). Qed.
Lemma lem5490542 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term873 _70607.
Proof. exact (@lem5490541 _70607 (@lem5490538 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490543 (_70607 : int) : (term874 _70607) = (term239 _70607).
Proof. exact (@lem1982733 (term239 _70607)). Qed.
Lemma lem5490544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5490545 (_70607 : int) : (term875 _70607) = (term575 _70607).
Proof. exact (MK_COMB (@lem5490544) (@lem5490543 _70607)). Qed.
Lemma lem5490546 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5490547 (_70607 : int) : (term873 _70607) = (term576 _70607).
Proof. exact (MK_COMB (@lem5490545 _70607) (@lem5490546)). Qed.
Lemma lem5490548 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term576 _70607.
Proof. exact (EQ_MP (@lem5490547 _70607) (@lem5490542 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490549 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term971 _70607.
Proof. exact (conj (@lem5490548 _70607 _70606 _70608 h1) (@lem5490474 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490551 (x : real) (y : real) : term277 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5490552 (_70607 : int) : term972 _70607.
Proof. exact (@lem5490551 (term239 _70607) (term962 _70607)). Qed.
Lemma lem5490553 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term973 _70607.
Proof. exact (@lem5490552 _70607 (@lem5490549 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490554 (_70607 : int) : (term974 _70607) = (term975 _70607).
Proof. exact (@lem1982763 (term239 _70607) (real_of_int _70607) term939). Qed.
Lemma lem5490555 (_70607 : int) : (term246 _70607) = (term247 _70607).
Proof. exact (@lem1982713 term164 (real_of_int _70607)). Qed.
Lemma lem5490557 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490558 : term143 = term191.
Proof. exact (@lem5490557 term144). Qed.
Lemma lem5490560 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5490561 : term164 = term165.
Proof. exact (@lem5490560 term144). Qed.
Lemma lem5490562 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490563 : term248 = term249.
Proof. exact (MK_COMB (@lem5490562) (@lem5490561)). Qed.
Lemma lem5490564 : term250 = term251.
Proof. exact (MK_COMB (@lem5490563) (@lem5490558)). Qed.
Lemma lem5490565 : term252.
Proof. exact (@lem1981473 term164 term143 term143 term143 term129 term143). Qed.
Lemma lem5490567 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490568 : term211 = term217.
Proof. exact (@lem5490567 (NUMERAL 0) term144). Qed.
Lemma lem5490569 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490570 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490571 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490570 h1) (fun h1 : term217 = True => @lem5490569)). Qed.
Lemma lem5490572 : term217 = True.
Proof. exact (EQ_MP (@lem5490571) (@lem5490569)). Qed.
Lemma lem5490573 : term211 = True.
Proof. exact (TRANS (@lem5490568) (@lem5490572)). Qed.
Lemma lem5490574 : True = term211.
Proof. exact (SYM (@lem5490573)). Qed.
Lemma lem5490575 : term211.
Proof. exact (EQ_MP (@lem5490574) (@lem0)). Qed.
Lemma lem5490576 : term253.
Proof. exact (@lem5490565 (@lem5490575)). Qed.
Lemma lem5490578 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490579 : term211 = term217.
Proof. exact (@lem5490578 (NUMERAL 0) term144). Qed.
Lemma lem5490580 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490581 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490582 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490581 h1) (fun h1 : term217 = True => @lem5490580)). Qed.
Lemma lem5490583 : term217 = True.
Proof. exact (EQ_MP (@lem5490582) (@lem5490580)). Qed.
Lemma lem5490584 : term211 = True.
Proof. exact (TRANS (@lem5490579) (@lem5490583)). Qed.
Lemma lem5490585 : True = term211.
Proof. exact (SYM (@lem5490584)). Qed.
Lemma lem5490586 : term211.
Proof. exact (EQ_MP (@lem5490585) (@lem0)). Qed.
Lemma lem5490587 : term254.
Proof. exact (@lem5490576 (@lem5490586)). Qed.
Lemma lem5490589 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490590 : term211 = term217.
Proof. exact (@lem5490589 (NUMERAL 0) term144). Qed.
Lemma lem5490591 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490592 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490593 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490592 h1) (fun h1 : term217 = True => @lem5490591)). Qed.
Lemma lem5490594 : term217 = True.
Proof. exact (EQ_MP (@lem5490593) (@lem5490591)). Qed.
Lemma lem5490595 : term211 = True.
Proof. exact (TRANS (@lem5490590) (@lem5490594)). Qed.
Lemma lem5490596 : True = term211.
Proof. exact (SYM (@lem5490595)). Qed.
Lemma lem5490597 : term211.
Proof. exact (EQ_MP (@lem5490596) (@lem0)). Qed.
Lemma lem5490598 : term255.
Proof. exact (@lem5490587 (@lem5490597)). Qed.
Lemma lem5490600 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490601 : term173 = term174.
Proof. exact (@lem5490600 term144 term144). Qed.
Lemma lem5490602 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490603 : term176 = term144.
Proof. exact (EQ_MP (@lem5490602) (@lem940073)). Qed.
Lemma lem5490604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490605 : term174 = term143.
Proof. exact (MK_COMB (@lem5490604) (@lem5490603)). Qed.
Lemma lem5490606 : term173 = term143.
Proof. exact (TRANS (@lem5490601) (@lem5490605)). Qed.
Lemma lem5490608 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5490609 : term192 = term197.
Proof. exact (@lem5490608 term144 term144). Qed.
Lemma lem5490610 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490611 : term176 = term144.
Proof. exact (EQ_MP (@lem5490610) (@lem940073)). Qed.
Lemma lem5490612 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490613 : term174 = term143.
Proof. exact (MK_COMB (@lem5490612) (@lem5490611)). Qed.
Lemma lem5490614 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490615 : term197 = term164.
Proof. exact (MK_COMB (@lem5490614) (@lem5490613)). Qed.
Lemma lem5490616 : term192 = term164.
Proof. exact (TRANS (@lem5490609) (@lem5490615)). Qed.
Lemma lem5490617 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490618 : term256 = term248.
Proof. exact (MK_COMB (@lem5490617) (@lem5490616)). Qed.
Lemma lem5490619 : term257 = term250.
Proof. exact (MK_COMB (@lem5490618) (@lem5490606)). Qed.
Lemma lem5490621 (m : nat) : (term258 m) = term129.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5490622 : term250 = term129.
Proof. exact (@lem5490621 term144). Qed.
Lemma lem5490623 : term257 = term129.
Proof. exact (TRANS (@lem5490619) (@lem5490622)). Qed.
Lemma lem5490624 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5490625 : term259 = term260.
Proof. exact (MK_COMB (@lem5490624) (@lem5490623)). Qed.
Lemma lem5490626 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5490627 : term261 = term222.
Proof. exact (MK_COMB (@lem5490625) (@lem5490626)). Qed.
Lemma lem5490629 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490630 : term222 = term129.
Proof. exact (@lem5490629 term144). Qed.
Lemma lem5490631 : term261 = term129.
Proof. exact (TRANS (@lem5490627) (@lem5490630)). Qed.
Lemma lem5490633 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5490634 : term173 = term174.
Proof. exact (@lem5490633 term144 term144). Qed.
Lemma lem5490635 : (term175 = (BIT1 0)) = (term176 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5490636 : term176 = term144.
Proof. exact (EQ_MP (@lem5490635) (@lem940073)). Qed.
Lemma lem5490637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490638 : term174 = term143.
Proof. exact (MK_COMB (@lem5490637) (@lem5490636)). Qed.
Lemma lem5490639 : term173 = term143.
Proof. exact (TRANS (@lem5490634) (@lem5490638)). Qed.
Lemma lem5490640 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5490641 : term262 = term222.
Proof. exact (MK_COMB (@lem5490640) (@lem5490639)). Qed.
Lemma lem5490643 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490644 : term222 = term129.
Proof. exact (@lem5490643 term144). Qed.
Lemma lem5490645 : term262 = term129.
Proof. exact (TRANS (@lem5490641) (@lem5490644)). Qed.
Lemma lem5490646 : term129 = term262.
Proof. exact (SYM (@lem5490645)). Qed.
Lemma lem5490647 : term261 = term262.
Proof. exact (TRANS (@lem5490631) (@lem5490646)). Qed.
Lemma lem5490648 : term251 = term161.
Proof. exact (@lem5490598 (@lem5490647)). Qed.
Lemma lem5490649 : term250 = term161.
Proof. exact (TRANS (@lem5490564) (@lem5490648)). Qed.
Lemma lem5490651 (x : real) : (term180 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5490652 : term161 = term129.
Proof. exact (@lem5490651 term129). Qed.
Lemma lem5490653 : term250 = term129.
Proof. exact (TRANS (@lem5490649) (@lem5490652)). Qed.
Lemma lem5490654 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5490655 : term263 = term260.
Proof. exact (MK_COMB (@lem5490654) (@lem5490653)). Qed.
Lemma lem5490656 (_70607 : int) : (real_of_int _70607) = (real_of_int _70607).
Proof. exact (eq_refl (real_of_int _70607)). Qed.
Lemma lem5490657 (_70607 : int) : (term247 _70607) = (term264 _70607).
Proof. exact (MK_COMB (@lem5490655) (@lem5490656 _70607)). Qed.
Lemma lem5490658 (_70607 : int) : (term246 _70607) = (term264 _70607).
Proof. exact (TRANS (@lem5490555 _70607) (@lem5490657 _70607)). Qed.
Lemma lem5490659 (_70607 : int) : (term264 _70607) = term129.
Proof. exact (@lem1982719 (real_of_int _70607)). Qed.
Lemma lem5490660 (_70607 : int) : (term246 _70607) = term129.
Proof. exact (TRANS (@lem5490658 _70607) (@lem5490659 _70607)). Qed.
Lemma lem5490661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5490662 (_70607 : int) : (term265 _70607) = term266.
Proof. exact (MK_COMB (@lem5490661) (@lem5490660 _70607)). Qed.
Lemma lem5490663 : term939 = term939.
Proof. exact (eq_refl term939). Qed.
Lemma lem5490664 (_70607 : int) : (term975 _70607) = term961.
Proof. exact (MK_COMB (@lem5490662 _70607) (@lem5490663)). Qed.
Lemma lem5490665 (_70607 : int) : (term974 _70607) = term961.
Proof. exact (TRANS (@lem5490554 _70607) (@lem5490664 _70607)). Qed.
Lemma lem5490666 : term961 = term939.
Proof. exact (@lem1982721 term939). Qed.
Lemma lem5490667 (_70607 : int) : (term974 _70607) = term939.
Proof. exact (TRANS (@lem5490665 _70607) (@lem5490666)). Qed.
Lemma lem5490668 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5490669 (_70607 : int) : (term976 _70607) = term977.
Proof. exact (MK_COMB (@lem5490668) (@lem5490667 _70607)). Qed.
Lemma lem5490670 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5490671 (_70607 : int) : (term973 _70607) = term978.
Proof. exact (MK_COMB (@lem5490669 _70607) (@lem5490670)). Qed.
Lemma lem5490672 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : term978.
Proof. exact (EQ_MP (@lem5490671 _70607) (@lem5490553 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490674 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5490675 : term978 = term979.
Proof. exact (@lem5490674 term129 term939). Qed.
Lemma lem5490677 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5490678 : term939 = term960.
Proof. exact (@lem5490677 term948). Qed.
Lemma lem5490680 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5490681 : term129 = term161.
Proof. exact (@lem5490680 (NUMERAL 0)). Qed.
Lemma lem5490682 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5490683 : term131 = term287.
Proof. exact (MK_COMB (@lem5490682) (@lem5490681)). Qed.
Lemma lem5490684 : term979 = term980.
Proof. exact (MK_COMB (@lem5490683) (@lem5490678)). Qed.
Lemma lem5490685 : term981.
Proof. exact (@lem1980026 term129 term143 term939 term143). Qed.
Lemma lem5490687 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490688 : term211 = term217.
Proof. exact (@lem5490687 (NUMERAL 0) term144). Qed.
Lemma lem5490689 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490690 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490691 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490690 h1) (fun h1 : term217 = True => @lem5490689)). Qed.
Lemma lem5490692 : term217 = True.
Proof. exact (EQ_MP (@lem5490691) (@lem5490689)). Qed.
Lemma lem5490693 : term211 = True.
Proof. exact (TRANS (@lem5490688) (@lem5490692)). Qed.
Lemma lem5490694 : True = term211.
Proof. exact (SYM (@lem5490693)). Qed.
Lemma lem5490695 : term211.
Proof. exact (EQ_MP (@lem5490694) (@lem0)). Qed.
Lemma lem5490696 : term982.
Proof. exact (@lem5490685 (@lem5490695)). Qed.
Lemma lem5490698 (m : nat) (n : nat) : (term216 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5490699 : term211 = term217.
Proof. exact (@lem5490698 (NUMERAL 0) term144). Qed.
Lemma lem5490700 : term218 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5490701 (h1 : term218 = (BIT1 0)) : term217 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5490702 : (term218 = (BIT1 0)) = (term217 = True).
Proof. exact (prop_ext (fun h1 : term218 = (BIT1 0) => @lem5490701 h1) (fun h1 : term217 = True => @lem5490700)). Qed.
Lemma lem5490703 : term217 = True.
Proof. exact (EQ_MP (@lem5490702) (@lem5490700)). Qed.
Lemma lem5490704 : term211 = True.
Proof. exact (TRANS (@lem5490699) (@lem5490703)). Qed.
Lemma lem5490705 : True = term211.
Proof. exact (SYM (@lem5490704)). Qed.
Lemma lem5490706 : term211.
Proof. exact (EQ_MP (@lem5490705) (@lem0)). Qed.
Lemma lem5490707 : term980 = term983.
Proof. exact (@lem5490696 (@lem5490706)). Qed.
Lemma lem5490709 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5490710 : term954 = term955.
Proof. exact (@lem5490709 term948 term144). Qed.
Lemma lem5490711 : term956 = term946.
Proof. exact (@lem996237 term946). Qed.
Lemma lem5490712 : (term956 = term946) = (term957 = term948).
Proof. exact (@lem1007663 term946 (BIT1 0) term946). Qed.
Lemma lem5490713 : term957 = term948.
Proof. exact (EQ_MP (@lem5490712) (@lem5490711)). Qed.
Lemma lem5490714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5490715 : term958 = term950.
Proof. exact (MK_COMB (@lem5490714) (@lem5490713)). Qed.
Lemma lem5490716 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5490717 : term955 = term939.
Proof. exact (MK_COMB (@lem5490716) (@lem5490715)). Qed.
Lemma lem5490718 : term954 = term939.
Proof. exact (TRANS (@lem5490710) (@lem5490717)). Qed.
Lemma lem5490720 (x : nat) : (term221 x) = term129.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5490721 : term222 = term129.
Proof. exact (@lem5490720 term144). Qed.
Lemma lem5490722 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5490723 : term292 = term131.
Proof. exact (MK_COMB (@lem5490722) (@lem5490721)). Qed.
Lemma lem5490724 : term983 = term979.
Proof. exact (MK_COMB (@lem5490723) (@lem5490718)). Qed.
Lemma lem5490726 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5490727 : term979 = term984.
Proof. exact (@lem5490726 (NUMERAL 0) term948). Qed.
Lemma lem5490728 : term985 = term946.
Proof. exact (@lem912803). Qed.
Lemma lem5490729 (h1 : term985 = term946) : (term948 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term946 h1). Qed.
Lemma lem5490730 : (term985 = term946) = ((term948 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term985 = term946 => @lem5490729 h1) (fun h1 : (term948 = (NUMERAL 0)) = False => @lem5490728)). Qed.
Lemma lem5490731 : (term948 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5490730) (@lem5490728)). Qed.
Lemma lem5490732 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5490733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5490734 : term296 = (and True).
Proof. exact (MK_COMB (@lem5490733) (@lem5490732)). Qed.
Lemma lem5490735 : term984 = (True /\ False).
Proof. exact (MK_COMB (@lem5490734) (@lem5490731)). Qed.
Lemma lem5490737 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5490738 : term984 = False.
Proof. exact (TRANS (@lem5490735) (@lem5490737)). Qed.
Lemma lem5490739 : term979 = False.
Proof. exact (TRANS (@lem5490727) (@lem5490738)). Qed.
Lemma lem5490740 : term983 = False.
Proof. exact (TRANS (@lem5490724) (@lem5490739)). Qed.
Lemma lem5490741 : term980 = False.
Proof. exact (TRANS (@lem5490707) (@lem5490740)). Qed.
Lemma lem5490742 : term979 = False.
Proof. exact (TRANS (@lem5490684) (@lem5490741)). Qed.
Lemma lem5490743 : term978 = False.
Proof. exact (TRANS (@lem5490675) (@lem5490742)). Qed.
Lemma lem5490744 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term986 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5490743) (@lem5490672 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490745 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term775 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5488810 _70607 _70606 _70608 h1) (fun h0 : term920 _70607 _70606 _70608 => @lem5489777 _70607 _70606 _70608 h0) (fun h0 : term986 _70607 _70606 _70608 => @lem5490744 _70607 _70606 _70608 h0)). Qed.
Lemma lem5490746 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term784 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5487057 _70607 _70606 _70608 h1) (fun h0 : term779 _70607 _70606 _70608 => @lem5488809 _70607 _70606 _70608 h0) (fun h0 : term775 _70607 _70606 _70608 => @lem5490745 _70607 _70606 _70608 h0)). Qed.
Lemma lem5490747 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term800 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5485622 _70607 _70606 _70608 h1) (fun h0 : term797 _70606 _70607 _70608 => @lem5487056 _70606 _70607 _70608 h0) (fun h0 : term784 _70607 _70606 _70608 => @lem5490746 _70607 _70606 _70608 h0)). Qed.
Lemma lem5490748 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term816 _70607 _70606 _70608) : False.
Proof. exact (or_elim (@lem5483042 _70607 _70606 _70608 h1) (fun h0 : term813 _70607 _70606 _70608 => @lem5485621 _70607 _70606 _70608 h0) (fun h0 : term800 _70607 _70606 _70608 => @lem5490747 _70607 _70606 _70608 h0)). Qed.
Lemma lem5490750 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term816 _70607 _70606 _70608) : term816 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5490751 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term816 _70607 _70606 _70608) : (term816 _70607 _70606 _70608) = False.
Proof. exact (prop_ext (fun h2 : term816 _70607 _70606 _70608 => @lem5490748 _70607 _70606 _70608 h1) (fun h2 : False => @lem5490750 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490752 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term816 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5490751 _70607 _70606 _70608 h1) (@lem5490750 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490753 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term536 _70607 _70606 _70608) : term536 _70607 _70606 _70608.
Proof. exact (h1). Qed.
Lemma lem5490754 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term536 _70607 _70606 _70608) : term816 _70607 _70606 _70608.
Proof. exact (EQ_MP (@lem5482972 _70607 _70606 _70608) (@lem5490753 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490755 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term536 _70607 _70606 _70608) : (term816 _70607 _70606 _70608) = False.
Proof. exact (prop_ext (fun h2 : term816 _70607 _70606 _70608 => @lem5490752 _70607 _70606 _70608 h2) (fun h2 : False => @lem5490754 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490756 (_70607 : int) (_70606 : int) (_70608 : int) (h1 : term536 _70607 _70606 _70608) : False.
Proof. exact (EQ_MP (@lem5490755 _70607 _70606 _70608 h1) (@lem5490754 _70607 _70606 _70608 h1)). Qed.
Lemma lem5490757 (_70607 : int) (_70606 : int) (_70608 : int) : term987 _70607 _70606 _70608.
Proof. exact (fun h0 : term536 _70607 _70606 _70608 => @lem5490756 _70607 _70606 _70608 h0). Qed.
Lemma lem5490758 (_70607 : int) (_70606 : int) (_70608 : int) : term988 _70607 _70606 _70608.
Proof. exact (@lem1386578 (term989 _70607 _70606 _70608)). Qed.
Lemma lem5490761 (_70607 : int) (_70606 : int) (_70608 : int) : term989 _70607 _70606 _70608.
Proof. exact (@lem5490758 _70607 _70606 _70608 (@lem5490757 _70607 _70606 _70608)). Qed.
Lemma lem5490762 (_70607 : int) (_70608 : int) (_70606 : int) : (term535 _70607 _70606 _70608) = (term492 _70607 _70608 _70606).
Proof. exact (SYM (@lem5481562 _70607 _70606 _70608)). Qed.
Lemma lem5490763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5490764 (_70607 : int) (_70608 : int) (_70606 : int) : (term989 _70607 _70606 _70608) = (term426 _70607 _70608 _70606).
Proof. exact (MK_COMB (@lem5490763) (@lem5490762 _70607 _70608 _70606)). Qed.
Lemma lem5490765 (_70607 : int) (_70608 : int) (_70606 : int) : term426 _70607 _70608 _70606.
Proof. exact (EQ_MP (@lem5490764 _70607 _70608 _70606) (@lem5490761 _70607 _70606 _70608)). Qed.
Lemma lem5490766 (_70607 : int) (_70608 : int) (_70606 : int) : term427 _70607 _70608 _70606.
Proof. exact (EQ_MP (@lem5481121 _70607 _70608 _70606) (@lem5490765 _70607 _70608 _70606)). Qed.
Lemma lem5490767 (n : nat) (x : nat) (d : nat) : term990 n x d.
Proof. exact (@lem5490766 (int_of_num n) (int_of_num x) (int_of_num d)). Qed.
Lemma lem5490768 (n : nat) (x : nat) (d : nat) : term991 n x d.
Proof. exact (@lem5490767 n x d (@lem5481114 d)). Qed.
Lemma lem5490769 (n : nat) (x : nat) (d : nat) : term992 n x d.
Proof. exact (@lem5490768 n x d (@lem5481117 n)). Qed.
Lemma lem5490770 (n : nat) (x : nat) (d : nat) : term421 n x d.
Proof. exact (@lem5490769 n x d (@lem5481120 x)). Qed.
Lemma lem5490771 (n : nat) (x : nat) : term423 n x.
Proof. exact (fun d : nat => @lem5490770 n x d). Qed.
Lemma lem5490772 (n : nat) : term425 n.
Proof. exact (fun x : nat => @lem5490771 n x). Qed.
Lemma lem5490773 (n : nat) : (term425 n) = (term302 n).
Proof. exact (SYM (@lem5481111 n)). Qed.
Lemma lem5490774 (n : nat) : term302 n.
Proof. exact (EQ_MP (@lem5490773 n) (@lem5490772 n)). Qed.
Lemma lem5490775 (n : nat) : (term302 n) = ((term302 n) = True).
Proof. exact (@lem7 (term302 n)). Qed.
Lemma lem5490776 (n : nat) : (term302 n) = True.
Proof. exact (EQ_MP (@lem5490775 n) (@lem5490774 n)). Qed.
Lemma lem5490777 (n : nat) : True = (term302 n).
Proof. exact (SYM (@lem5490776 n)). Qed.
Lemma lem5490778 (n : nat) : term302 n.
Proof. exact (EQ_MP (@lem5490777 n) (@lem0)). Qed.
Lemma lem5490779 (n : nat) (h1 : term42 n) : term74 n.
Proof. exact (@lem5490778 n (@lem5479491 n h1)). Qed.
Lemma lem5490782 (n : nat) (h1 : term42 n) : (term28 n) = (term26 n).
Proof. exact (EQ_MP (@lem5479619 n) (@lem5490779 n h1)). Qed.
Lemma lem5490783 (n : nat) (h1 : term42 n) : (term42 n) = ((term28 n) = (term26 n)).
Proof. exact (prop_ext (fun h2 : term42 n => @lem5490782 n h1) (fun h2 : (term28 n) = (term26 n) => @lem5479491 n h1)). Qed.
Lemma lem5490784 (n : nat) (h1 : term42 n) : (term28 n) = (term26 n).
Proof. exact (EQ_MP (@lem5490783 n h1) (@lem5479491 n h1)). Qed.
Lemma lem5490785 (n : nat) : term31 n.
Proof. exact (fun h0 : term42 n => @lem5490784 n h0). Qed.
Lemma lem5490786 (n : nat) (h1 : n = (NUMERAL 0)) : (term28 n) = (@EMPTY nat).
Proof. exact (EQ_MP (@lem5479562 n) (@lem5480742 n h1)). Qed.
Lemma lem5490787 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((term28 n) = (@EMPTY nat)).
Proof. exact (prop_ext (fun h2 : n = (NUMERAL 0) => @lem5490786 n h1) (fun h2 : (term28 n) = (@EMPTY nat) => @lem5479474 n h1)). Qed.
Lemma lem5490788 (n : nat) (h1 : n = (NUMERAL 0)) : (term28 n) = (@EMPTY nat).
Proof. exact (EQ_MP (@lem5490787 n h1) (@lem5479474 n h1)). Qed.
Lemma lem5490789 (n : nat) : term35 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem5490788 n h0). Qed.
Lemma lem5490790 (n : nat) : term38 n.
Proof. exact (conj (@lem5490789 n) (@lem5490785 n)). Qed.
Lemma lem5490791 (n : nat) : (term28 n) = (term39 n).
Proof. exact (EQ_MP (@lem5479473 n) (@lem5490790 n)). Qed.
Lemma lem5490796 : term993.
Proof. exact (fun n : nat => @lem5490791 n). Qed.
