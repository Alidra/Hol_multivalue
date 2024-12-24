Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_MONO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_RDIV_EQ_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem191397 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem191398 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem191399 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem191398 t1) (@lem191397 t1)). Qed.
Lemma lem191400 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem191399 t1 t2). Qed.
Lemma lem191401 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem191402 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem191401 t1 t2) (@lem191400 t1 t2)). Qed.
Lemma lem191403 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem191402 t1 t2 t3). Qed.
Lemma lem191404 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem191405 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem191404 t1 t2 t3) (@lem191403 t1 t2 t3)). Qed.
Lemma lem191406 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem191405 t1 t2 t3)). Qed.
Lemma lem191418 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem191419 (a : nat) (b : nat) : (term8 a b) = (term9 a b).
Proof. exact (@lem191418 (term8 a b)). Qed.
Lemma lem191420 (a : nat) (b : nat) : (term9 a b) = (term8 a b).
Proof. exact (SYM (@lem191419 a b)). Qed.
Lemma lem191421 (a : nat) (b : nat) (h1 : term10 a b) : term10 a b.
Proof. exact (h1). Qed.
Lemma lem191424 (a : nat) (b : nat) (h1 : term11 a b) : term11 a b.
Proof. exact (h1). Qed.
Lemma lem191425 (a : nat) (b : nat) : term12 a b.
Proof. exact (fun h0 : term11 a b => @lem191424 a b h0). Qed.
Lemma lem191426 (a : nat) (b : nat) (h1 : term12 a b) : term12 a b.
Proof. exact (h1). Qed.
Lemma lem191427 (a : nat) (b : nat) (h1 : term11 a b) : term11 a b.
Proof. exact (h1). Qed.
Lemma lem191428 (a : nat) (b : nat) (h1 : term11 a b) (h2 : term12 a b) : term11 a b.
Proof. exact (@lem191426 a b h2 (@lem191427 a b h1)). Qed.
Lemma lem191429 (a : nat) (b : nat) (h1 : term11 a b) : term13 a b.
Proof. exact (fun h0 : term12 a b => @lem191428 a b h1 h0). Qed.
Lemma lem191430 (a : nat) (b : nat) (h1 : term12 a b) : term12 a b.
Proof. exact (h1). Qed.
Lemma lem191431 (a : nat) (b : nat) (h1 : term11 a b) (h2 : term12 a b) : term11 a b.
Proof. exact (@lem191429 a b h1 (@lem191430 a b h2)). Qed.
Lemma lem191432 (a : nat) (b : nat) (h1 : term12 a b) : term12 a b.
Proof. exact (fun h0 : term11 a b => @lem191431 a b h0 h1). Qed.
Lemma lem191433 (a : nat) (b : nat) : term14 a b.
Proof. exact (fun h0 : term12 a b => @lem191432 a b h0). Qed.
Lemma lem191436 (a : nat) (b : nat) : term12 a b.
Proof. exact (@lem191433 a b (@lem191425 a b)). Qed.
Lemma lem191456 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem191457 : term15 = term16.
Proof. exact (@lem191456 term17). Qed.
Lemma lem191462 (a : nat) (b : nat) : (term18 a b) = (term18 a b).
Proof. exact (eq_refl (term18 a b)). Qed.
Lemma lem191463 (a : nat) (b : nat) : (term11 a b) = (term19 a b).
Proof. exact (MK_COMB (@lem191462 a b) (@lem191457)). Qed.
Lemma lem191466 (b : nat) : (term20 b) = (term21 b).
Proof. exact (fun_ext (fun a : nat => @lem191463 a b)). Qed.
Lemma lem191467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191468 (b : nat) : (term22 b) = (term23 b).
Proof. exact (MK_COMB (@lem191467) (@lem191466 b)). Qed.
Lemma lem191473 : term24 = term25.
Proof. exact (fun_ext (fun b : nat => @lem191468 b)). Qed.
Lemma lem191474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191483 : term26 = term27.
Proof. exact (MK_COMB (@lem191474) (@lem191473)). Qed.
Lemma lem191484 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem191485 : term28 = term28.
Proof. exact (fun_ext (fun n : nat => @lem191484 n)). Qed.
Lemma lem191486 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191487 : term17 = term17.
Proof. exact (MK_COMB (@lem191486) (@lem191485)). Qed.
Lemma lem191488 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem191489 : term16 = term16.
Proof. exact (MK_COMB (@lem191488) (@lem191487)). Qed.
Lemma lem191490 (a : nat) (b : nat) : (Peano.le a b) = (Peano.le a b).
Proof. exact (eq_refl (Peano.le a b)). Qed.
Lemma lem191495 (a : nat) (k : nat) (b : nat) : (term29 a k b) = (term29 a k b).
Proof. exact (eq_refl (term29 a k b)). Qed.
Lemma lem191496 (a : nat) (b : nat) : (term30 a b) = (term30 a b).
Proof. exact (fun_ext (fun k : nat => @lem191495 a k b)). Qed.
Lemma lem191497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191498 (a : nat) (b : nat) : (term31 a b) = (term31 a b).
Proof. exact (MK_COMB (@lem191497) (@lem191496 a b)). Qed.
Lemma lem191499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem191500 (a : nat) (b : nat) : (term32 a b) = (term32 a b).
Proof. exact (MK_COMB (@lem191499) (@lem191498 a b)). Qed.
Lemma lem191501 (a : nat) (b : nat) : (term8 a b) = (term8 a b).
Proof. exact (MK_COMB (@lem191500 a b) (@lem191490 a b)). Qed.
Lemma lem191502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem191503 (a : nat) (b : nat) : (term10 a b) = (term10 a b).
Proof. exact (MK_COMB (@lem191502) (@lem191501 a b)). Qed.
Lemma lem191504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem191505 (a : nat) (b : nat) : (term18 a b) = (term18 a b).
Proof. exact (MK_COMB (@lem191504) (@lem191503 a b)). Qed.
Lemma lem191506 (a : nat) (b : nat) : (term19 a b) = (term19 a b).
Proof. exact (MK_COMB (@lem191505 a b) (@lem191489)). Qed.
Lemma lem191507 (b : nat) : (term21 b) = (term21 b).
Proof. exact (fun_ext (fun a : nat => @lem191506 a b)). Qed.
Lemma lem191508 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191509 (b : nat) : (term23 b) = (term23 b).
Proof. exact (MK_COMB (@lem191508) (@lem191507 b)). Qed.
Lemma lem191510 : term25 = term25.
Proof. exact (fun_ext (fun b : nat => @lem191509 b)). Qed.
Lemma lem191511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191512 : term27 = term27.
Proof. exact (MK_COMB (@lem191511) (@lem191510)). Qed.
Lemma lem191545 : term26 = term27.
Proof. exact (TRANS (@lem191483) (@lem191512)). Qed.
Lemma lem191546 : term27 = term26.
Proof. exact (SYM (@lem191545)). Qed.
Lemma lem191547 (a : nat) (b : nat) (h1 : term10 a b) : term10 a b.
Proof. exact (h1). Qed.
Lemma lem191548 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem191555 (a : nat) (k : nat) (b : nat) : (term29 a k b) = (term33 a k b).
Proof. exact (@lem17265 (Peano.le k a) (Peano.le k b)). Qed.
Lemma lem191556 (a : nat) (b : nat) : (term30 a b) = (term34 a b).
Proof. exact (fun_ext (fun k : nat => @lem191555 a k b)). Qed.
Lemma lem191557 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191558 (a : nat) (b : nat) : (term31 a b) = (term35 a b).
Proof. exact (MK_COMB (@lem191557) (@lem191556 a b)). Qed.
Lemma lem191559 (a : nat) (b : nat) : (term36 a b) = (term36 a b).
Proof. exact (eq_refl (term36 a b)). Qed.
Lemma lem191560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem191561 (a : nat) (b : nat) : (term37 a b) = (term38 a b).
Proof. exact (MK_COMB (@lem191560) (@lem191558 a b)). Qed.
Lemma lem191562 (a : nat) (b : nat) : (term39 a b) = (term40 a b).
Proof. exact (MK_COMB (@lem191561 a b) (@lem191559 a b)). Qed.
Lemma lem191563 (a : nat) (b : nat) : (term10 a b) = (term39 a b).
Proof. exact (@lem17362 (term31 a b) (Peano.le a b)). Qed.
Lemma lem191616 (a : nat) (b : nat) : (term10 a b) = (term40 a b).
Proof. exact (TRANS (@lem191563 a b) (@lem191562 a b)). Qed.
Lemma lem191617 (a : nat) (b : nat) (h1 : term10 a b) : term40 a b.
Proof. exact (EQ_MP (@lem191616 a b) (@lem191547 a b h1)). Qed.
Lemma lem191618 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem191619 : term28 = term28.
Proof. exact (fun_ext (fun n : nat => @lem191618 n)). Qed.
Lemma lem191620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191629 : term17 = term17.
Proof. exact (MK_COMB (@lem191620) (@lem191619)). Qed.
Lemma lem191630 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem191629) (@lem191548 h1)). Qed.
Lemma lem191637 (a : nat) (b : nat) : (term36 a b) = (term36 a b).
Proof. exact (eq_refl (term36 a b)). Qed.
Lemma lem191652 (a : nat) (k : nat) (b : nat) : (term33 a k b) = (term33 a k b).
Proof. exact (eq_refl (term33 a k b)). Qed.
Lemma lem191653 (a : nat) (b : nat) : (term34 a b) = (term34 a b).
Proof. exact (fun_ext (fun k : nat => @lem191652 a k b)). Qed.
Lemma lem191654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191655 (a : nat) (b : nat) : (term35 a b) = (term35 a b).
Proof. exact (MK_COMB (@lem191654) (@lem191653 a b)). Qed.
Lemma lem191656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem191657 (a : nat) (b : nat) : (term38 a b) = (term38 a b).
Proof. exact (MK_COMB (@lem191656) (@lem191655 a b)). Qed.
Lemma lem191658 (a : nat) (b : nat) : (term40 a b) = (term40 a b).
Proof. exact (MK_COMB (@lem191657 a b) (@lem191637 a b)). Qed.
Lemma lem191659 (a : nat) (b : nat) (h1 : term10 a b) : term40 a b.
Proof. exact (EQ_MP (@lem191658 a b) (@lem191617 a b h1)). Qed.
Lemma lem191664 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem191665 : term28 = term28.
Proof. exact (fun_ext (fun n : nat => @lem191664 n)). Qed.
Lemma lem191666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191667 : term17 = term17.
Proof. exact (MK_COMB (@lem191666) (@lem191665)). Qed.
Lemma lem191668 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem191667) (@lem191630 h1)). Qed.
Lemma lem191670 (a : nat) (b : nat) (h1 : term10 a b) : term35 a b.
Proof. exact (proj1 (@lem191659 a b h1)). Qed.
Lemma lem191672 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem191673 : term28 = term28.
Proof. exact (fun_ext (fun n : nat => @lem191672 n)). Qed.
Lemma lem191674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191676 : term17 = term17.
Proof. exact (MK_COMB (@lem191674) (@lem191673)). Qed.
Lemma lem191677 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem191676) (@lem191668 h1)). Qed.
Lemma lem191685 (a : nat) (k : nat) (b : nat) : (term33 a k b) = (term33 a k b).
Proof. exact (eq_refl (term33 a k b)). Qed.
Lemma lem191686 (a : nat) (b : nat) : (term34 a b) = (term34 a b).
Proof. exact (fun_ext (fun k : nat => @lem191685 a k b)). Qed.
Lemma lem191687 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem191689 (a : nat) (b : nat) : (term35 a b) = (term35 a b).
Proof. exact (MK_COMB (@lem191687) (@lem191686 a b)). Qed.
Lemma lem191690 (a : nat) (b : nat) (h1 : term10 a b) : term35 a b.
Proof. exact (EQ_MP (@lem191689 a b) (@lem191670 a b h1)). Qed.
Lemma lem191695 (_3884 : nat) (h1 : term17) : term41 _3884.
Proof. exact (@lem191677 h1 _3884). Qed.
Lemma lem191696 (_3884 : nat) : (term41 _3884) = (Peano.le _3884 _3884).
Proof. exact (eq_refl (term41 _3884)). Qed.
Lemma lem191698 (_3885 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term42 a b _3885.
Proof. exact (@lem191690 a b h1 _3885). Qed.
Lemma lem191699 (a : nat) (_3885 : nat) (b : nat) : (term42 a b _3885) = (term33 a _3885 b).
Proof. exact (eq_refl (term42 a b _3885)). Qed.
Lemma lem191708 (_3885 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term33 a _3885 b.
Proof. exact (EQ_MP (@lem191699 a _3885 b) (@lem191698 _3885 a b h1)). Qed.
Lemma lem191710 (a : nat) (b : nat) (h1 : term10 a b) : term36 a b.
Proof. exact (proj2 (@lem191659 a b h1)). Qed.
Lemma lem191712 (_3884 : nat) (h1 : term17) : Peano.le _3884 _3884.
Proof. exact (EQ_MP (@lem191696 _3884) (@lem191695 _3884 h1)). Qed.
Lemma lem191713 (a : nat) (h1 : term17) : Peano.le a a.
Proof. exact (@lem191712 a h1). Qed.
Lemma lem191714 (a : nat) (h1 : term17) : term43 a.
Proof. exact (fun h0 : term44 a => @lem191713 a h1). Qed.
Lemma lem191716 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem191717 (a : nat) : (term43 a) = (Peano.le a a).
Proof. exact (@lem191716 (Peano.le a a)). Qed.
Lemma lem191718 (a : nat) (h1 : term17) : Peano.le a a.
Proof. exact (EQ_MP (@lem191717 a) (@lem191714 a h1)). Qed.
Lemma lem191724 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem191725 (b : nat) (_3885 : nat) (a : nat) : (term33 a _3885 b) = (term46 b _3885 a).
Proof. exact (@lem191724 (Peano.le _3885 b) (term36 _3885 a)). Qed.
Lemma lem191731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem191732 (b : nat) (_3885 : nat) (a : nat) : (term47 a _3885 b) = (term48 b _3885 a).
Proof. exact (MK_COMB (@lem191731) (@lem191725 b _3885 a)). Qed.
Lemma lem191738 (b : nat) (_3885 : nat) (a : nat) : (term46 b _3885 a) = (term46 b _3885 a).
Proof. exact (eq_refl (term46 b _3885 a)). Qed.
Lemma lem191739 (b : nat) (_3885 : nat) (a : nat) : ((term33 a _3885 b) = (term46 b _3885 a)) = ((term46 b _3885 a) = (term46 b _3885 a)).
Proof. exact (MK_COMB (@lem191732 b _3885 a) (@lem191738 b _3885 a)). Qed.
Lemma lem191741 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem191742 (x : Prop) : (x = x) = True.
Proof. exact (@lem191741 Prop x). Qed.
Lemma lem191743 (b : nat) (_3885 : nat) (a : nat) : ((term46 b _3885 a) = (term46 b _3885 a)) = True.
Proof. exact (@lem191742 (term46 b _3885 a)). Qed.
Lemma lem191744 (b : nat) (_3885 : nat) (a : nat) : ((term33 a _3885 b) = (term46 b _3885 a)) = True.
Proof. exact (TRANS (@lem191739 b _3885 a) (@lem191743 b _3885 a)). Qed.
Lemma lem191745 (b : nat) (_3885 : nat) (a : nat) : True = ((term33 a _3885 b) = (term46 b _3885 a)).
Proof. exact (SYM (@lem191744 b _3885 a)). Qed.
Lemma lem191746 (b : nat) (_3885 : nat) (a : nat) : (term33 a _3885 b) = (term46 b _3885 a).
Proof. exact (EQ_MP (@lem191745 b _3885 a) (@lem0)). Qed.
Lemma lem191747 (_3885 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term46 b _3885 a.
Proof. exact (EQ_MP (@lem191746 b _3885 a) (@lem191708 _3885 a b h1)). Qed.
Lemma lem191749 (b : Prop) (a : Prop) : (a \/ b) = (term49 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem191750 (a : nat) (_3885 : nat) (b : nat) : (term46 b _3885 a) = (term50 a _3885 b).
Proof. exact (@lem191749 (term36 _3885 a) (Peano.le _3885 b)). Qed.
Lemma lem191752 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem191753 (_3885 : nat) (a : nat) : (term52 _3885 a) = (Peano.le _3885 a).
Proof. exact (@lem191752 (Peano.le _3885 a)). Qed.
Lemma lem191754 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem191755 (_3885 : nat) (a : nat) : (term53 _3885 a) = (term54 _3885 a).
Proof. exact (MK_COMB (@lem191754) (@lem191753 _3885 a)). Qed.
Lemma lem191756 (_3885 : nat) (b : nat) : (Peano.le _3885 b) = (Peano.le _3885 b).
Proof. exact (eq_refl (Peano.le _3885 b)). Qed.
Lemma lem191757 (a : nat) (_3885 : nat) (b : nat) : (term50 a _3885 b) = (term29 a _3885 b).
Proof. exact (MK_COMB (@lem191755 _3885 a) (@lem191756 _3885 b)). Qed.
Lemma lem191758 (a : nat) (_3885 : nat) (b : nat) : (term46 b _3885 a) = (term29 a _3885 b).
Proof. exact (TRANS (@lem191750 a _3885 b) (@lem191757 a _3885 b)). Qed.
Lemma lem191761 (_3885 : nat) (a : nat) (b : nat) (h1 : term10 a b) : term29 a _3885 b.
Proof. exact (EQ_MP (@lem191758 a _3885 b) (@lem191747 _3885 a b h1)). Qed.
Lemma lem191762 (a : nat) (b : nat) (h1 : term10 a b) : term55 a b.
Proof. exact (@lem191761 a a b h1). Qed.
Lemma lem191765 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : Peano.le a b.
Proof. exact (@lem191762 a b h2 (@lem191718 a h1)). Qed.
Lemma lem191766 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : term56 a b.
Proof. exact (fun h0 : term36 a b => @lem191765 a b h1 h2). Qed.
Lemma lem191768 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem191769 (a : nat) (b : nat) : (term56 a b) = (Peano.le a b).
Proof. exact (@lem191768 (Peano.le a b)). Qed.
Lemma lem191770 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : Peano.le a b.
Proof. exact (EQ_MP (@lem191769 a b) (@lem191766 a b h1 h2)). Qed.
Lemma lem191773 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem191775 (a : nat) (b : nat) : (term36 a b) = (term57 a b).
Proof. exact (@lem191773 (Peano.le a b)). Qed.
Lemma lem191778 (a : nat) (b : nat) (h1 : term10 a b) : term57 a b.
Proof. exact (EQ_MP (@lem191775 a b) (@lem191710 a b h1)). Qed.
Lemma lem191781 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : False.
Proof. exact (@lem191778 a b h2 (@lem191770 a b h1 h2)). Qed.
Lemma lem191782 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : term58.
Proof. exact (fun h0 : ~ False => @lem191781 a b h1 h2). Qed.
Lemma lem191784 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem191785 : term58 = False.
Proof. exact (@lem191784 False). Qed.
Lemma lem191786 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : False.
Proof. exact (EQ_MP (@lem191785) (@lem191782 a b h1 h2)). Qed.
Lemma lem191787 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem191786 a b h1 h2) (fun h3 : False => @lem191677 h1)). Qed.
Lemma lem191788 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : False.
Proof. exact (EQ_MP (@lem191787 a b h1 h2) (@lem191677 h1)). Qed.
Lemma lem191789 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem191788 a b h1 h2) (fun h3 : False => @lem191668 h1)). Qed.
Lemma lem191790 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : False.
Proof. exact (EQ_MP (@lem191789 a b h1 h2) (@lem191668 h1)). Qed.
Lemma lem191791 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem191790 a b h1 h2) (fun h3 : False => @lem191630 h1)). Qed.
Lemma lem191792 (a : nat) (b : nat) (h1 : term17) (h2 : term10 a b) : False.
Proof. exact (EQ_MP (@lem191791 a b h1 h2) (@lem191630 h1)). Qed.
Lemma lem191793 (a : nat) (b : nat) (h1 : term10 a b) : term15.
Proof. exact (fun h0 : term17 => @lem191792 a b h0 h1). Qed.
Lemma lem191794 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem191795 (a : nat) (b : nat) (h1 : term10 a b) : term16.
Proof. exact (EQ_MP (@lem191794) (@lem191793 a b h1)). Qed.
Lemma lem191796 (a : nat) (b : nat) : term19 a b.
Proof. exact (fun h0 : term10 a b => @lem191795 a b h0). Qed.
Lemma lem191801 (b : nat) : term23 b.
Proof. exact (fun a : nat => @lem191796 a b). Qed.
Lemma lem191806 : term27.
Proof. exact (fun b : nat => @lem191801 b). Qed.
Lemma lem191807 : term26.
Proof. exact (EQ_MP (@lem191546) (@lem191806)). Qed.
Lemma lem191808 (b : nat) : term59 b.
Proof. exact (@lem191807 b). Qed.
Lemma lem191809 (b : nat) : (term59 b) = (term22 b).
Proof. exact (eq_refl (term59 b)). Qed.
Lemma lem191810 (b : nat) : term22 b.
Proof. exact (EQ_MP (@lem191809 b) (@lem191808 b)). Qed.
Lemma lem191811 (b : nat) (a : nat) : term60 b a.
Proof. exact (@lem191810 b a). Qed.
Lemma lem191812 (a : nat) (b : nat) : (term60 b a) = (term11 a b).
Proof. exact (eq_refl (term60 b a)). Qed.
Lemma lem191813 (a : nat) (b : nat) : term11 a b.
Proof. exact (EQ_MP (@lem191812 a b) (@lem191811 b a)). Qed.
Lemma lem191815 (a : nat) (b : nat) : term11 a b.
Proof. exact (@lem191436 a b (@lem191813 a b)). Qed.
Lemma lem191816 (a : nat) (b : nat) (h1 : term10 a b) : term15.
Proof. exact (@lem191815 a b (@lem191421 a b h1)). Qed.
Lemma lem191817 (a : nat) (b : nat) (h1 : term10 a b) : False.
Proof. exact (@lem191816 a b h1 (@lem91603)). Qed.
Lemma lem191818 (a : nat) (b : nat) (h1 : term10 a b) : (term10 a b) = False.
Proof. exact (prop_ext (fun h2 : term10 a b => @lem191817 a b h1) (fun h2 : False => @lem191421 a b h1)). Qed.
Lemma lem191819 (a : nat) (b : nat) (h1 : term10 a b) : False.
Proof. exact (EQ_MP (@lem191818 a b h1) (@lem191421 a b h1)). Qed.
Lemma lem191820 (a : nat) (b : nat) : term9 a b.
Proof. exact (fun h0 : term10 a b => @lem191819 a b h0). Qed.
Lemma lem191821 (a : nat) (b : nat) : term8 a b.
Proof. exact (EQ_MP (@lem191420 a b) (@lem191820 a b)). Qed.
Lemma lem191822 (a : nat) (b : nat) (h1 : term8 a b) : term8 a b.
Proof. exact (h1). Qed.
Lemma lem191823 (a : nat) (b : nat) (h1 : term31 a b) : term31 a b.
Proof. exact (h1). Qed.
Lemma lem191824 (a : nat) (b : nat) (h1 : term31 a b) (h2 : term8 a b) : Peano.le a b.
Proof. exact (@lem191822 a b h2 (@lem191823 a b h1)). Qed.
Lemma lem191825 (a : nat) (b : nat) (h1 : term31 a b) : term61 a b.
Proof. exact (fun h0 : term8 a b => @lem191824 a b h1 h0). Qed.
Lemma lem191826 (a : nat) (b : nat) (h1 : term8 a b) : term8 a b.
Proof. exact (h1). Qed.
Lemma lem191827 (a : nat) (b : nat) (h1 : term31 a b) (h2 : term8 a b) : Peano.le a b.
Proof. exact (@lem191825 a b h1 (@lem191826 a b h2)). Qed.
Lemma lem191828 (a : nat) (b : nat) (h1 : term8 a b) : term8 a b.
Proof. exact (fun h0 : term31 a b => @lem191827 a b h0 h1). Qed.
Lemma lem191829 (a : nat) (b : nat) : term62 a b.
Proof. exact (fun h0 : term8 a b => @lem191828 a b h0). Qed.
Lemma lem191831 (p : nat) : term63 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem191832 (p : nat) : (term63 p) = (term64 p).
Proof. exact (eq_refl (term63 p)). Qed.
Lemma lem191833 (p : nat) : term64 p.
Proof. exact (EQ_MP (@lem191832 p) (@lem191831 p)). Qed.
Lemma lem191835 (p : nat) (h1 : term65 p) : term65 p.
Proof. exact (h1). Qed.
Lemma lem191836 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem191837 (n : nat) : term41 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem191838 (n : nat) : (term41 n) = (Peano.le n n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem191839 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem191838 n) (@lem191837 n)). Qed.
Lemma lem191840 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem191842 (n : nat) : term66 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem191843 (n : nat) : (term66 n) = ((term67 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term66 n)). Qed.
Lemma lem191850 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem191851 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem191852 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div m p) = (term67 m).
Proof. exact (MK_COMB (@lem191851 m) (@lem191850 p h1)). Qed.
Lemma lem191854 (n : nat) : (term67 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem191843 n) (@lem191842 n)). Qed.
Lemma lem191855 (m : nat) : (term67 m) = (NUMERAL 0).
Proof. exact (@lem191854 m). Qed.
Lemma lem191856 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div m p) = (NUMERAL 0).
Proof. exact (TRANS (@lem191852 m p h1) (@lem191855 m)). Qed.
Lemma lem191857 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem191858 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term68 m p) = term69.
Proof. exact (MK_COMB (@lem191857) (@lem191856 m p h1)). Qed.
Lemma lem191860 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem191861 (n : nat) : (Nat.div n) = (Nat.div n).
Proof. exact (eq_refl (Nat.div n)). Qed.
Lemma lem191862 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div n p) = (term67 n).
Proof. exact (MK_COMB (@lem191861 n) (@lem191860 p h1)). Qed.
Lemma lem191864 (n : nat) : (term67 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem191843 n) (@lem191842 n)). Qed.
Lemma lem191865 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem191862 n p h1) (@lem191864 n)). Qed.
Lemma lem191866 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term70 m n p) = term71.
Proof. exact (MK_COMB (@lem191858 m p h1) (@lem191865 n p h1)). Qed.
Lemma lem191868 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem191840 n) (@lem191839 n)). Qed.
Lemma lem191869 : term71 = True.
Proof. exact (@lem191868 (NUMERAL 0)). Qed.
Lemma lem191870 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term70 m n p) = True.
Proof. exact (TRANS (@lem191866 m n p h1) (@lem191869)). Qed.
Lemma lem191871 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : True = (term70 m n p).
Proof. exact (SYM (@lem191870 m n p h1)). Qed.
Lemma lem191872 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term70 m n p.
Proof. exact (EQ_MP (@lem191871 m n p h1) (@lem0)). Qed.
Lemma lem191901 (a : nat) (b : nat) : term8 a b.
Proof. exact (@lem191829 a b (@lem191821 a b)). Qed.
Lemma lem191902 (m : nat) (n : nat) (p : nat) : term72 m n p.
Proof. exact (@lem191901 (Nat.div m p) (Nat.div n p)). Qed.
Lemma lem191903 (a : nat) : term73 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem191904 (a : nat) : (term73 a) = (term74 a).
Proof. exact (eq_refl (term73 a)). Qed.
Lemma lem191905 (a : nat) : term74 a.
Proof. exact (EQ_MP (@lem191904 a) (@lem191903 a)). Qed.
Lemma lem191906 (a : nat) (b : nat) : term75 a b.
Proof. exact (@lem191905 a b). Qed.
Lemma lem191907 (a : nat) (b : nat) : (term75 a b) = (term76 a b).
Proof. exact (eq_refl (term75 a b)). Qed.
Lemma lem191908 (a : nat) (b : nat) : term76 a b.
Proof. exact (EQ_MP (@lem191907 a b) (@lem191906 a b)). Qed.
Lemma lem191909 (a : nat) (b : nat) (n : nat) : term77 a b n.
Proof. exact (@lem191908 a b n). Qed.
Lemma lem191910 (a : nat) (n : nat) (b : nat) : (term77 a b n) = (term78 a n b).
Proof. exact (eq_refl (term77 a b n)). Qed.
Lemma lem191911 (a : nat) (n : nat) (b : nat) : term78 a n b.
Proof. exact (EQ_MP (@lem191910 a n b) (@lem191909 a b n)). Qed.
Lemma lem191912 (a : nat) (h1 : term65 a) : term65 a.
Proof. exact (h1). Qed.
Lemma lem191913 (n : nat) (b : nat) (a : nat) (h1 : term65 a) : (term79 n b a) = (term80 a n b).
Proof. exact (@lem191911 a n b (@lem191912 a h1)). Qed.
Lemma lem191921 (p : nat) : term81 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem191941 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term82 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem191942 (p : Prop) (q : Prop) (p' : Prop) : term83 p q p'.
Proof. exact (fun q' : Prop => @lem191941 p q p' q'). Qed.
Lemma lem191943 (p : Prop) (q : Prop) : term84 p q.
Proof. exact (fun p' : Prop => @lem191942 p q p'). Qed.
Lemma lem191944 (m : nat) (k : nat) (n : nat) (p : nat) : term85 m k n p.
Proof. exact (@lem191943 (term79 k m p) (term79 k n p)). Qed.
Lemma lem191945 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) : term86 m k n p p'.
Proof. exact (@lem191944 m k n p p'). Qed.
Lemma lem191946 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) : (term86 m k n p p') = (term87 m k n p p').
Proof. exact (eq_refl (term86 m k n p p')). Qed.
Lemma lem191947 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) : term87 m k n p p'.
Proof. exact (EQ_MP (@lem191946 m k n p p') (@lem191945 m k n p p')). Qed.
Lemma lem191948 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : term88 m k n p p' q'.
Proof. exact (@lem191947 m k n p p' q'). Qed.
Lemma lem191949 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : (term88 m k n p p' q') = (term89 m k n p p' q').
Proof. exact (eq_refl (term88 m k n p p' q')). Qed.
Lemma lem191950 (m : nat) (k : nat) (n : nat) (p : nat) (p' : Prop) (q' : Prop) : term89 m k n p p' q'.
Proof. exact (EQ_MP (@lem191949 m k n p p' q') (@lem191948 m k n p p' q')). Qed.
Lemma lem191952 (a : nat) (n : nat) (b : nat) : term78 a n b.
Proof. exact (fun h0 : term65 a => @lem191913 n b a h0). Qed.
Lemma lem191953 (p : nat) (k : nat) (m : nat) : term78 p k m.
Proof. exact (@lem191952 p k m). Qed.
Lemma lem191955 (p : nat) (h1 : term65 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem191921 p (@lem191835 p h1)). Qed.
Lemma lem191956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem191957 (p : nat) (h1 : term65 p) : (term65 p) = (~ False).
Proof. exact (MK_COMB (@lem191956) (@lem191955 p h1)). Qed.
Lemma lem191959 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem191960 (p : nat) (h1 : term65 p) : (term65 p) = True.
Proof. exact (TRANS (@lem191957 p h1) (@lem191959)). Qed.
Lemma lem191961 (p : nat) (h1 : term65 p) : True = (term65 p).
Proof. exact (SYM (@lem191960 p h1)). Qed.
Lemma lem191962 (p : nat) (h1 : term65 p) : term65 p.
Proof. exact (EQ_MP (@lem191961 p h1) (@lem0)). Qed.
Lemma lem191963 (k : nat) (m : nat) (p : nat) (h1 : term65 p) : (term79 k m p) = (term80 p k m).
Proof. exact (@lem191953 p k m (@lem191962 p h1)). Qed.
Lemma lem191964 (n : nat) (p : nat) (k : nat) (m : nat) (q' : Prop) : term90 n p k m q'.
Proof. exact (@lem191950 m k n p (term80 p k m) q'). Qed.
Lemma lem191965 (n : nat) (k : nat) (m : nat) (q' : Prop) (p : nat) (h1 : term65 p) : term91 n p k m q'.
Proof. exact (@lem191964 n p k m q' (@lem191963 k m p h1)). Qed.
Lemma lem191970 (a : nat) (n : nat) (b : nat) : term78 a n b.
Proof. exact (fun h0 : term65 a => @lem191913 n b a h0). Qed.
Lemma lem191971 (p : nat) (k : nat) (n : nat) : term78 p k n.
Proof. exact (@lem191970 p k n). Qed.
Lemma lem191973 (p : nat) (h1 : term65 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem191921 p (@lem191835 p h1)). Qed.
Lemma lem191974 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem191975 (p : nat) (h1 : term65 p) : (term65 p) = (~ False).
Proof. exact (MK_COMB (@lem191974) (@lem191973 p h1)). Qed.
Lemma lem191977 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem191978 (p : nat) (h1 : term65 p) : (term65 p) = True.
Proof. exact (TRANS (@lem191975 p h1) (@lem191977)). Qed.
Lemma lem191979 (p : nat) (h1 : term65 p) : True = (term65 p).
Proof. exact (SYM (@lem191978 p h1)). Qed.
Lemma lem191980 (p : nat) (h1 : term65 p) : term65 p.
Proof. exact (EQ_MP (@lem191979 p h1) (@lem0)). Qed.
Lemma lem191981 (k : nat) (n : nat) (p : nat) (h1 : term65 p) : (term79 k n p) = (term80 p k n).
Proof. exact (@lem191971 p k n (@lem191980 p h1)). Qed.
Lemma lem191982 (m : nat) (k : nat) (n : nat) (p : nat) (h1 : term65 p) : term92 m p k n.
Proof. exact (fun h0 : term80 p k m => @lem191981 k n p h1). Qed.
Lemma lem191983 (m : nat) (k : nat) (n : nat) (p : nat) (h1 : term65 p) : term93 m p k n.
Proof. exact (@lem191965 n k m (term80 p k n) p h1). Qed.
Lemma lem191984 (m : nat) (k : nat) (n : nat) (p : nat) (h1 : term65 p) : (term94 m k n p) = (term95 m p k n).
Proof. exact (@lem191983 m k n p h1 (@lem191982 m k n p h1)). Qed.
Lemma lem192008 (m : nat) (n : nat) (p : nat) (h1 : term65 p) : (term96 m n p) = (term97 m p n).
Proof. exact (fun_ext (fun k : nat => @lem191984 m k n p h1)). Qed.
Lemma lem192032 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192033 (m : nat) (n : nat) (p : nat) (h1 : term65 p) : (term98 m n p) = (term99 m p n).
Proof. exact (MK_COMB (@lem192032) (@lem192008 m n p h1)). Qed.
Lemma lem192061 (m : nat) (n : nat) (p : nat) (h1 : term65 p) : (term99 m p n) = (term98 m n p).
Proof. exact (SYM (@lem192033 m n p h1)). Qed.
Lemma lem192063 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem192064 (m : nat) (p : nat) (n : nat) : (term99 m p n) = (term100 m p n).
Proof. exact (@lem192063 (term99 m p n)). Qed.
Lemma lem192065 (m : nat) (p : nat) (n : nat) : (term100 m p n) = (term99 m p n).
Proof. exact (SYM (@lem192064 m p n)). Qed.
Lemma lem192066 (m : nat) (p : nat) (n : nat) (h1 : term101 m p n) : term101 m p n.
Proof. exact (h1). Qed.
Lemma lem192069 (m : nat) (p : nat) (n : nat) (h1 : term102 m p n) : term102 m p n.
Proof. exact (h1). Qed.
Lemma lem192070 (m : nat) (p : nat) (n : nat) : term103 m p n.
Proof. exact (fun h0 : term102 m p n => @lem192069 m p n h0). Qed.
Lemma lem192071 (m : nat) (p : nat) (n : nat) (h1 : term103 m p n) : term103 m p n.
Proof. exact (h1). Qed.
Lemma lem192072 (m : nat) (p : nat) (n : nat) (h1 : term102 m p n) : term102 m p n.
Proof. exact (h1). Qed.
Lemma lem192073 (m : nat) (p : nat) (n : nat) (h1 : term102 m p n) (h2 : term103 m p n) : term102 m p n.
Proof. exact (@lem192071 m p n h2 (@lem192072 m p n h1)). Qed.
Lemma lem192074 (m : nat) (p : nat) (n : nat) (h1 : term102 m p n) : term104 m p n.
Proof. exact (fun h0 : term103 m p n => @lem192073 m p n h1 h0). Qed.
Lemma lem192075 (m : nat) (p : nat) (n : nat) (h1 : term103 m p n) : term103 m p n.
Proof. exact (h1). Qed.
Lemma lem192076 (m : nat) (p : nat) (n : nat) (h1 : term102 m p n) (h2 : term103 m p n) : term102 m p n.
Proof. exact (@lem192074 m p n h1 (@lem192075 m p n h2)). Qed.
Lemma lem192077 (m : nat) (p : nat) (n : nat) (h1 : term103 m p n) : term103 m p n.
Proof. exact (fun h0 : term102 m p n => @lem192076 m p n h0 h1). Qed.
Lemma lem192078 (m : nat) (p : nat) (n : nat) : term105 m p n.
Proof. exact (fun h0 : term103 m p n => @lem192077 m p n h0). Qed.
Lemma lem192081 (m : nat) (p : nat) (n : nat) : term103 m p n.
Proof. exact (@lem192078 m p n (@lem192070 m p n)). Qed.
Lemma lem192107 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem192108 : term106 = term107.
Proof. exact (@lem192107 term108). Qed.
Lemma lem192125 (m : nat) (p : nat) (n : nat) : (term109 m p n) = (term109 m p n).
Proof. exact (eq_refl (term109 m p n)). Qed.
Lemma lem192126 (m : nat) (p : nat) (n : nat) : (term110 m p n) = (term111 m p n).
Proof. exact (MK_COMB (@lem192125 m p n) (@lem192108)). Qed.
Lemma lem192129 (p : nat) : (term112 p) = (term112 p).
Proof. exact (eq_refl (term112 p)). Qed.
Lemma lem192130 (m : nat) (p : nat) (n : nat) : (term113 m p n) = (term114 m p n).
Proof. exact (MK_COMB (@lem192129 p) (@lem192126 m p n)). Qed.
Lemma lem192133 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem192134 (m : nat) (p : nat) (n : nat) : (term102 m p n) = (term115 m p n).
Proof. exact (MK_COMB (@lem192133 m n) (@lem192130 m p n)). Qed.
Lemma lem192137 (p : nat) (n : nat) : (term116 p n) = (term117 p n).
Proof. exact (fun_ext (fun m : nat => @lem192134 m p n)). Qed.
Lemma lem192138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192139 (p : nat) (n : nat) : (term118 p n) = (term119 p n).
Proof. exact (MK_COMB (@lem192138) (@lem192137 p n)). Qed.
Lemma lem192144 (n : nat) : (term120 n) = (term121 n).
Proof. exact (fun_ext (fun p : nat => @lem192139 p n)). Qed.
Lemma lem192145 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192146 (n : nat) : (term122 n) = (term123 n).
Proof. exact (MK_COMB (@lem192145) (@lem192144 n)). Qed.
Lemma lem192151 : term124 = term125.
Proof. exact (fun_ext (fun n : nat => @lem192146 n)). Qed.
Lemma lem192152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192161 : term126 = term127.
Proof. exact (MK_COMB (@lem192152) (@lem192151)). Qed.
Lemma lem192170 (n : nat) (m : nat) (p : nat) : (term128 n m p) = (term128 n m p).
Proof. exact (eq_refl (term128 n m p)). Qed.
Lemma lem192171 (n : nat) (m : nat) : (term129 n m) = (term129 n m).
Proof. exact (fun_ext (fun p : nat => @lem192170 n m p)). Qed.
Lemma lem192172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192173 (n : nat) (m : nat) : (term130 n m) = (term130 n m).
Proof. exact (MK_COMB (@lem192172) (@lem192171 n m)). Qed.
Lemma lem192174 (m : nat) : (term131 m) = (term131 m).
Proof. exact (fun_ext (fun n : nat => @lem192173 n m)). Qed.
Lemma lem192175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192176 (m : nat) : (term132 m) = (term132 m).
Proof. exact (MK_COMB (@lem192175) (@lem192174 m)). Qed.
Lemma lem192177 : term133 = term133.
Proof. exact (fun_ext (fun m : nat => @lem192176 m)). Qed.
Lemma lem192178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192179 : term108 = term108.
Proof. exact (MK_COMB (@lem192178) (@lem192177)). Qed.
Lemma lem192180 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem192181 : term107 = term107.
Proof. exact (MK_COMB (@lem192180) (@lem192179)). Qed.
Lemma lem192186 (m : nat) (p : nat) (k : nat) (n : nat) : (term95 m p k n) = (term95 m p k n).
Proof. exact (eq_refl (term95 m p k n)). Qed.
Lemma lem192187 (m : nat) (p : nat) (n : nat) : (term97 m p n) = (term97 m p n).
Proof. exact (fun_ext (fun k : nat => @lem192186 m p k n)). Qed.
Lemma lem192188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192189 (m : nat) (p : nat) (n : nat) : (term99 m p n) = (term99 m p n).
Proof. exact (MK_COMB (@lem192188) (@lem192187 m p n)). Qed.
Lemma lem192190 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem192191 (m : nat) (p : nat) (n : nat) : (term101 m p n) = (term101 m p n).
Proof. exact (MK_COMB (@lem192190) (@lem192189 m p n)). Qed.
Lemma lem192192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem192193 (m : nat) (p : nat) (n : nat) : (term109 m p n) = (term109 m p n).
Proof. exact (MK_COMB (@lem192192) (@lem192191 m p n)). Qed.
Lemma lem192194 (m : nat) (p : nat) (n : nat) : (term111 m p n) = (term111 m p n).
Proof. exact (MK_COMB (@lem192193 m p n) (@lem192181)). Qed.
Lemma lem192199 (p : nat) : (term112 p) = (term112 p).
Proof. exact (eq_refl (term112 p)). Qed.
Lemma lem192200 (m : nat) (p : nat) (n : nat) : (term114 m p n) = (term114 m p n).
Proof. exact (MK_COMB (@lem192199 p) (@lem192194 m p n)). Qed.
Lemma lem192203 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem192204 (m : nat) (p : nat) (n : nat) : (term115 m p n) = (term115 m p n).
Proof. exact (MK_COMB (@lem192203 m n) (@lem192200 m p n)). Qed.
Lemma lem192205 (p : nat) (n : nat) : (term117 p n) = (term117 p n).
Proof. exact (fun_ext (fun m : nat => @lem192204 m p n)). Qed.
Lemma lem192206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192207 (p : nat) (n : nat) : (term119 p n) = (term119 p n).
Proof. exact (MK_COMB (@lem192206) (@lem192205 p n)). Qed.
Lemma lem192208 (n : nat) : (term121 n) = (term121 n).
Proof. exact (fun_ext (fun p : nat => @lem192207 p n)). Qed.
Lemma lem192209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192210 (n : nat) : (term123 n) = (term123 n).
Proof. exact (MK_COMB (@lem192209) (@lem192208 n)). Qed.
Lemma lem192211 : term125 = term125.
Proof. exact (fun_ext (fun n : nat => @lem192210 n)). Qed.
Lemma lem192212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192213 : term127 = term127.
Proof. exact (MK_COMB (@lem192212) (@lem192211)). Qed.
Lemma lem192270 : term126 = term127.
Proof. exact (TRANS (@lem192161) (@lem192213)). Qed.
Lemma lem192271 : term127 = term126.
Proof. exact (SYM (@lem192270)). Qed.
Lemma lem192274 (m : nat) (p : nat) (n : nat) (h1 : term101 m p n) : term101 m p n.
Proof. exact (h1). Qed.
Lemma lem192275 (h1 : term108) : term108.
Proof. exact (h1). Qed.
Lemma lem192281 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem192294 (m : nat) (p : nat) (k : nat) (n : nat) : (term134 m p k n) = (term135 m p k n).
Proof. exact (@lem17362 (term80 p k m) (term80 p k n)). Qed.
Lemma lem192295 (P : nat -> Prop) : (term136 P) = (term137 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem192296 (m : nat) (p : nat) (n : nat) : (term101 m p n) = (term138 m p n).
Proof. exact (@lem192295 (term97 m p n)). Qed.
Lemma lem192297 (m : nat) (p : nat) (k : nat) (n : nat) : (term139 m p n k) = (term95 m p k n).
Proof. exact (eq_refl (term139 m p n k)). Qed.
Lemma lem192298 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem192299 (m : nat) (p : nat) (k : nat) (n : nat) : (term140 m p n k) = (term134 m p k n).
Proof. exact (MK_COMB (@lem192298) (@lem192297 m p k n)). Qed.
Lemma lem192300 (m : nat) (p : nat) (k : nat) (n : nat) : (term140 m p n k) = (term135 m p k n).
Proof. exact (TRANS (@lem192299 m p k n) (@lem192294 m p k n)). Qed.
Lemma lem192301 (m : nat) (p : nat) (n : nat) : (term141 m p n) = (term142 m p n).
Proof. exact (fun_ext (fun k : nat => @lem192300 m p k n)). Qed.
Lemma lem192302 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem192303 (m : nat) (p : nat) (n : nat) : (term138 m p n) = (term143 m p n).
Proof. exact (MK_COMB (@lem192302) (@lem192301 m p n)). Qed.
Lemma lem192356 (m : nat) (p : nat) (n : nat) : (term101 m p n) = (term143 m p n).
Proof. exact (TRANS (@lem192296 m p n) (@lem192303 m p n)). Qed.
Lemma lem192357 (m : nat) (p : nat) (n : nat) (h1 : term101 m p n) : term143 m p n.
Proof. exact (EQ_MP (@lem192356 m p n) (@lem192274 m p n h1)). Qed.
Lemma lem192364 (m : nat) (n : nat) (p : nat) : (term144 m n p) = (term145 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem192365 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem192366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem192367 (m : nat) (n : nat) (p : nat) : (term146 m n p) = (term147 m n p).
Proof. exact (MK_COMB (@lem192366) (@lem192364 m n p)). Qed.
Lemma lem192368 (n : nat) (m : nat) (p : nat) : (term148 n m p) = (term149 n m p).
Proof. exact (MK_COMB (@lem192367 m n p) (@lem192365 m p)). Qed.
Lemma lem192369 (n : nat) (m : nat) (p : nat) : (term128 n m p) = (term148 n m p).
Proof. exact (@lem17265 (term150 m n p) (Peano.le m p)). Qed.
Lemma lem192370 (n : nat) (m : nat) (p : nat) : (term128 n m p) = (term149 n m p).
Proof. exact (TRANS (@lem192369 n m p) (@lem192368 n m p)). Qed.
Lemma lem192371 (n : nat) (m : nat) : (term129 n m) = (term151 n m).
Proof. exact (fun_ext (fun p : nat => @lem192370 n m p)). Qed.
Lemma lem192372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192373 (n : nat) (m : nat) : (term130 n m) = (term152 n m).
Proof. exact (MK_COMB (@lem192372) (@lem192371 n m)). Qed.
Lemma lem192374 (m : nat) : (term131 m) = (term153 m).
Proof. exact (fun_ext (fun n : nat => @lem192373 n m)). Qed.
Lemma lem192375 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192376 (m : nat) : (term132 m) = (term154 m).
Proof. exact (MK_COMB (@lem192375) (@lem192374 m)). Qed.
Lemma lem192377 : term133 = term155.
Proof. exact (fun_ext (fun m : nat => @lem192376 m)). Qed.
Lemma lem192378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192439 : term108 = term156.
Proof. exact (MK_COMB (@lem192378) (@lem192377)). Qed.
Lemma lem192440 (h1 : term108) : term156.
Proof. exact (EQ_MP (@lem192439) (@lem192275 h1)). Qed.
Lemma lem192447 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem192482 (n : nat) (m : nat) (p : nat) : (term149 n m p) = (term149 n m p).
Proof. exact (eq_refl (term149 n m p)). Qed.
Lemma lem192483 (n : nat) (m : nat) : (term151 n m) = (term151 n m).
Proof. exact (fun_ext (fun p : nat => @lem192482 n m p)). Qed.
Lemma lem192484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192485 (n : nat) (m : nat) : (term152 n m) = (term152 n m).
Proof. exact (MK_COMB (@lem192484) (@lem192483 n m)). Qed.
Lemma lem192486 (m : nat) : (term153 m) = (term153 m).
Proof. exact (fun_ext (fun n : nat => @lem192485 n m)). Qed.
Lemma lem192487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192488 (m : nat) : (term154 m) = (term154 m).
Proof. exact (MK_COMB (@lem192487) (@lem192486 m)). Qed.
Lemma lem192489 : term155 = term155.
Proof. exact (fun_ext (fun m : nat => @lem192488 m)). Qed.
Lemma lem192490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192491 : term156 = term156.
Proof. exact (MK_COMB (@lem192490) (@lem192489)). Qed.
Lemma lem192492 (h1 : term108) : term156.
Proof. exact (EQ_MP (@lem192491) (@lem192440 h1)). Qed.
Lemma lem192516 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term135 m p k n) : term135 m p k n.
Proof. exact (h1). Qed.
Lemma lem192522 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem192540 (n : nat) (m : nat) (p : nat) : (term149 n m p) = (term149 n m p).
Proof. exact (eq_refl (term149 n m p)). Qed.
Lemma lem192541 (n : nat) (m : nat) : (term151 n m) = (term151 n m).
Proof. exact (fun_ext (fun p : nat => @lem192540 n m p)). Qed.
Lemma lem192542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192543 (n : nat) (m : nat) : (term152 n m) = (term152 n m).
Proof. exact (MK_COMB (@lem192542) (@lem192541 n m)). Qed.
Lemma lem192544 (m : nat) : (term153 m) = (term153 m).
Proof. exact (fun_ext (fun n : nat => @lem192543 n m)). Qed.
Lemma lem192545 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192546 (m : nat) : (term154 m) = (term154 m).
Proof. exact (MK_COMB (@lem192545) (@lem192544 m)). Qed.
Lemma lem192547 : term155 = term155.
Proof. exact (fun_ext (fun m : nat => @lem192546 m)). Qed.
Lemma lem192548 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem192550 : term156 = term156.
Proof. exact (MK_COMB (@lem192548) (@lem192547)). Qed.
Lemma lem192551 (h1 : term108) : term156.
Proof. exact (EQ_MP (@lem192550) (@lem192492 h1)). Qed.
Lemma lem192560 (_3886 : nat) (h1 : term108) : term157 _3886.
Proof. exact (@lem192551 h1 _3886). Qed.
Lemma lem192561 (_3886 : nat) : (term157 _3886) = (term154 _3886).
Proof. exact (eq_refl (term157 _3886)). Qed.
Lemma lem192562 (_3886 : nat) (h1 : term108) : term154 _3886.
Proof. exact (EQ_MP (@lem192561 _3886) (@lem192560 _3886 h1)). Qed.
Lemma lem192563 (_3886 : nat) (_3887 : nat) (h1 : term108) : term158 _3886 _3887.
Proof. exact (@lem192562 _3886 h1 _3887). Qed.
Lemma lem192564 (_3887 : nat) (_3886 : nat) : (term158 _3886 _3887) = (term152 _3887 _3886).
Proof. exact (eq_refl (term158 _3886 _3887)). Qed.
Lemma lem192565 (_3887 : nat) (_3886 : nat) (h1 : term108) : term152 _3887 _3886.
Proof. exact (EQ_MP (@lem192564 _3887 _3886) (@lem192563 _3886 _3887 h1)). Qed.
Lemma lem192566 (_3887 : nat) (_3886 : nat) (_3888 : nat) (h1 : term108) : term159 _3887 _3886 _3888.
Proof. exact (@lem192565 _3887 _3886 h1 _3888). Qed.
Lemma lem192567 (_3887 : nat) (_3886 : nat) (_3888 : nat) : (term159 _3887 _3886 _3888) = (term149 _3887 _3886 _3888).
Proof. exact (eq_refl (term159 _3887 _3886 _3888)). Qed.
Lemma lem192568 (_3887 : nat) (_3886 : nat) (_3888 : nat) (h1 : term108) : term149 _3887 _3886 _3888.
Proof. exact (EQ_MP (@lem192567 _3887 _3886 _3888) (@lem192566 _3887 _3886 _3888 h1)). Qed.
Lemma lem192570 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem192583 (_3887 : nat) (_3886 : nat) (_3888 : nat) : (term149 _3887 _3886 _3888) = (term160 _3887 _3886 _3888).
Proof. exact (@lem191406 (term36 _3886 _3887) (term36 _3887 _3888) (Peano.le _3886 _3888)). Qed.
Lemma lem192584 (_3887 : nat) (_3886 : nat) (_3888 : nat) (h1 : term108) : term160 _3887 _3886 _3888.
Proof. exact (EQ_MP (@lem192583 _3887 _3886 _3888) (@lem192568 _3887 _3886 _3888 h1)). Qed.
Lemma lem192588 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term135 m p k n) : term161 p k n.
Proof. exact (proj2 (@lem192516 m p k n h1)). Qed.
Lemma lem192634 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term135 m p k n) : term80 p k m.
Proof. exact (proj1 (@lem192516 m p k n h1)). Qed.
Lemma lem192635 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term135 m p k n) : term162 p k m.
Proof. exact (fun h0 : term161 p k m => @lem192634 m p k n h1). Qed.
Lemma lem192637 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem192638 (p : nat) (k : nat) (m : nat) : (term162 p k m) = (term80 p k m).
Proof. exact (@lem192637 (term80 p k m)). Qed.
Lemma lem192639 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term135 m p k n) : term80 p k m.
Proof. exact (EQ_MP (@lem192638 p k m) (@lem192635 m p k n h1)). Qed.
Lemma lem192641 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem192642 (m : nat) (n : nat) (h1 : Peano.le m n) : term56 m n.
Proof. exact (fun h0 : term36 m n => @lem192641 m n h1). Qed.
Lemma lem192644 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem192645 (m : nat) (n : nat) : (term56 m n) = (Peano.le m n).
Proof. exact (@lem192644 (Peano.le m n)). Qed.
Lemma lem192646 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem192645 m n) (@lem192642 m n h1)). Qed.
Lemma lem192662 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem192663 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term163 _3887 _3886 _3888) = (term164 _3886 _3887 _3888).
Proof. exact (@lem192662 (Peano.le _3886 _3888) (term36 _3887 _3888)). Qed.
Lemma lem192669 (_3886 : nat) (_3887 : nat) : (term165 _3886 _3887) = (term165 _3886 _3887).
Proof. exact (eq_refl (term165 _3886 _3887)). Qed.
Lemma lem192670 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term160 _3887 _3886 _3888) = (term166 _3886 _3887 _3888).
Proof. exact (MK_COMB (@lem192669 _3886 _3887) (@lem192663 _3886 _3887 _3888)). Qed.
Lemma lem192674 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem192675 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term166 _3886 _3887 _3888) = (term167 _3886 _3887 _3888).
Proof. exact (@lem192674 (Peano.le _3886 _3888) (term36 _3886 _3887) (term36 _3887 _3888)). Qed.
Lemma lem192691 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term160 _3887 _3886 _3888) = (term167 _3886 _3887 _3888).
Proof. exact (TRANS (@lem192670 _3886 _3887 _3888) (@lem192675 _3886 _3887 _3888)). Qed.
Lemma lem192692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem192693 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term168 _3887 _3886 _3888) = (term169 _3886 _3887 _3888).
Proof. exact (MK_COMB (@lem192692) (@lem192691 _3886 _3887 _3888)). Qed.
Lemma lem192709 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term167 _3886 _3887 _3888) = (term167 _3886 _3887 _3888).
Proof. exact (eq_refl (term167 _3886 _3887 _3888)). Qed.
Lemma lem192710 (_3886 : nat) (_3887 : nat) (_3888 : nat) : ((term160 _3887 _3886 _3888) = (term167 _3886 _3887 _3888)) = ((term167 _3886 _3887 _3888) = (term167 _3886 _3887 _3888)).
Proof. exact (MK_COMB (@lem192693 _3886 _3887 _3888) (@lem192709 _3886 _3887 _3888)). Qed.
Lemma lem192712 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem192713 (x : Prop) : (x = x) = True.
Proof. exact (@lem192712 Prop x). Qed.
Lemma lem192714 (_3886 : nat) (_3887 : nat) (_3888 : nat) : ((term167 _3886 _3887 _3888) = (term167 _3886 _3887 _3888)) = True.
Proof. exact (@lem192713 (term167 _3886 _3887 _3888)). Qed.
Lemma lem192715 (_3886 : nat) (_3887 : nat) (_3888 : nat) : ((term160 _3887 _3886 _3888) = (term167 _3886 _3887 _3888)) = True.
Proof. exact (TRANS (@lem192710 _3886 _3887 _3888) (@lem192714 _3886 _3887 _3888)). Qed.
Lemma lem192716 (_3886 : nat) (_3887 : nat) (_3888 : nat) : True = ((term160 _3887 _3886 _3888) = (term167 _3886 _3887 _3888)).
Proof. exact (SYM (@lem192715 _3886 _3887 _3888)). Qed.
Lemma lem192717 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term160 _3887 _3886 _3888) = (term167 _3886 _3887 _3888).
Proof. exact (EQ_MP (@lem192716 _3886 _3887 _3888) (@lem0)). Qed.
Lemma lem192718 (_3886 : nat) (_3887 : nat) (_3888 : nat) (h1 : term108) : term167 _3886 _3887 _3888.
Proof. exact (EQ_MP (@lem192717 _3886 _3887 _3888) (@lem192584 _3887 _3886 _3888 h1)). Qed.
Lemma lem192720 (b : Prop) (a : Prop) : (a \/ b) = (term49 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem192721 (_3887 : nat) (_3886 : nat) (_3888 : nat) : (term167 _3886 _3887 _3888) = (term170 _3887 _3886 _3888).
Proof. exact (@lem192720 (term145 _3886 _3887 _3888) (Peano.le _3886 _3888)). Qed.
Lemma lem192723 (a : Prop) (b : Prop) : (term171 a b) = (term172 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem192724 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term173 _3886 _3887 _3888) = (term174 _3886 _3887 _3888).
Proof. exact (@lem192723 (term36 _3886 _3887) (term36 _3887 _3888)). Qed.
Lemma lem192726 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem192727 (_3886 : nat) (_3887 : nat) : (term52 _3886 _3887) = (Peano.le _3886 _3887).
Proof. exact (@lem192726 (Peano.le _3886 _3887)). Qed.
Lemma lem192728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem192729 (_3886 : nat) (_3887 : nat) : (term175 _3886 _3887) = (term176 _3886 _3887).
Proof. exact (MK_COMB (@lem192728) (@lem192727 _3886 _3887)). Qed.
Lemma lem192731 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem192732 (_3887 : nat) (_3888 : nat) : (term52 _3887 _3888) = (Peano.le _3887 _3888).
Proof. exact (@lem192731 (Peano.le _3887 _3888)). Qed.
Lemma lem192733 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term174 _3886 _3887 _3888) = (term150 _3886 _3887 _3888).
Proof. exact (MK_COMB (@lem192729 _3886 _3887) (@lem192732 _3887 _3888)). Qed.
Lemma lem192734 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term173 _3886 _3887 _3888) = (term150 _3886 _3887 _3888).
Proof. exact (TRANS (@lem192724 _3886 _3887 _3888) (@lem192733 _3886 _3887 _3888)). Qed.
Lemma lem192735 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem192736 (_3886 : nat) (_3887 : nat) (_3888 : nat) : (term177 _3886 _3887 _3888) = (term178 _3886 _3887 _3888).
Proof. exact (MK_COMB (@lem192735) (@lem192734 _3886 _3887 _3888)). Qed.
Lemma lem192737 (_3886 : nat) (_3888 : nat) : (Peano.le _3886 _3888) = (Peano.le _3886 _3888).
Proof. exact (eq_refl (Peano.le _3886 _3888)). Qed.
Lemma lem192738 (_3887 : nat) (_3886 : nat) (_3888 : nat) : (term170 _3887 _3886 _3888) = (term128 _3887 _3886 _3888).
Proof. exact (MK_COMB (@lem192736 _3886 _3887 _3888) (@lem192737 _3886 _3888)). Qed.
Lemma lem192739 (_3887 : nat) (_3886 : nat) (_3888 : nat) : (term167 _3886 _3887 _3888) = (term128 _3887 _3886 _3888).
Proof. exact (TRANS (@lem192721 _3887 _3886 _3888) (@lem192738 _3887 _3886 _3888)). Qed.
Lemma lem192741 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term135 m p k n) (h2 : Peano.le m n) : term179 p k m n.
Proof. exact (conj (@lem192639 m p k n h1) (@lem192646 m n h2)). Qed.
Lemma lem192743 (_3887 : nat) (_3886 : nat) (_3888 : nat) (h1 : term108) : term128 _3887 _3886 _3888.
Proof. exact (EQ_MP (@lem192739 _3887 _3886 _3888) (@lem192718 _3886 _3887 _3888 h1)). Qed.
Lemma lem192744 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term108) : term180 m p k n.
Proof. exact (@lem192743 m (Nat.mul p k) n h1). Qed.
Lemma lem192747 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : term80 p k n.
Proof. exact (@lem192744 m p k n h1 (@lem192741 p k m n h2 h3)). Qed.
Lemma lem192748 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : term162 p k n.
Proof. exact (fun h0 : term161 p k n => @lem192747 p k m n h1 h2 h3). Qed.
Lemma lem192750 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem192751 (p : nat) (k : nat) (n : nat) : (term162 p k n) = (term80 p k n).
Proof. exact (@lem192750 (term80 p k n)). Qed.
Lemma lem192752 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : term80 p k n.
Proof. exact (EQ_MP (@lem192751 p k n) (@lem192748 p k m n h1 h2 h3)). Qed.
Lemma lem192755 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem192757 (p : nat) (k : nat) (n : nat) : (term161 p k n) = (term181 p k n).
Proof. exact (@lem192755 (term80 p k n)). Qed.
Lemma lem192760 (m : nat) (p : nat) (k : nat) (n : nat) (h1 : term135 m p k n) : term181 p k n.
Proof. exact (EQ_MP (@lem192757 p k n) (@lem192588 m p k n h1)). Qed.
Lemma lem192763 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : False.
Proof. exact (@lem192760 m p k n h2 (@lem192752 p k m n h1 h2 h3)). Qed.
Lemma lem192764 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : term58.
Proof. exact (fun h0 : ~ False => @lem192763 p k m n h1 h2 h3). Qed.
Lemma lem192766 (p : Prop) : (term45 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem192767 : term58 = False.
Proof. exact (@lem192766 False). Qed.
Lemma lem192768 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192767) (@lem192764 p k m n h1 h2 h3)). Qed.
Lemma lem192769 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem192768 p k m n h1 h2 h3) (fun h4 : False => @lem192570 m n h3)). Qed.
Lemma lem192770 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192769 p k m n h1 h2 h3) (@lem192570 m n h3)). Qed.
Lemma lem192771 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem192770 p k m n h1 h2 h3) (fun h4 : False => @lem192522 m n h3)). Qed.
Lemma lem192772 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192771 p k m n h1 h2 h3) (@lem192522 m n h3)). Qed.
Lemma lem192773 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem192772 p k m n h1 h2 h3) (fun h4 : False => @lem192522 m n h3)). Qed.
Lemma lem192774 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192773 p k m n h1 h2 h3) (@lem192522 m n h3)). Qed.
Lemma lem192775 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : (term135 m p k n) = False.
Proof. exact (prop_ext (fun h4 : term135 m p k n => @lem192774 p k m n h1 h2 h3) (fun h4 : False => @lem192516 m p k n h2)). Qed.
Lemma lem192776 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192775 p k m n h1 h2 h3) (@lem192516 m p k n h2)). Qed.
Lemma lem192777 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem192776 p k m n h1 h2 h3) (fun h4 : False => @lem192447 m n h3)). Qed.
Lemma lem192778 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term135 m p k n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192777 p k m n h1 h2 h3) (@lem192447 m n h3)). Qed.
Lemma lem192779 (p : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term101 m p n) (h3 : Peano.le m n) : False.
Proof. exact (ex_elim (@lem192357 m p n h2) (fun k : nat => fun h0 : term142 m p n k => @lem192778 p k m n h1 h0 h3)). Qed.
Lemma lem192780 (p : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term101 m p n) (h3 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem192779 p m n h1 h2 h3) (fun h4 : False => @lem192281 m n h3)). Qed.
Lemma lem192781 (p : nat) (m : nat) (n : nat) (h1 : term108) (h2 : term101 m p n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192780 p m n h1 h2 h3) (@lem192281 m n h3)). Qed.
Lemma lem192782 (p : nat) (m : nat) (n : nat) (h1 : term101 m p n) (h2 : Peano.le m n) : term106.
Proof. exact (fun h0 : term108 => @lem192781 p m n h0 h1 h2). Qed.
Lemma lem192783 : term106 = term107.
Proof. exact (@lem69 term108). Qed.
Lemma lem192784 (p : nat) (m : nat) (n : nat) (h1 : term101 m p n) (h2 : Peano.le m n) : term107.
Proof. exact (EQ_MP (@lem192783) (@lem192782 p m n h1 h2)). Qed.
Lemma lem192785 (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term111 m p n.
Proof. exact (fun h0 : term101 m p n => @lem192784 p m n h0 h1). Qed.
Lemma lem192786 (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term114 m p n.
Proof. exact (fun h0 : term65 p => @lem192785 p m n h1). Qed.
Lemma lem192787 (m : nat) (p : nat) (n : nat) : term115 m p n.
Proof. exact (fun h0 : Peano.le m n => @lem192786 p m n h0). Qed.
Lemma lem192792 (p : nat) (n : nat) : term119 p n.
Proof. exact (fun m : nat => @lem192787 m p n). Qed.
Lemma lem192797 (n : nat) : term123 n.
Proof. exact (fun p : nat => @lem192792 p n). Qed.
Lemma lem192802 : term127.
Proof. exact (fun n : nat => @lem192797 n). Qed.
Lemma lem192803 : term126.
Proof. exact (EQ_MP (@lem192271) (@lem192802)). Qed.
Lemma lem192804 (n : nat) : term182 n.
Proof. exact (@lem192803 n). Qed.
Lemma lem192805 (n : nat) : (term182 n) = (term122 n).
Proof. exact (eq_refl (term182 n)). Qed.
Lemma lem192806 (n : nat) : term122 n.
Proof. exact (EQ_MP (@lem192805 n) (@lem192804 n)). Qed.
Lemma lem192807 (n : nat) (p : nat) : term183 n p.
Proof. exact (@lem192806 n p). Qed.
Lemma lem192808 (p : nat) (n : nat) : (term183 n p) = (term118 p n).
Proof. exact (eq_refl (term183 n p)). Qed.
Lemma lem192809 (p : nat) (n : nat) : term118 p n.
Proof. exact (EQ_MP (@lem192808 p n) (@lem192807 n p)). Qed.
Lemma lem192810 (p : nat) (n : nat) (m : nat) : term184 p n m.
Proof. exact (@lem192809 p n m). Qed.
Lemma lem192811 (m : nat) (p : nat) (n : nat) : (term184 p n m) = (term102 m p n).
Proof. exact (eq_refl (term184 p n m)). Qed.
Lemma lem192812 (m : nat) (p : nat) (n : nat) : term102 m p n.
Proof. exact (EQ_MP (@lem192811 m p n) (@lem192810 p n m)). Qed.
Lemma lem192814 (m : nat) (p : nat) (n : nat) : term102 m p n.
Proof. exact (@lem192081 m p n (@lem192812 m p n)). Qed.
Lemma lem192815 (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term113 m p n.
Proof. exact (@lem192814 m p n (@lem191836 m n h1)). Qed.
Lemma lem192816 (p : nat) (m : nat) (n : nat) (h1 : term65 p) (h2 : Peano.le m n) : term110 m p n.
Proof. exact (@lem192815 p m n h2 (@lem191835 p h1)). Qed.
Lemma lem192817 (p : nat) (m : nat) (n : nat) (h1 : term101 m p n) (h2 : term65 p) (h3 : Peano.le m n) : term106.
Proof. exact (@lem192816 p m n h2 h3 (@lem192066 m p n h1)). Qed.
Lemma lem192818 (p : nat) (m : nat) (n : nat) (h1 : term101 m p n) (h2 : term65 p) (h3 : Peano.le m n) : False.
Proof. exact (@lem192817 p m n h1 h2 h3 (@lem93743)). Qed.
Lemma lem192819 (p : nat) (m : nat) (n : nat) (h1 : term101 m p n) (h2 : term65 p) (h3 : Peano.le m n) : (term101 m p n) = False.
Proof. exact (prop_ext (fun h4 : term101 m p n => @lem192818 p m n h1 h2 h3) (fun h4 : False => @lem192066 m p n h1)). Qed.
Lemma lem192820 (p : nat) (m : nat) (n : nat) (h1 : term101 m p n) (h2 : term65 p) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem192819 p m n h1 h2 h3) (@lem192066 m p n h1)). Qed.
Lemma lem192821 (p : nat) (m : nat) (n : nat) (h1 : term65 p) (h2 : Peano.le m n) : term100 m p n.
Proof. exact (fun h0 : term101 m p n => @lem192820 p m n h0 h1 h2). Qed.
Lemma lem192822 (p : nat) (m : nat) (n : nat) (h1 : term65 p) (h2 : Peano.le m n) : term99 m p n.
Proof. exact (EQ_MP (@lem192065 m p n) (@lem192821 p m n h1 h2)). Qed.
Lemma lem192823 (p : nat) (m : nat) (n : nat) (h1 : term65 p) (h2 : Peano.le m n) : term98 m n p.
Proof. exact (EQ_MP (@lem192061 m n p h1) (@lem192822 p m n h1 h2)). Qed.
Lemma lem192825 (p : nat) (m : nat) (n : nat) (h1 : term65 p) (h2 : Peano.le m n) : term70 m n p.
Proof. exact (@lem191902 m n p (@lem192823 p m n h1 h2)). Qed.
Lemma lem192826 (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term70 m n p.
Proof. exact (or_elim (@lem191833 p) (fun h0 : p = (NUMERAL 0) => @lem191872 m n p h0) (fun h0 : term65 p => @lem192825 p m n h0 h1)). Qed.
Lemma lem192827 (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = (term70 m n p).
Proof. exact (prop_ext (fun h2 : Peano.le m n => @lem192826 p m n h1) (fun h2 : term70 m n p => @lem191836 m n h1)). Qed.
Lemma lem192828 (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term70 m n p.
Proof. exact (EQ_MP (@lem192827 p m n h1) (@lem191836 m n h1)). Qed.
Lemma lem192829 (m : nat) (n : nat) (p : nat) : term185 m n p.
Proof. exact (fun h0 : Peano.le m n => @lem192828 p m n h0). Qed.
Lemma lem192834 (m : nat) (n : nat) : term186 m n.
Proof. exact (fun p : nat => @lem192829 m n p). Qed.
Lemma lem192839 (m : nat) : term187 m.
Proof. exact (fun n : nat => @lem192834 m n). Qed.
Lemma lem192844 : term188.
Proof. exact (fun m : nat => @lem192839 m). Qed.
