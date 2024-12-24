Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_NSUM_MOD_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_NUMSEG_spec.
Require Import MOD_NSUM_MOD_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm18392_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7053450 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7053451 : term1 = term2.
Proof. exact (@lem7053450 term1). Qed.
Lemma lem7053452 : term2 = term1.
Proof. exact (SYM (@lem7053451)). Qed.
Lemma lem7053453 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem7053454 : term4.
Proof. exact (@lem7053438 nat). Qed.
Lemma lem7053457 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem7053458 {A : Type'} : term6 A.
Proof. exact (fun h0 : term5 A => @lem7053457 A h0). Qed.
Lemma lem7053459 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7053460 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem7053461 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem7053459 A h2 (@lem7053460 A h1)). Qed.
Lemma lem7053462 {A : Type'} (h1 : term5 A) : term7 A.
Proof. exact (fun h0 : term6 A => @lem7053461 A h1 h0). Qed.
Lemma lem7053463 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7053464 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem7053462 A h1 (@lem7053463 A h2)). Qed.
Lemma lem7053465 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (fun h0 : term5 A => @lem7053464 A h0 h1). Qed.
Lemma lem7053466 {A : Type'} : term8 A.
Proof. exact (fun h0 : term6 A => @lem7053465 A h0). Qed.
Lemma lem7053469 {A : Type'} : term6 A.
Proof. exact (@lem7053466 A (@lem7053458 A)). Qed.
Lemma lem7053470 {A : Type'} : term6 A.
Proof. exact (@lem7053469 A). Qed.
Lemma lem7053516 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7053517 : term9 = term10.
Proof. exact (@lem7053516 term4). Qed.
Lemma lem7053532 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem7053533 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (MK_COMB (@lem7053532 A) (@lem7053517)). Qed.
Lemma lem7053536 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem7053537 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem7053536) (@lem7053533 A)). Qed.
Lemma lem7053540 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem7053545 {A : Type'} : (term5 A) = (term18 A).
Proof. exact (MK_COMB (@lem7053540) (@lem7053537 A)). Qed.
Lemma lem7053546 (_94156 : type1000) (h1 : _94156 = term19) : _94156 = term19.
Proof. exact (h1). Qed.
Lemma lem7053547 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7053548 (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (_94156 f) = (term20 f).
Proof. exact (MK_COMB (@lem7053546 _94156 h1) (@lem7053547 f)). Qed.
Lemma lem7053549 (f : nat -> nat) : (term20 f) = (term21 f).
Proof. exact (eq_refl (term20 f)). Qed.
Lemma lem7053550 (_94156 : type1000) (f : nat -> nat) : (term22 _94156 f) = (term22 _94156 f).
Proof. exact (eq_refl (term22 _94156 f)). Qed.
Lemma lem7053551 (_94156 : type1000) (f : nat -> nat) : ((_94156 f) = (term20 f)) = ((_94156 f) = (term21 f)).
Proof. exact (MK_COMB (@lem7053550 _94156 f) (@lem7053549 f)). Qed.
Lemma lem7053552 (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (_94156 f) = (term21 f).
Proof. exact (EQ_MP (@lem7053551 _94156 f) (@lem7053548 f _94156 h1)). Qed.
Lemma lem7053553 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053554 (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (_94156 f n) = (term23 f n).
Proof. exact (MK_COMB (@lem7053552 f _94156 h1) (@lem7053553 n)). Qed.
Lemma lem7053555 (f : nat -> nat) (n : nat) : (term23 f n) = (term24 f n).
Proof. exact (eq_refl (term23 f n)). Qed.
Lemma lem7053556 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term25 _94156 f n) = (term25 _94156 f n).
Proof. exact (eq_refl (term25 _94156 f n)). Qed.
Lemma lem7053557 (_94156 : type1000) (f : nat -> nat) (n : nat) : ((_94156 f n) = (term23 f n)) = ((_94156 f n) = (term24 f n)).
Proof. exact (MK_COMB (@lem7053556 _94156 f n) (@lem7053555 f n)). Qed.
Lemma lem7053558 (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (_94156 f n) = (term24 f n).
Proof. exact (EQ_MP (@lem7053557 _94156 f n) (@lem7053554 f n _94156 h1)). Qed.
Lemma lem7053560 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053562 (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term24 f n) = (_94156 f n).
Proof. exact (SYM (@lem7053558 f n _94156 h1)). Qed.
Lemma lem7053565 (s : nat -> Prop) : (@nsum nat s) = (@nsum nat s).
Proof. exact (eq_refl (@nsum nat s)). Qed.
Lemma lem7053566 (s : nat -> Prop) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term26 s f n) = (term27 s _94156 f n).
Proof. exact (MK_COMB (@lem7053565 s) (@lem7053562 f n _94156 h1)). Qed.
Lemma lem7053567 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7053568 (s : nat -> Prop) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term28 s f n) = (term29 s _94156 f n).
Proof. exact (MK_COMB (@lem7053567) (@lem7053566 s f n _94156 h1)). Qed.
Lemma lem7053569 (s : nat -> Prop) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term30 s f n) = (term31 s _94156 f n).
Proof. exact (MK_COMB (@lem7053568 s f n _94156 h1) (@lem7053560 n)). Qed.
Lemma lem7053580 (s : nat -> Prop) (f : nat -> nat) (n : nat) : (term32 s f n) = (term32 s f n).
Proof. exact (eq_refl (term32 s f n)). Qed.
Lemma lem7053581 (s : nat -> Prop) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : ((term33 s f n) = (term30 s f n)) = ((term33 s f n) = (term31 s _94156 f n)).
Proof. exact (MK_COMB (@lem7053580 s f n) (@lem7053569 s f n _94156 h1)). Qed.
Lemma lem7053586 (s : nat -> Prop) : (term34 s) = (term34 s).
Proof. exact (eq_refl (term34 s)). Qed.
Lemma lem7053587 (s : nat -> Prop) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term35 s f n) = (term36 s _94156 f n).
Proof. exact (MK_COMB (@lem7053586 s) (@lem7053581 s f n _94156 h1)). Qed.
Lemma lem7053588 (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term37 f n) = (term38 _94156 f n).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7053587 s f n _94156 h1)). Qed.
Lemma lem7053589 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7053590 (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term39 f n) = (term40 _94156 f n).
Proof. exact (MK_COMB (@lem7053589) (@lem7053588 f n _94156 h1)). Qed.
Lemma lem7053591 (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term41 f) = (term42 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7053590 f n _94156 h1)). Qed.
Lemma lem7053592 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053593 (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term43 f) = (term44 _94156 f).
Proof. exact (MK_COMB (@lem7053592) (@lem7053591 f _94156 h1)). Qed.
Lemma lem7053594 (_94156 : type1000) (h1 : _94156 = term19) : term45 = (term46 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053593 f _94156 h1)). Qed.
Lemma lem7053595 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7053596 (_94156 : type1000) (h1 : _94156 = term19) : term4 = (term47 _94156).
Proof. exact (MK_COMB (@lem7053595) (@lem7053594 _94156 h1)). Qed.
Lemma lem7053597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7053598 (_94156 : type1000) (h1 : _94156 = term19) : term10 = (term48 _94156).
Proof. exact (MK_COMB (@lem7053597) (@lem7053596 _94156 h1)). Qed.
Lemma lem7053599 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053608 {A : Type'} (f : A -> nat) (i : A) (n : nat) : (term49 A f i n) = (term49 A f i n).
Proof. exact (eq_refl (term49 A f i n)). Qed.
Lemma lem7053609 {A : Type'} (f : A -> nat) (n : nat) : (term50 A f n) = (term50 A f n).
Proof. exact (fun_ext (fun i : A => @lem7053608 A f i n)). Qed.
Lemma lem7053612 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@nsum A s).
Proof. exact (eq_refl (@nsum A s)). Qed.
Lemma lem7053613 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term51 A s f n) = (term51 A s f n).
Proof. exact (MK_COMB (@lem7053612 A s) (@lem7053609 A f n)). Qed.
Lemma lem7053614 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7053615 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term52 A s f n) = (term52 A s f n).
Proof. exact (MK_COMB (@lem7053614) (@lem7053613 A s f n)). Qed.
Lemma lem7053616 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term53 A s f n) = (term53 A s f n).
Proof. exact (MK_COMB (@lem7053615 A s f n) (@lem7053599 n)). Qed.
Lemma lem7053627 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term54 A s f n) = (term54 A s f n).
Proof. exact (eq_refl (term54 A s f n)). Qed.
Lemma lem7053628 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : ((term55 A s f n) = (term53 A s f n)) = ((term55 A s f n) = (term53 A s f n)).
Proof. exact (MK_COMB (@lem7053627 A s f n) (@lem7053616 A s f n)). Qed.
Lemma lem7053633 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem7053634 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term57 A s f n) = (term57 A s f n).
Proof. exact (MK_COMB (@lem7053633 A s) (@lem7053628 A s f n)). Qed.
Lemma lem7053635 {A : Type'} (f : A -> nat) (n : nat) : (term58 A f n) = (term58 A f n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7053634 A s f n)). Qed.
Lemma lem7053636 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7053637 {A : Type'} (f : A -> nat) (n : nat) : (term59 A f n) = (term59 A f n).
Proof. exact (MK_COMB (@lem7053636 A) (@lem7053635 A f n)). Qed.
Lemma lem7053638 {A : Type'} (f : A -> nat) : (term60 A f) = (term60 A f).
Proof. exact (fun_ext (fun n : nat => @lem7053637 A f n)). Qed.
Lemma lem7053639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053640 {A : Type'} (f : A -> nat) : (term61 A f) = (term61 A f).
Proof. exact (MK_COMB (@lem7053639) (@lem7053638 A f)). Qed.
Lemma lem7053641 {A : Type'} : (term62 A) = (term62 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7053640 A f)). Qed.
Lemma lem7053642 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7053643 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (MK_COMB (@lem7053642 A) (@lem7053641 A)). Qed.
Lemma lem7053644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053645 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7053644) (@lem7053643 A)). Qed.
Lemma lem7053646 {A : Type'} (_94156 : type1000) (h1 : _94156 = term19) : (term13 A) = (term64 A _94156).
Proof. exact (MK_COMB (@lem7053645 A) (@lem7053598 _94156 h1)). Qed.
Lemma lem7053653 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem7053654 (m : nat) : (term66 m) = (term66 m).
Proof. exact (fun_ext (fun n : nat => @lem7053653 m n)). Qed.
Lemma lem7053655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053656 (m : nat) : (term67 m) = (term67 m).
Proof. exact (MK_COMB (@lem7053655) (@lem7053654 m)). Qed.
Lemma lem7053657 : term68 = term68.
Proof. exact (fun_ext (fun m : nat => @lem7053656 m)). Qed.
Lemma lem7053658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053659 : term69 = term69.
Proof. exact (MK_COMB (@lem7053658) (@lem7053657)). Qed.
Lemma lem7053660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053661 : term14 = term14.
Proof. exact (MK_COMB (@lem7053660) (@lem7053659)). Qed.
Lemma lem7053662 {A : Type'} (_94156 : type1000) (h1 : _94156 = term19) : (term16 A) = (term70 A _94156).
Proof. exact (MK_COMB (@lem7053661) (@lem7053646 A _94156 h1)). Qed.
Lemma lem7053663 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053665 (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term24 f n) = (_94156 f n).
Proof. exact (SYM (@lem7053558 f n _94156 h1)). Qed.
Lemma lem7053672 (a : nat) (b : nat) : (term71 a b) = (term71 a b).
Proof. exact (eq_refl (term71 a b)). Qed.
Lemma lem7053673 (a : nat) (b : nat) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term72 a b f n) = (term73 a b _94156 f n).
Proof. exact (MK_COMB (@lem7053672 a b) (@lem7053665 f n _94156 h1)). Qed.
Lemma lem7053674 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7053675 (a : nat) (b : nat) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term74 a b f n) = (term75 a b _94156 f n).
Proof. exact (MK_COMB (@lem7053674) (@lem7053673 a b f n _94156 h1)). Qed.
Lemma lem7053676 (a : nat) (b : nat) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : (term76 a b f n) = (term77 a b _94156 f n).
Proof. exact (MK_COMB (@lem7053675 a b f n _94156 h1) (@lem7053663 n)). Qed.
Lemma lem7053691 (a : nat) (b : nat) (f : nat -> nat) (n : nat) : (term78 a b f n) = (term78 a b f n).
Proof. exact (eq_refl (term78 a b f n)). Qed.
Lemma lem7053692 (a : nat) (b : nat) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : _94156 = term19) : ((term79 a b f n) = (term76 a b f n)) = ((term79 a b f n) = (term77 a b _94156 f n)).
Proof. exact (MK_COMB (@lem7053691 a b f n) (@lem7053676 a b f n _94156 h1)). Qed.
Lemma lem7053693 (a : nat) (b : nat) (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term80 a b f) = (term81 a b _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7053692 a b f n _94156 h1)). Qed.
Lemma lem7053694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053695 (a : nat) (b : nat) (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term82 a b f) = (term83 a b _94156 f).
Proof. exact (MK_COMB (@lem7053694) (@lem7053693 a b f _94156 h1)). Qed.
Lemma lem7053696 (a : nat) (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term84 a f) = (term85 a _94156 f).
Proof. exact (fun_ext (fun b : nat => @lem7053695 a b f _94156 h1)). Qed.
Lemma lem7053697 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053698 (a : nat) (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term86 a f) = (term87 a _94156 f).
Proof. exact (MK_COMB (@lem7053697) (@lem7053696 a f _94156 h1)). Qed.
Lemma lem7053699 (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term88 f) = (term89 _94156 f).
Proof. exact (fun_ext (fun a : nat => @lem7053698 a f _94156 h1)). Qed.
Lemma lem7053700 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053701 (f : nat -> nat) (_94156 : type1000) (h1 : _94156 = term19) : (term90 f) = (term91 _94156 f).
Proof. exact (MK_COMB (@lem7053700) (@lem7053699 f _94156 h1)). Qed.
Lemma lem7053702 (_94156 : type1000) (h1 : _94156 = term19) : term92 = (term93 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053701 f _94156 h1)). Qed.
Lemma lem7053703 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7053704 (_94156 : type1000) (h1 : _94156 = term19) : term1 = (term94 _94156).
Proof. exact (MK_COMB (@lem7053703) (@lem7053702 _94156 h1)). Qed.
Lemma lem7053705 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7053706 (_94156 : type1000) (h1 : _94156 = term19) : term3 = (term95 _94156).
Proof. exact (MK_COMB (@lem7053705) (@lem7053704 _94156 h1)). Qed.
Lemma lem7053707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053708 (_94156 : type1000) (h1 : _94156 = term19) : term17 = (term96 _94156).
Proof. exact (MK_COMB (@lem7053707) (@lem7053706 _94156 h1)). Qed.
Lemma lem7053709 {A : Type'} (_94156 : type1000) (h1 : _94156 = term19) : (term18 A) = (term97 A _94156).
Proof. exact (MK_COMB (@lem7053708 _94156 h1) (@lem7053662 A _94156 h1)). Qed.
Lemma lem7053710 {A : Type'} (_94156 : type1000) : term98 A _94156.
Proof. exact (fun h0 : _94156 = term19 => @lem7053709 A _94156 h0). Qed.
Lemma lem7053711 {A : Type'} : term99 A.
Proof. exact (fun _94156 : type1000 => @lem7053710 A _94156). Qed.
Lemma lem7053713 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term100 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem7053714 (P : Prop) (c : type1000) (Q : type253) : term101 P c Q.
Proof. exact (@lem7053713 type1000 P c Q). Qed.
Lemma lem7053715 {A : Type'} : term102 A.
Proof. exact (@lem7053714 (term18 A) term19 (term103 A)). Qed.
Lemma lem7053716 {A : Type'} (_94156 : type1000) : (term104 A _94156) = (term97 A _94156).
Proof. exact (eq_refl (term104 A _94156)). Qed.
Lemma lem7053717 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7053718 {A : Type'} (_94156 : type1000) : ((term18 A) = (term104 A _94156)) = ((term18 A) = (term97 A _94156)).
Proof. exact (MK_COMB (@lem7053717 A) (@lem7053716 A _94156)). Qed.
Lemma lem7053719 (_94156 : type1000) : (term106 _94156) = (term106 _94156).
Proof. exact (eq_refl (term106 _94156)). Qed.
Lemma lem7053720 {A : Type'} (_94156 : type1000) : (term107 A _94156) = (term98 A _94156).
Proof. exact (MK_COMB (@lem7053719 _94156) (@lem7053718 A _94156)). Qed.
Lemma lem7053721 {A : Type'} : (term108 A) = (term109 A).
Proof. exact (fun_ext (fun _94156 : type1000 => @lem7053720 A _94156)). Qed.
Lemma lem7053722 : (@all ((nat -> nat) -> nat -> nat -> nat)) = (@all ((nat -> nat) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@all ((nat -> nat) -> nat -> nat -> nat))). Qed.
Lemma lem7053723 {A : Type'} : (term110 A) = (term99 A).
Proof. exact (MK_COMB (@lem7053722) (@lem7053721 A)). Qed.
Lemma lem7053724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053725 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (MK_COMB (@lem7053724) (@lem7053723 A)). Qed.
Lemma lem7053726 {A : Type'} (_94156 : type1000) : (term104 A _94156) = (term97 A _94156).
Proof. exact (eq_refl (term104 A _94156)). Qed.
Lemma lem7053727 (_94156 : type1000) : (term106 _94156) = (term106 _94156).
Proof. exact (eq_refl (term106 _94156)). Qed.
Lemma lem7053728 {A : Type'} (_94156 : type1000) : (term113 A _94156) = (term114 A _94156).
Proof. exact (MK_COMB (@lem7053727 _94156) (@lem7053726 A _94156)). Qed.
Lemma lem7053729 {A : Type'} : (term115 A) = (term116 A).
Proof. exact (fun_ext (fun _94156 : type1000 => @lem7053728 A _94156)). Qed.
Lemma lem7053730 : (@all ((nat -> nat) -> nat -> nat -> nat)) = (@all ((nat -> nat) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@all ((nat -> nat) -> nat -> nat -> nat))). Qed.
Lemma lem7053731 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem7053730) (@lem7053729 A)). Qed.
Lemma lem7053732 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7053733 {A : Type'} : ((term18 A) = (term117 A)) = ((term18 A) = (term118 A)).
Proof. exact (MK_COMB (@lem7053732 A) (@lem7053731 A)). Qed.
Lemma lem7053734 {A : Type'} : (term102 A) = (term119 A).
Proof. exact (MK_COMB (@lem7053725 A) (@lem7053733 A)). Qed.
Lemma lem7053735 {A : Type'} : term119 A.
Proof. exact (EQ_MP (@lem7053734 A) (@lem7053715 A)). Qed.
Lemma lem7053736 {A : Type'} : (term18 A) = (term118 A).
Proof. exact (@lem7053735 A (@lem7053711 A)). Qed.
Lemma lem7053738 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term120 _3571 _3575 t)) = (term121 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7053739 (s : type1000) (t : type1000) : (s = (term122 t)) = (term123 s t).
Proof. exact (@lem7053738 type1606 (nat -> nat) s t). Qed.
Lemma lem7053740 (_94156 : type1000) : (_94156 = term124) = (term125 _94156).
Proof. exact (@lem7053739 _94156 term19). Qed.
Lemma lem7053741 (f : nat -> nat) : (term20 f) = (term21 f).
Proof. exact (eq_refl (term20 f)). Qed.
Lemma lem7053742 : term124 = term19.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053741 f)). Qed.
Lemma lem7053743 (_94156 : type1000) : (@eq ((nat -> nat) -> nat -> nat -> nat) _94156) = (@eq ((nat -> nat) -> nat -> nat -> nat) _94156).
Proof. exact (eq_refl (@eq ((nat -> nat) -> nat -> nat -> nat) _94156)). Qed.
Lemma lem7053744 (_94156 : type1000) : (_94156 = term124) = (_94156 = term19).
Proof. exact (MK_COMB (@lem7053743 _94156) (@lem7053742)). Qed.
Lemma lem7053745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7053746 (_94156 : type1000) : (term126 _94156) = (term127 _94156).
Proof. exact (MK_COMB (@lem7053745) (@lem7053744 _94156)). Qed.
Lemma lem7053747 (f : nat -> nat) : (term20 f) = (term21 f).
Proof. exact (eq_refl (term20 f)). Qed.
Lemma lem7053748 (_94156 : type1000) (f : nat -> nat) : (term22 _94156 f) = (term22 _94156 f).
Proof. exact (eq_refl (term22 _94156 f)). Qed.
Lemma lem7053749 (_94156 : type1000) (f : nat -> nat) : ((_94156 f) = (term20 f)) = ((_94156 f) = (term21 f)).
Proof. exact (MK_COMB (@lem7053748 _94156 f) (@lem7053747 f)). Qed.
Lemma lem7053750 (_94156 : type1000) : (term128 _94156) = (term129 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053749 _94156 f)). Qed.
Lemma lem7053751 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7053752 (_94156 : type1000) : (term125 _94156) = (term130 _94156).
Proof. exact (MK_COMB (@lem7053751) (@lem7053750 _94156)). Qed.
Lemma lem7053753 (_94156 : type1000) : ((_94156 = term124) = (term125 _94156)) = ((_94156 = term19) = (term130 _94156)).
Proof. exact (MK_COMB (@lem7053746 _94156) (@lem7053752 _94156)). Qed.
Lemma lem7053754 (_94156 : type1000) : (_94156 = term19) = (term130 _94156).
Proof. exact (EQ_MP (@lem7053753 _94156) (@lem7053740 _94156)). Qed.
Lemma lem7053756 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term120 _3571 _3575 t)) = (term121 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7053757 (s : type1606) (t : type1606) : (s = (term131 t)) = (term132 s t).
Proof. exact (@lem7053756 (nat -> nat) nat s t). Qed.
Lemma lem7053758 (_94156 : type1000) (f : nat -> nat) : ((_94156 f) = (term133 f)) = (term134 _94156 f).
Proof. exact (@lem7053757 (_94156 f) (term21 f)). Qed.
Lemma lem7053759 (f : nat -> nat) (n : nat) : (term23 f n) = (term24 f n).
Proof. exact (eq_refl (term23 f n)). Qed.
Lemma lem7053760 (f : nat -> nat) : (term133 f) = (term21 f).
Proof. exact (fun_ext (fun n : nat => @lem7053759 f n)). Qed.
Lemma lem7053761 (_94156 : type1000) (f : nat -> nat) : (term22 _94156 f) = (term22 _94156 f).
Proof. exact (eq_refl (term22 _94156 f)). Qed.
Lemma lem7053762 (_94156 : type1000) (f : nat -> nat) : ((_94156 f) = (term133 f)) = ((_94156 f) = (term21 f)).
Proof. exact (MK_COMB (@lem7053761 _94156 f) (@lem7053760 f)). Qed.
Lemma lem7053763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7053764 (_94156 : type1000) (f : nat -> nat) : (term135 _94156 f) = (term136 _94156 f).
Proof. exact (MK_COMB (@lem7053763) (@lem7053762 _94156 f)). Qed.
Lemma lem7053765 (f : nat -> nat) (n : nat) : (term23 f n) = (term24 f n).
Proof. exact (eq_refl (term23 f n)). Qed.
Lemma lem7053766 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term25 _94156 f n) = (term25 _94156 f n).
Proof. exact (eq_refl (term25 _94156 f n)). Qed.
Lemma lem7053767 (_94156 : type1000) (f : nat -> nat) (n : nat) : ((_94156 f n) = (term23 f n)) = ((_94156 f n) = (term24 f n)).
Proof. exact (MK_COMB (@lem7053766 _94156 f n) (@lem7053765 f n)). Qed.
Lemma lem7053768 (_94156 : type1000) (f : nat -> nat) : (term137 _94156 f) = (term138 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7053767 _94156 f n)). Qed.
Lemma lem7053769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053770 (_94156 : type1000) (f : nat -> nat) : (term134 _94156 f) = (term139 _94156 f).
Proof. exact (MK_COMB (@lem7053769) (@lem7053768 _94156 f)). Qed.
Lemma lem7053771 (_94156 : type1000) (f : nat -> nat) : (((_94156 f) = (term133 f)) = (term134 _94156 f)) = (((_94156 f) = (term21 f)) = (term139 _94156 f)).
Proof. exact (MK_COMB (@lem7053764 _94156 f) (@lem7053770 _94156 f)). Qed.
Lemma lem7053772 (_94156 : type1000) (f : nat -> nat) : ((_94156 f) = (term21 f)) = (term139 _94156 f).
Proof. exact (EQ_MP (@lem7053771 _94156 f) (@lem7053758 _94156 f)). Qed.
Lemma lem7053774 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term120 _3571 _3575 t)) = (term121 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7053775 (s : nat -> nat) (t : nat -> nat) : (s = (term140 t)) = (term141 s t).
Proof. exact (@lem7053774 nat nat s t). Qed.
Lemma lem7053776 (_94156 : type1000) (f : nat -> nat) (n : nat) : ((_94156 f n) = (term142 f n)) = (term143 _94156 f n).
Proof. exact (@lem7053775 (_94156 f n) (term24 f n)). Qed.
Lemma lem7053777 (f : nat -> nat) (i : nat) (n : nat) : (term144 f n i) = (term145 f i n).
Proof. exact (eq_refl (term144 f n i)). Qed.
Lemma lem7053778 (f : nat -> nat) (n : nat) : (term142 f n) = (term24 f n).
Proof. exact (fun_ext (fun i : nat => @lem7053777 f i n)). Qed.
Lemma lem7053779 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term25 _94156 f n) = (term25 _94156 f n).
Proof. exact (eq_refl (term25 _94156 f n)). Qed.
Lemma lem7053780 (_94156 : type1000) (f : nat -> nat) (n : nat) : ((_94156 f n) = (term142 f n)) = ((_94156 f n) = (term24 f n)).
Proof. exact (MK_COMB (@lem7053779 _94156 f n) (@lem7053778 f n)). Qed.
Lemma lem7053781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7053782 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term146 _94156 f n) = (term147 _94156 f n).
Proof. exact (MK_COMB (@lem7053781) (@lem7053780 _94156 f n)). Qed.
Lemma lem7053783 (f : nat -> nat) (i : nat) (n : nat) : (term144 f n i) = (term145 f i n).
Proof. exact (eq_refl (term144 f n i)). Qed.
Lemma lem7053784 (_94156 : type1000) (f : nat -> nat) (n : nat) (i : nat) : (term148 _94156 f n i) = (term148 _94156 f n i).
Proof. exact (eq_refl (term148 _94156 f n i)). Qed.
Lemma lem7053785 (_94156 : type1000) (f : nat -> nat) (i : nat) (n : nat) : ((_94156 f n i) = (term144 f n i)) = ((_94156 f n i) = (term145 f i n)).
Proof. exact (MK_COMB (@lem7053784 _94156 f n i) (@lem7053783 f i n)). Qed.
Lemma lem7053786 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term149 _94156 f n) = (term150 _94156 f n).
Proof. exact (fun_ext (fun i : nat => @lem7053785 _94156 f i n)). Qed.
Lemma lem7053787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053788 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term143 _94156 f n) = (term151 _94156 f n).
Proof. exact (MK_COMB (@lem7053787) (@lem7053786 _94156 f n)). Qed.
Lemma lem7053789 (_94156 : type1000) (f : nat -> nat) (n : nat) : (((_94156 f n) = (term142 f n)) = (term143 _94156 f n)) = (((_94156 f n) = (term24 f n)) = (term151 _94156 f n)).
Proof. exact (MK_COMB (@lem7053782 _94156 f n) (@lem7053788 _94156 f n)). Qed.
Lemma lem7053790 (_94156 : type1000) (f : nat -> nat) (n : nat) : ((_94156 f n) = (term24 f n)) = (term151 _94156 f n).
Proof. exact (EQ_MP (@lem7053789 _94156 f n) (@lem7053776 _94156 f n)). Qed.
Lemma lem7053791 (_94156 : type1000) (f : nat -> nat) (i : nat) (n : nat) : ((_94156 f n i) = (term145 f i n)) = ((_94156 f n i) = (term145 f i n)).
Proof. exact (eq_refl ((_94156 f n i) = (term145 f i n))). Qed.
Lemma lem7053792 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term150 _94156 f n) = (term150 _94156 f n).
Proof. exact (fun_ext (fun i : nat => @lem7053791 _94156 f i n)). Qed.
Lemma lem7053793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053794 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term151 _94156 f n) = (term151 _94156 f n).
Proof. exact (MK_COMB (@lem7053793) (@lem7053792 _94156 f n)). Qed.
Lemma lem7053795 (_94156 : type1000) (f : nat -> nat) (n : nat) : ((_94156 f n) = (term24 f n)) = (term151 _94156 f n).
Proof. exact (TRANS (@lem7053790 _94156 f n) (@lem7053794 _94156 f n)). Qed.
Lemma lem7053796 (_94156 : type1000) (f : nat -> nat) : (term138 _94156 f) = (term152 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7053795 _94156 f n)). Qed.
Lemma lem7053797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053798 (_94156 : type1000) (f : nat -> nat) : (term139 _94156 f) = (term153 _94156 f).
Proof. exact (MK_COMB (@lem7053797) (@lem7053796 _94156 f)). Qed.
Lemma lem7053799 (_94156 : type1000) (f : nat -> nat) : ((_94156 f) = (term21 f)) = (term153 _94156 f).
Proof. exact (TRANS (@lem7053772 _94156 f) (@lem7053798 _94156 f)). Qed.
Lemma lem7053800 (_94156 : type1000) : (term129 _94156) = (term154 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053799 _94156 f)). Qed.
Lemma lem7053801 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7053802 (_94156 : type1000) : (term130 _94156) = (term155 _94156).
Proof. exact (MK_COMB (@lem7053801) (@lem7053800 _94156)). Qed.
Lemma lem7053803 (_94156 : type1000) : (_94156 = term19) = (term155 _94156).
Proof. exact (TRANS (@lem7053754 _94156) (@lem7053802 _94156)). Qed.
Lemma lem7053804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053805 (_94156 : type1000) : (term106 _94156) = (term156 _94156).
Proof. exact (MK_COMB (@lem7053804) (@lem7053803 _94156)). Qed.
Lemma lem7053806 {A : Type'} (_94156 : type1000) : (term97 A _94156) = (term97 A _94156).
Proof. exact (eq_refl (term97 A _94156)). Qed.
Lemma lem7053807 {A : Type'} (_94156 : type1000) : (term114 A _94156) = (term157 A _94156).
Proof. exact (MK_COMB (@lem7053805 _94156) (@lem7053806 A _94156)). Qed.
Lemma lem7053808 {A : Type'} : (term116 A) = (term158 A).
Proof. exact (fun_ext (fun _94156 : type1000 => @lem7053807 A _94156)). Qed.
Lemma lem7053809 : (@all ((nat -> nat) -> nat -> nat -> nat)) = (@all ((nat -> nat) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@all ((nat -> nat) -> nat -> nat -> nat))). Qed.
Lemma lem7053810 {A : Type'} : (term118 A) = (term159 A).
Proof. exact (MK_COMB (@lem7053809) (@lem7053808 A)). Qed.
Lemma lem7053811 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (eq_refl (term105 A)). Qed.
Lemma lem7053812 {A : Type'} : ((term18 A) = (term118 A)) = ((term18 A) = (term159 A)).
Proof. exact (MK_COMB (@lem7053811 A) (@lem7053810 A)). Qed.
Lemma lem7053813 {A : Type'} : (term18 A) = (term159 A).
Proof. exact (EQ_MP (@lem7053812 A) (@lem7053736 A)). Qed.
Lemma lem7053814 {A : Type'} (_94157 : type701 A) (h1 : _94157 = (term160 A)) : _94157 = (term160 A).
Proof. exact (h1). Qed.
Lemma lem7053815 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7053816 {A : Type'} (f : A -> nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (_94157 f) = (term161 A f).
Proof. exact (MK_COMB (@lem7053814 A _94157 h1) (@lem7053815 A f)). Qed.
Lemma lem7053817 {A : Type'} (f : A -> nat) : (term161 A f) = (term162 A f).
Proof. exact (eq_refl (term161 A f)). Qed.
Lemma lem7053818 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term163 A _94157 f) = (term163 A _94157 f).
Proof. exact (eq_refl (term163 A _94157 f)). Qed.
Lemma lem7053819 {A : Type'} (_94157 : type701 A) (f : A -> nat) : ((_94157 f) = (term161 A f)) = ((_94157 f) = (term162 A f)).
Proof. exact (MK_COMB (@lem7053818 A _94157 f) (@lem7053817 A f)). Qed.
Lemma lem7053820 {A : Type'} (f : A -> nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (_94157 f) = (term162 A f).
Proof. exact (EQ_MP (@lem7053819 A _94157 f) (@lem7053816 A f _94157 h1)). Qed.
Lemma lem7053821 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053822 {A : Type'} (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (_94157 f n) = (term164 A f n).
Proof. exact (MK_COMB (@lem7053820 A f _94157 h1) (@lem7053821 n)). Qed.
Lemma lem7053823 {A : Type'} (f : A -> nat) (n : nat) : (term164 A f n) = (term50 A f n).
Proof. exact (eq_refl (term164 A f n)). Qed.
Lemma lem7053824 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term165 A _94157 f n) = (term165 A _94157 f n).
Proof. exact (eq_refl (term165 A _94157 f n)). Qed.
Lemma lem7053825 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : ((_94157 f n) = (term164 A f n)) = ((_94157 f n) = (term50 A f n)).
Proof. exact (MK_COMB (@lem7053824 A _94157 f n) (@lem7053823 A f n)). Qed.
Lemma lem7053826 {A : Type'} (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (_94157 f n) = (term50 A f n).
Proof. exact (EQ_MP (@lem7053825 A _94157 f n) (@lem7053822 A f n _94157 h1)). Qed.
Lemma lem7053858 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term36 s _94156 f n) = (term36 s _94156 f n).
Proof. exact (eq_refl (term36 s _94156 f n)). Qed.
Lemma lem7053859 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term38 _94156 f n) = (term38 _94156 f n).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7053858 s _94156 f n)). Qed.
Lemma lem7053860 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7053861 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term40 _94156 f n) = (term40 _94156 f n).
Proof. exact (MK_COMB (@lem7053860) (@lem7053859 _94156 f n)). Qed.
Lemma lem7053862 (_94156 : type1000) (f : nat -> nat) : (term42 _94156 f) = (term42 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7053861 _94156 f n)). Qed.
Lemma lem7053863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053864 (_94156 : type1000) (f : nat -> nat) : (term44 _94156 f) = (term44 _94156 f).
Proof. exact (MK_COMB (@lem7053863) (@lem7053862 _94156 f)). Qed.
Lemma lem7053865 (_94156 : type1000) : (term46 _94156) = (term46 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053864 _94156 f)). Qed.
Lemma lem7053866 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7053867 (_94156 : type1000) : (term47 _94156) = (term47 _94156).
Proof. exact (MK_COMB (@lem7053866) (@lem7053865 _94156)). Qed.
Lemma lem7053868 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7053869 (_94156 : type1000) : (term48 _94156) = (term48 _94156).
Proof. exact (MK_COMB (@lem7053868) (@lem7053867 _94156)). Qed.
Lemma lem7053870 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053872 {A : Type'} (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term50 A f n) = (_94157 f n).
Proof. exact (SYM (@lem7053826 A f n _94157 h1)). Qed.
Lemma lem7053873 {A : Type'} (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term50 A f n) = (_94157 f n).
Proof. exact (@lem7053872 A f n _94157 h1). Qed.
Lemma lem7053876 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@nsum A s).
Proof. exact (eq_refl (@nsum A s)). Qed.
Lemma lem7053877 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term51 A s f n) = (term166 A s _94157 f n).
Proof. exact (MK_COMB (@lem7053876 A s) (@lem7053873 A f n _94157 h1)). Qed.
Lemma lem7053878 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7053879 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term52 A s f n) = (term167 A s _94157 f n).
Proof. exact (MK_COMB (@lem7053878) (@lem7053877 A s f n _94157 h1)). Qed.
Lemma lem7053880 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term53 A s f n) = (term168 A s _94157 f n).
Proof. exact (MK_COMB (@lem7053879 A s f n _94157 h1) (@lem7053870 n)). Qed.
Lemma lem7053891 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term54 A s f n) = (term54 A s f n).
Proof. exact (eq_refl (term54 A s f n)). Qed.
Lemma lem7053892 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : ((term55 A s f n) = (term53 A s f n)) = ((term55 A s f n) = (term168 A s _94157 f n)).
Proof. exact (MK_COMB (@lem7053891 A s f n) (@lem7053880 A s f n _94157 h1)). Qed.
Lemma lem7053897 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (eq_refl (term56 A s)). Qed.
Lemma lem7053898 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term57 A s f n) = (term169 A s _94157 f n).
Proof. exact (MK_COMB (@lem7053897 A s) (@lem7053892 A s f n _94157 h1)). Qed.
Lemma lem7053899 {A : Type'} (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term58 A f n) = (term170 A _94157 f n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7053898 A s f n _94157 h1)). Qed.
Lemma lem7053900 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7053901 {A : Type'} (f : A -> nat) (n : nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term59 A f n) = (term171 A _94157 f n).
Proof. exact (MK_COMB (@lem7053900 A) (@lem7053899 A f n _94157 h1)). Qed.
Lemma lem7053902 {A : Type'} (f : A -> nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term60 A f) = (term172 A _94157 f).
Proof. exact (fun_ext (fun n : nat => @lem7053901 A f n _94157 h1)). Qed.
Lemma lem7053903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053904 {A : Type'} (f : A -> nat) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term61 A f) = (term173 A _94157 f).
Proof. exact (MK_COMB (@lem7053903) (@lem7053902 A f _94157 h1)). Qed.
Lemma lem7053905 {A : Type'} (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term62 A) = (term174 A _94157).
Proof. exact (fun_ext (fun f : A -> nat => @lem7053904 A f _94157 h1)). Qed.
Lemma lem7053906 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7053907 {A : Type'} (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term63 A) = (term175 A _94157).
Proof. exact (MK_COMB (@lem7053906 A) (@lem7053905 A _94157 h1)). Qed.
Lemma lem7053908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053909 {A : Type'} (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term11 A) = (term176 A _94157).
Proof. exact (MK_COMB (@lem7053908) (@lem7053907 A _94157 h1)). Qed.
Lemma lem7053910 {A : Type'} (_94156 : type1000) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term64 A _94156) = (term177 A _94157 _94156).
Proof. exact (MK_COMB (@lem7053909 A _94157 h1) (@lem7053869 _94156)). Qed.
Lemma lem7053917 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem7053918 (m : nat) : (term66 m) = (term66 m).
Proof. exact (fun_ext (fun n : nat => @lem7053917 m n)). Qed.
Lemma lem7053919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053920 (m : nat) : (term67 m) = (term67 m).
Proof. exact (MK_COMB (@lem7053919) (@lem7053918 m)). Qed.
Lemma lem7053921 : term68 = term68.
Proof. exact (fun_ext (fun m : nat => @lem7053920 m)). Qed.
Lemma lem7053922 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053923 : term69 = term69.
Proof. exact (MK_COMB (@lem7053922) (@lem7053921)). Qed.
Lemma lem7053924 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053925 : term14 = term14.
Proof. exact (MK_COMB (@lem7053924) (@lem7053923)). Qed.
Lemma lem7053926 {A : Type'} (_94156 : type1000) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term70 A _94156) = (term178 A _94157 _94156).
Proof. exact (MK_COMB (@lem7053925) (@lem7053910 A _94156 _94157 h1)). Qed.
Lemma lem7053959 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : ((term79 a b f n) = (term77 a b _94156 f n)) = ((term79 a b f n) = (term77 a b _94156 f n)).
Proof. exact (eq_refl ((term79 a b f n) = (term77 a b _94156 f n))). Qed.
Lemma lem7053960 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term81 a b _94156 f) = (term81 a b _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7053959 a b _94156 f n)). Qed.
Lemma lem7053961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053962 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term83 a b _94156 f) = (term83 a b _94156 f).
Proof. exact (MK_COMB (@lem7053961) (@lem7053960 a b _94156 f)). Qed.
Lemma lem7053963 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term85 a _94156 f) = (term85 a _94156 f).
Proof. exact (fun_ext (fun b : nat => @lem7053962 a b _94156 f)). Qed.
Lemma lem7053964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053965 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term87 a _94156 f) = (term87 a _94156 f).
Proof. exact (MK_COMB (@lem7053964) (@lem7053963 a _94156 f)). Qed.
Lemma lem7053966 (_94156 : type1000) (f : nat -> nat) : (term89 _94156 f) = (term89 _94156 f).
Proof. exact (fun_ext (fun a : nat => @lem7053965 a _94156 f)). Qed.
Lemma lem7053967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053968 (_94156 : type1000) (f : nat -> nat) : (term91 _94156 f) = (term91 _94156 f).
Proof. exact (MK_COMB (@lem7053967) (@lem7053966 _94156 f)). Qed.
Lemma lem7053969 (_94156 : type1000) : (term93 _94156) = (term93 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053968 _94156 f)). Qed.
Lemma lem7053970 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7053971 (_94156 : type1000) : (term94 _94156) = (term94 _94156).
Proof. exact (MK_COMB (@lem7053970) (@lem7053969 _94156)). Qed.
Lemma lem7053972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7053973 (_94156 : type1000) : (term95 _94156) = (term95 _94156).
Proof. exact (MK_COMB (@lem7053972) (@lem7053971 _94156)). Qed.
Lemma lem7053974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7053975 (_94156 : type1000) : (term96 _94156) = (term96 _94156).
Proof. exact (MK_COMB (@lem7053974) (@lem7053973 _94156)). Qed.
Lemma lem7053976 {A : Type'} (_94156 : type1000) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term97 A _94156) = (term179 A _94157 _94156).
Proof. exact (MK_COMB (@lem7053975 _94156) (@lem7053926 A _94156 _94157 h1)). Qed.
Lemma lem7053993 (_94156 : type1000) (f : nat -> nat) (i : nat) (n : nat) : ((_94156 f n i) = (term145 f i n)) = ((_94156 f n i) = (term145 f i n)).
Proof. exact (eq_refl ((_94156 f n i) = (term145 f i n))). Qed.
Lemma lem7053994 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term150 _94156 f n) = (term150 _94156 f n).
Proof. exact (fun_ext (fun i : nat => @lem7053993 _94156 f i n)). Qed.
Lemma lem7053995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053996 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term151 _94156 f n) = (term151 _94156 f n).
Proof. exact (MK_COMB (@lem7053995) (@lem7053994 _94156 f n)). Qed.
Lemma lem7053997 (_94156 : type1000) (f : nat -> nat) : (term152 _94156 f) = (term152 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7053996 _94156 f n)). Qed.
Lemma lem7053998 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7053999 (_94156 : type1000) (f : nat -> nat) : (term153 _94156 f) = (term153 _94156 f).
Proof. exact (MK_COMB (@lem7053998) (@lem7053997 _94156 f)). Qed.
Lemma lem7054000 (_94156 : type1000) : (term154 _94156) = (term154 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7053999 _94156 f)). Qed.
Lemma lem7054001 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7054002 (_94156 : type1000) : (term155 _94156) = (term155 _94156).
Proof. exact (MK_COMB (@lem7054001) (@lem7054000 _94156)). Qed.
Lemma lem7054003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054004 (_94156 : type1000) : (term156 _94156) = (term156 _94156).
Proof. exact (MK_COMB (@lem7054003) (@lem7054002 _94156)). Qed.
Lemma lem7054005 {A : Type'} (_94156 : type1000) (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term157 A _94156) = (term180 A _94157 _94156).
Proof. exact (MK_COMB (@lem7054004 _94156) (@lem7053976 A _94156 _94157 h1)). Qed.
Lemma lem7054006 {A : Type'} (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term158 A) = (term181 A _94157).
Proof. exact (fun_ext (fun _94156 : type1000 => @lem7054005 A _94156 _94157 h1)). Qed.
Lemma lem7054007 : (@all ((nat -> nat) -> nat -> nat -> nat)) = (@all ((nat -> nat) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@all ((nat -> nat) -> nat -> nat -> nat))). Qed.
Lemma lem7054008 {A : Type'} (_94157 : type701 A) (h1 : _94157 = (term160 A)) : (term159 A) = (term182 A _94157).
Proof. exact (MK_COMB (@lem7054007) (@lem7054006 A _94157 h1)). Qed.
Lemma lem7054009 {A : Type'} (_94157 : type701 A) : term183 A _94157.
Proof. exact (fun h0 : _94157 = (term160 A) => @lem7054008 A _94157 h0). Qed.
Lemma lem7054010 {A : Type'} : term184 A.
Proof. exact (fun _94157 : type701 A => @lem7054009 A _94157). Qed.
Lemma lem7054012 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term100 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem7054013 {A : Type'} (P : Prop) (c : type701 A) (Q : type186 A) : term185 A P c Q.
Proof. exact (@lem7054012 (type701 A) P c Q). Qed.
Lemma lem7054014 {A : Type'} : term186 A.
Proof. exact (@lem7054013 A (term159 A) (term160 A) (term187 A)). Qed.
Lemma lem7054015 {A : Type'} (_94157 : type701 A) : (term188 A _94157) = (term182 A _94157).
Proof. exact (eq_refl (term188 A _94157)). Qed.
Lemma lem7054016 {A : Type'} : (term189 A) = (term189 A).
Proof. exact (eq_refl (term189 A)). Qed.
Lemma lem7054017 {A : Type'} (_94157 : type701 A) : ((term159 A) = (term188 A _94157)) = ((term159 A) = (term182 A _94157)).
Proof. exact (MK_COMB (@lem7054016 A) (@lem7054015 A _94157)). Qed.
Lemma lem7054018 {A : Type'} (_94157 : type701 A) : (term190 A _94157) = (term190 A _94157).
Proof. exact (eq_refl (term190 A _94157)). Qed.
Lemma lem7054019 {A : Type'} (_94157 : type701 A) : (term191 A _94157) = (term183 A _94157).
Proof. exact (MK_COMB (@lem7054018 A _94157) (@lem7054017 A _94157)). Qed.
Lemma lem7054020 {A : Type'} : (term192 A) = (term193 A).
Proof. exact (fun_ext (fun _94157 : type701 A => @lem7054019 A _94157)). Qed.
Lemma lem7054021 {A : Type'} : (@all ((A -> nat) -> nat -> A -> nat)) = (@all ((A -> nat) -> nat -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> nat -> A -> nat))). Qed.
Lemma lem7054022 {A : Type'} : (term194 A) = (term184 A).
Proof. exact (MK_COMB (@lem7054021 A) (@lem7054020 A)). Qed.
Lemma lem7054023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054024 {A : Type'} : (term195 A) = (term196 A).
Proof. exact (MK_COMB (@lem7054023) (@lem7054022 A)). Qed.
Lemma lem7054025 {A : Type'} (_94157 : type701 A) : (term188 A _94157) = (term182 A _94157).
Proof. exact (eq_refl (term188 A _94157)). Qed.
Lemma lem7054026 {A : Type'} (_94157 : type701 A) : (term190 A _94157) = (term190 A _94157).
Proof. exact (eq_refl (term190 A _94157)). Qed.
Lemma lem7054027 {A : Type'} (_94157 : type701 A) : (term197 A _94157) = (term198 A _94157).
Proof. exact (MK_COMB (@lem7054026 A _94157) (@lem7054025 A _94157)). Qed.
Lemma lem7054028 {A : Type'} : (term199 A) = (term200 A).
Proof. exact (fun_ext (fun _94157 : type701 A => @lem7054027 A _94157)). Qed.
Lemma lem7054029 {A : Type'} : (@all ((A -> nat) -> nat -> A -> nat)) = (@all ((A -> nat) -> nat -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> nat -> A -> nat))). Qed.
Lemma lem7054030 {A : Type'} : (term201 A) = (term202 A).
Proof. exact (MK_COMB (@lem7054029 A) (@lem7054028 A)). Qed.
Lemma lem7054031 {A : Type'} : (term189 A) = (term189 A).
Proof. exact (eq_refl (term189 A)). Qed.
Lemma lem7054032 {A : Type'} : ((term159 A) = (term201 A)) = ((term159 A) = (term202 A)).
Proof. exact (MK_COMB (@lem7054031 A) (@lem7054030 A)). Qed.
Lemma lem7054033 {A : Type'} : (term186 A) = (term203 A).
Proof. exact (MK_COMB (@lem7054024 A) (@lem7054032 A)). Qed.
Lemma lem7054034 {A : Type'} : term203 A.
Proof. exact (EQ_MP (@lem7054033 A) (@lem7054014 A)). Qed.
Lemma lem7054035 {A : Type'} : (term159 A) = (term202 A).
Proof. exact (@lem7054034 A (@lem7054010 A)). Qed.
Lemma lem7054037 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term120 _3571 _3575 t)) = (term121 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7054038 {A : Type'} (s : type701 A) (t : type701 A) : (s = (term204 A t)) = (term205 A s t).
Proof. exact (@lem7054037 (type1598 A) (A -> nat) s t). Qed.
Lemma lem7054039 {A : Type'} (_94157 : type701 A) : (_94157 = (term206 A)) = (term207 A _94157).
Proof. exact (@lem7054038 A _94157 (term160 A)). Qed.
Lemma lem7054040 {A : Type'} (f : A -> nat) : (term161 A f) = (term162 A f).
Proof. exact (eq_refl (term161 A f)). Qed.
Lemma lem7054041 {A : Type'} : (term206 A) = (term160 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7054040 A f)). Qed.
Lemma lem7054042 {A : Type'} (_94157 : type701 A) : (@eq ((A -> nat) -> nat -> A -> nat) _94157) = (@eq ((A -> nat) -> nat -> A -> nat) _94157).
Proof. exact (eq_refl (@eq ((A -> nat) -> nat -> A -> nat) _94157)). Qed.
Lemma lem7054043 {A : Type'} (_94157 : type701 A) : (_94157 = (term206 A)) = (_94157 = (term160 A)).
Proof. exact (MK_COMB (@lem7054042 A _94157) (@lem7054041 A)). Qed.
Lemma lem7054044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7054045 {A : Type'} (_94157 : type701 A) : (term208 A _94157) = (term209 A _94157).
Proof. exact (MK_COMB (@lem7054044) (@lem7054043 A _94157)). Qed.
Lemma lem7054046 {A : Type'} (f : A -> nat) : (term161 A f) = (term162 A f).
Proof. exact (eq_refl (term161 A f)). Qed.
Lemma lem7054047 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term163 A _94157 f) = (term163 A _94157 f).
Proof. exact (eq_refl (term163 A _94157 f)). Qed.
Lemma lem7054048 {A : Type'} (_94157 : type701 A) (f : A -> nat) : ((_94157 f) = (term161 A f)) = ((_94157 f) = (term162 A f)).
Proof. exact (MK_COMB (@lem7054047 A _94157 f) (@lem7054046 A f)). Qed.
Lemma lem7054049 {A : Type'} (_94157 : type701 A) : (term210 A _94157) = (term211 A _94157).
Proof. exact (fun_ext (fun f : A -> nat => @lem7054048 A _94157 f)). Qed.
Lemma lem7054050 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7054051 {A : Type'} (_94157 : type701 A) : (term207 A _94157) = (term212 A _94157).
Proof. exact (MK_COMB (@lem7054050 A) (@lem7054049 A _94157)). Qed.
Lemma lem7054052 {A : Type'} (_94157 : type701 A) : ((_94157 = (term206 A)) = (term207 A _94157)) = ((_94157 = (term160 A)) = (term212 A _94157)).
Proof. exact (MK_COMB (@lem7054045 A _94157) (@lem7054051 A _94157)). Qed.
Lemma lem7054053 {A : Type'} (_94157 : type701 A) : (_94157 = (term160 A)) = (term212 A _94157).
Proof. exact (EQ_MP (@lem7054052 A _94157) (@lem7054039 A _94157)). Qed.
Lemma lem7054055 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term120 _3571 _3575 t)) = (term121 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7054056 {A : Type'} (s : type1598 A) (t : type1598 A) : (s = (term213 A t)) = (term214 A s t).
Proof. exact (@lem7054055 (A -> nat) nat s t). Qed.
Lemma lem7054057 {A : Type'} (_94157 : type701 A) (f : A -> nat) : ((_94157 f) = (term215 A f)) = (term216 A _94157 f).
Proof. exact (@lem7054056 A (_94157 f) (term162 A f)). Qed.
Lemma lem7054058 {A : Type'} (f : A -> nat) (n : nat) : (term164 A f n) = (term50 A f n).
Proof. exact (eq_refl (term164 A f n)). Qed.
Lemma lem7054059 {A : Type'} (f : A -> nat) : (term215 A f) = (term162 A f).
Proof. exact (fun_ext (fun n : nat => @lem7054058 A f n)). Qed.
Lemma lem7054060 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term163 A _94157 f) = (term163 A _94157 f).
Proof. exact (eq_refl (term163 A _94157 f)). Qed.
Lemma lem7054061 {A : Type'} (_94157 : type701 A) (f : A -> nat) : ((_94157 f) = (term215 A f)) = ((_94157 f) = (term162 A f)).
Proof. exact (MK_COMB (@lem7054060 A _94157 f) (@lem7054059 A f)). Qed.
Lemma lem7054062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7054063 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term217 A _94157 f) = (term218 A _94157 f).
Proof. exact (MK_COMB (@lem7054062) (@lem7054061 A _94157 f)). Qed.
Lemma lem7054064 {A : Type'} (f : A -> nat) (n : nat) : (term164 A f n) = (term50 A f n).
Proof. exact (eq_refl (term164 A f n)). Qed.
Lemma lem7054065 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term165 A _94157 f n) = (term165 A _94157 f n).
Proof. exact (eq_refl (term165 A _94157 f n)). Qed.
Lemma lem7054066 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : ((_94157 f n) = (term164 A f n)) = ((_94157 f n) = (term50 A f n)).
Proof. exact (MK_COMB (@lem7054065 A _94157 f n) (@lem7054064 A f n)). Qed.
Lemma lem7054067 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term219 A _94157 f) = (term220 A _94157 f).
Proof. exact (fun_ext (fun n : nat => @lem7054066 A _94157 f n)). Qed.
Lemma lem7054068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054069 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term216 A _94157 f) = (term221 A _94157 f).
Proof. exact (MK_COMB (@lem7054068) (@lem7054067 A _94157 f)). Qed.
Lemma lem7054070 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (((_94157 f) = (term215 A f)) = (term216 A _94157 f)) = (((_94157 f) = (term162 A f)) = (term221 A _94157 f)).
Proof. exact (MK_COMB (@lem7054063 A _94157 f) (@lem7054069 A _94157 f)). Qed.
Lemma lem7054071 {A : Type'} (_94157 : type701 A) (f : A -> nat) : ((_94157 f) = (term162 A f)) = (term221 A _94157 f).
Proof. exact (EQ_MP (@lem7054070 A _94157 f) (@lem7054057 A _94157 f)). Qed.
Lemma lem7054073 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term120 _3571 _3575 t)) = (term121 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7054074 {A : Type'} (s : A -> nat) (t : A -> nat) : (s = (term222 A t)) = (term223 A s t).
Proof. exact (@lem7054073 nat A s t). Qed.
Lemma lem7054075 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : ((_94157 f n) = (term224 A f n)) = (term225 A _94157 f n).
Proof. exact (@lem7054074 A (_94157 f n) (term50 A f n)). Qed.
Lemma lem7054076 {A : Type'} (f : A -> nat) (i : A) (n : nat) : (term226 A f n i) = (term49 A f i n).
Proof. exact (eq_refl (term226 A f n i)). Qed.
Lemma lem7054077 {A : Type'} (f : A -> nat) (n : nat) : (term224 A f n) = (term50 A f n).
Proof. exact (fun_ext (fun i : A => @lem7054076 A f i n)). Qed.
Lemma lem7054078 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term165 A _94157 f n) = (term165 A _94157 f n).
Proof. exact (eq_refl (term165 A _94157 f n)). Qed.
Lemma lem7054079 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : ((_94157 f n) = (term224 A f n)) = ((_94157 f n) = (term50 A f n)).
Proof. exact (MK_COMB (@lem7054078 A _94157 f n) (@lem7054077 A f n)). Qed.
Lemma lem7054080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7054081 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term227 A _94157 f n) = (term228 A _94157 f n).
Proof. exact (MK_COMB (@lem7054080) (@lem7054079 A _94157 f n)). Qed.
Lemma lem7054082 {A : Type'} (f : A -> nat) (i : A) (n : nat) : (term226 A f n i) = (term49 A f i n).
Proof. exact (eq_refl (term226 A f n i)). Qed.
Lemma lem7054083 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) (i : A) : (term229 A _94157 f n i) = (term229 A _94157 f n i).
Proof. exact (eq_refl (term229 A _94157 f n i)). Qed.
Lemma lem7054084 {A : Type'} (_94157 : type701 A) (f : A -> nat) (i : A) (n : nat) : ((_94157 f n i) = (term226 A f n i)) = ((_94157 f n i) = (term49 A f i n)).
Proof. exact (MK_COMB (@lem7054083 A _94157 f n i) (@lem7054082 A f i n)). Qed.
Lemma lem7054085 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term230 A _94157 f n) = (term231 A _94157 f n).
Proof. exact (fun_ext (fun i : A => @lem7054084 A _94157 f i n)). Qed.
Lemma lem7054086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7054087 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term225 A _94157 f n) = (term232 A _94157 f n).
Proof. exact (MK_COMB (@lem7054086 A) (@lem7054085 A _94157 f n)). Qed.
Lemma lem7054088 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (((_94157 f n) = (term224 A f n)) = (term225 A _94157 f n)) = (((_94157 f n) = (term50 A f n)) = (term232 A _94157 f n)).
Proof. exact (MK_COMB (@lem7054081 A _94157 f n) (@lem7054087 A _94157 f n)). Qed.
Lemma lem7054089 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : ((_94157 f n) = (term50 A f n)) = (term232 A _94157 f n).
Proof. exact (EQ_MP (@lem7054088 A _94157 f n) (@lem7054075 A _94157 f n)). Qed.
Lemma lem7054090 {A : Type'} (_94157 : type701 A) (f : A -> nat) (i : A) (n : nat) : ((_94157 f n i) = (term49 A f i n)) = ((_94157 f n i) = (term49 A f i n)).
Proof. exact (eq_refl ((_94157 f n i) = (term49 A f i n))). Qed.
Lemma lem7054091 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term231 A _94157 f n) = (term231 A _94157 f n).
Proof. exact (fun_ext (fun i : A => @lem7054090 A _94157 f i n)). Qed.
Lemma lem7054092 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7054093 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term232 A _94157 f n) = (term232 A _94157 f n).
Proof. exact (MK_COMB (@lem7054092 A) (@lem7054091 A _94157 f n)). Qed.
Lemma lem7054094 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : ((_94157 f n) = (term50 A f n)) = (term232 A _94157 f n).
Proof. exact (TRANS (@lem7054089 A _94157 f n) (@lem7054093 A _94157 f n)). Qed.
Lemma lem7054095 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term220 A _94157 f) = (term233 A _94157 f).
Proof. exact (fun_ext (fun n : nat => @lem7054094 A _94157 f n)). Qed.
Lemma lem7054096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054097 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term221 A _94157 f) = (term234 A _94157 f).
Proof. exact (MK_COMB (@lem7054096) (@lem7054095 A _94157 f)). Qed.
Lemma lem7054098 {A : Type'} (_94157 : type701 A) (f : A -> nat) : ((_94157 f) = (term162 A f)) = (term234 A _94157 f).
Proof. exact (TRANS (@lem7054071 A _94157 f) (@lem7054097 A _94157 f)). Qed.
Lemma lem7054099 {A : Type'} (_94157 : type701 A) : (term211 A _94157) = (term235 A _94157).
Proof. exact (fun_ext (fun f : A -> nat => @lem7054098 A _94157 f)). Qed.
Lemma lem7054100 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7054101 {A : Type'} (_94157 : type701 A) : (term212 A _94157) = (term236 A _94157).
Proof. exact (MK_COMB (@lem7054100 A) (@lem7054099 A _94157)). Qed.
Lemma lem7054102 {A : Type'} (_94157 : type701 A) : (_94157 = (term160 A)) = (term236 A _94157).
Proof. exact (TRANS (@lem7054053 A _94157) (@lem7054101 A _94157)). Qed.
Lemma lem7054103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054104 {A : Type'} (_94157 : type701 A) : (term190 A _94157) = (term237 A _94157).
Proof. exact (MK_COMB (@lem7054103) (@lem7054102 A _94157)). Qed.
Lemma lem7054105 {A : Type'} (_94157 : type701 A) : (term182 A _94157) = (term182 A _94157).
Proof. exact (eq_refl (term182 A _94157)). Qed.
Lemma lem7054106 {A : Type'} (_94157 : type701 A) : (term198 A _94157) = (term238 A _94157).
Proof. exact (MK_COMB (@lem7054104 A _94157) (@lem7054105 A _94157)). Qed.
Lemma lem7054107 {A : Type'} : (term200 A) = (term239 A).
Proof. exact (fun_ext (fun _94157 : type701 A => @lem7054106 A _94157)). Qed.
Lemma lem7054108 {A : Type'} : (@all ((A -> nat) -> nat -> A -> nat)) = (@all ((A -> nat) -> nat -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> nat -> A -> nat))). Qed.
Lemma lem7054109 {A : Type'} : (term202 A) = (term240 A).
Proof. exact (MK_COMB (@lem7054108 A) (@lem7054107 A)). Qed.
Lemma lem7054110 {A : Type'} : (term189 A) = (term189 A).
Proof. exact (eq_refl (term189 A)). Qed.
Lemma lem7054111 {A : Type'} : ((term159 A) = (term202 A)) = ((term159 A) = (term240 A)).
Proof. exact (MK_COMB (@lem7054110 A) (@lem7054109 A)). Qed.
Lemma lem7054114 {A : Type'} : (term159 A) = (term240 A).
Proof. exact (EQ_MP (@lem7054111 A) (@lem7054035 A)). Qed.
Lemma lem7054115 {A : Type'} : (term18 A) = (term240 A).
Proof. exact (TRANS (@lem7053813 A) (@lem7054114 A)). Qed.
Lemma lem7054116 {A : Type'} : (term5 A) = (term240 A).
Proof. exact (TRANS (@lem7053545 A) (@lem7054115 A)). Qed.
Lemma lem7054121 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term36 s _94156 f n) = (term36 s _94156 f n).
Proof. exact (eq_refl (term36 s _94156 f n)). Qed.
Lemma lem7054122 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term38 _94156 f n) = (term38 _94156 f n).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7054121 s _94156 f n)). Qed.
Lemma lem7054123 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7054124 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term40 _94156 f n) = (term40 _94156 f n).
Proof. exact (MK_COMB (@lem7054123) (@lem7054122 _94156 f n)). Qed.
Lemma lem7054125 (_94156 : type1000) (f : nat -> nat) : (term42 _94156 f) = (term42 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7054124 _94156 f n)). Qed.
Lemma lem7054126 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054127 (_94156 : type1000) (f : nat -> nat) : (term44 _94156 f) = (term44 _94156 f).
Proof. exact (MK_COMB (@lem7054126) (@lem7054125 _94156 f)). Qed.
Lemma lem7054128 (_94156 : type1000) : (term46 _94156) = (term46 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7054127 _94156 f)). Qed.
Lemma lem7054129 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7054130 (_94156 : type1000) : (term47 _94156) = (term47 _94156).
Proof. exact (MK_COMB (@lem7054129) (@lem7054128 _94156)). Qed.
Lemma lem7054131 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7054132 (_94156 : type1000) : (term48 _94156) = (term48 _94156).
Proof. exact (MK_COMB (@lem7054131) (@lem7054130 _94156)). Qed.
Lemma lem7054137 {A : Type'} (s : A -> Prop) (_94157 : type701 A) (f : A -> nat) (n : nat) : (term169 A s _94157 f n) = (term169 A s _94157 f n).
Proof. exact (eq_refl (term169 A s _94157 f n)). Qed.
Lemma lem7054138 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term170 A _94157 f n) = (term170 A _94157 f n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7054137 A s _94157 f n)). Qed.
Lemma lem7054139 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7054140 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term171 A _94157 f n) = (term171 A _94157 f n).
Proof. exact (MK_COMB (@lem7054139 A) (@lem7054138 A _94157 f n)). Qed.
Lemma lem7054141 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term172 A _94157 f) = (term172 A _94157 f).
Proof. exact (fun_ext (fun n : nat => @lem7054140 A _94157 f n)). Qed.
Lemma lem7054142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054143 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term173 A _94157 f) = (term173 A _94157 f).
Proof. exact (MK_COMB (@lem7054142) (@lem7054141 A _94157 f)). Qed.
Lemma lem7054144 {A : Type'} (_94157 : type701 A) : (term174 A _94157) = (term174 A _94157).
Proof. exact (fun_ext (fun f : A -> nat => @lem7054143 A _94157 f)). Qed.
Lemma lem7054145 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7054146 {A : Type'} (_94157 : type701 A) : (term175 A _94157) = (term175 A _94157).
Proof. exact (MK_COMB (@lem7054145 A) (@lem7054144 A _94157)). Qed.
Lemma lem7054147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054148 {A : Type'} (_94157 : type701 A) : (term176 A _94157) = (term176 A _94157).
Proof. exact (MK_COMB (@lem7054147) (@lem7054146 A _94157)). Qed.
Lemma lem7054149 {A : Type'} (_94157 : type701 A) (_94156 : type1000) : (term177 A _94157 _94156) = (term177 A _94157 _94156).
Proof. exact (MK_COMB (@lem7054148 A _94157) (@lem7054132 _94156)). Qed.
Lemma lem7054150 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem7054151 (m : nat) : (term66 m) = (term66 m).
Proof. exact (fun_ext (fun n : nat => @lem7054150 m n)). Qed.
Lemma lem7054152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054153 (m : nat) : (term67 m) = (term67 m).
Proof. exact (MK_COMB (@lem7054152) (@lem7054151 m)). Qed.
Lemma lem7054154 : term68 = term68.
Proof. exact (fun_ext (fun m : nat => @lem7054153 m)). Qed.
Lemma lem7054155 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054156 : term69 = term69.
Proof. exact (MK_COMB (@lem7054155) (@lem7054154)). Qed.
Lemma lem7054157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054158 : term14 = term14.
Proof. exact (MK_COMB (@lem7054157) (@lem7054156)). Qed.
Lemma lem7054159 {A : Type'} (_94157 : type701 A) (_94156 : type1000) : (term178 A _94157 _94156) = (term178 A _94157 _94156).
Proof. exact (MK_COMB (@lem7054158) (@lem7054149 A _94157 _94156)). Qed.
Lemma lem7054160 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : ((term79 a b f n) = (term77 a b _94156 f n)) = ((term79 a b f n) = (term77 a b _94156 f n)).
Proof. exact (eq_refl ((term79 a b f n) = (term77 a b _94156 f n))). Qed.
Lemma lem7054161 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term81 a b _94156 f) = (term81 a b _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7054160 a b _94156 f n)). Qed.
Lemma lem7054162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054163 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term83 a b _94156 f) = (term83 a b _94156 f).
Proof. exact (MK_COMB (@lem7054162) (@lem7054161 a b _94156 f)). Qed.
Lemma lem7054164 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term85 a _94156 f) = (term85 a _94156 f).
Proof. exact (fun_ext (fun b : nat => @lem7054163 a b _94156 f)). Qed.
Lemma lem7054165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054166 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term87 a _94156 f) = (term87 a _94156 f).
Proof. exact (MK_COMB (@lem7054165) (@lem7054164 a _94156 f)). Qed.
Lemma lem7054167 (_94156 : type1000) (f : nat -> nat) : (term89 _94156 f) = (term89 _94156 f).
Proof. exact (fun_ext (fun a : nat => @lem7054166 a _94156 f)). Qed.
Lemma lem7054168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054169 (_94156 : type1000) (f : nat -> nat) : (term91 _94156 f) = (term91 _94156 f).
Proof. exact (MK_COMB (@lem7054168) (@lem7054167 _94156 f)). Qed.
Lemma lem7054170 (_94156 : type1000) : (term93 _94156) = (term93 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7054169 _94156 f)). Qed.
Lemma lem7054171 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7054172 (_94156 : type1000) : (term94 _94156) = (term94 _94156).
Proof. exact (MK_COMB (@lem7054171) (@lem7054170 _94156)). Qed.
Lemma lem7054173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7054174 (_94156 : type1000) : (term95 _94156) = (term95 _94156).
Proof. exact (MK_COMB (@lem7054173) (@lem7054172 _94156)). Qed.
Lemma lem7054175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054176 (_94156 : type1000) : (term96 _94156) = (term96 _94156).
Proof. exact (MK_COMB (@lem7054175) (@lem7054174 _94156)). Qed.
Lemma lem7054177 {A : Type'} (_94157 : type701 A) (_94156 : type1000) : (term179 A _94157 _94156) = (term179 A _94157 _94156).
Proof. exact (MK_COMB (@lem7054176 _94156) (@lem7054159 A _94157 _94156)). Qed.
Lemma lem7054178 (_94156 : type1000) (f : nat -> nat) (i : nat) (n : nat) : ((_94156 f n i) = (term145 f i n)) = ((_94156 f n i) = (term145 f i n)).
Proof. exact (eq_refl ((_94156 f n i) = (term145 f i n))). Qed.
Lemma lem7054179 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term150 _94156 f n) = (term150 _94156 f n).
Proof. exact (fun_ext (fun i : nat => @lem7054178 _94156 f i n)). Qed.
Lemma lem7054180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054181 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term151 _94156 f n) = (term151 _94156 f n).
Proof. exact (MK_COMB (@lem7054180) (@lem7054179 _94156 f n)). Qed.
Lemma lem7054182 (_94156 : type1000) (f : nat -> nat) : (term152 _94156 f) = (term152 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7054181 _94156 f n)). Qed.
Lemma lem7054183 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054184 (_94156 : type1000) (f : nat -> nat) : (term153 _94156 f) = (term153 _94156 f).
Proof. exact (MK_COMB (@lem7054183) (@lem7054182 _94156 f)). Qed.
Lemma lem7054185 (_94156 : type1000) : (term154 _94156) = (term154 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7054184 _94156 f)). Qed.
Lemma lem7054186 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7054187 (_94156 : type1000) : (term155 _94156) = (term155 _94156).
Proof. exact (MK_COMB (@lem7054186) (@lem7054185 _94156)). Qed.
Lemma lem7054188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054189 (_94156 : type1000) : (term156 _94156) = (term156 _94156).
Proof. exact (MK_COMB (@lem7054188) (@lem7054187 _94156)). Qed.
Lemma lem7054190 {A : Type'} (_94157 : type701 A) (_94156 : type1000) : (term180 A _94157 _94156) = (term180 A _94157 _94156).
Proof. exact (MK_COMB (@lem7054189 _94156) (@lem7054177 A _94157 _94156)). Qed.
Lemma lem7054191 {A : Type'} (_94157 : type701 A) : (term181 A _94157) = (term181 A _94157).
Proof. exact (fun_ext (fun _94156 : type1000 => @lem7054190 A _94157 _94156)). Qed.
Lemma lem7054192 : (@all ((nat -> nat) -> nat -> nat -> nat)) = (@all ((nat -> nat) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@all ((nat -> nat) -> nat -> nat -> nat))). Qed.
Lemma lem7054193 {A : Type'} (_94157 : type701 A) : (term182 A _94157) = (term182 A _94157).
Proof. exact (MK_COMB (@lem7054192) (@lem7054191 A _94157)). Qed.
Lemma lem7054194 {A : Type'} (_94157 : type701 A) (f : A -> nat) (i : A) (n : nat) : ((_94157 f n i) = (term49 A f i n)) = ((_94157 f n i) = (term49 A f i n)).
Proof. exact (eq_refl ((_94157 f n i) = (term49 A f i n))). Qed.
Lemma lem7054195 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term231 A _94157 f n) = (term231 A _94157 f n).
Proof. exact (fun_ext (fun i : A => @lem7054194 A _94157 f i n)). Qed.
Lemma lem7054196 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7054197 {A : Type'} (_94157 : type701 A) (f : A -> nat) (n : nat) : (term232 A _94157 f n) = (term232 A _94157 f n).
Proof. exact (MK_COMB (@lem7054196 A) (@lem7054195 A _94157 f n)). Qed.
Lemma lem7054198 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term233 A _94157 f) = (term233 A _94157 f).
Proof. exact (fun_ext (fun n : nat => @lem7054197 A _94157 f n)). Qed.
Lemma lem7054199 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054200 {A : Type'} (_94157 : type701 A) (f : A -> nat) : (term234 A _94157 f) = (term234 A _94157 f).
Proof. exact (MK_COMB (@lem7054199) (@lem7054198 A _94157 f)). Qed.
Lemma lem7054201 {A : Type'} (_94157 : type701 A) : (term235 A _94157) = (term235 A _94157).
Proof. exact (fun_ext (fun f : A -> nat => @lem7054200 A _94157 f)). Qed.
Lemma lem7054202 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7054203 {A : Type'} (_94157 : type701 A) : (term236 A _94157) = (term236 A _94157).
Proof. exact (MK_COMB (@lem7054202 A) (@lem7054201 A _94157)). Qed.
Lemma lem7054204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7054205 {A : Type'} (_94157 : type701 A) : (term237 A _94157) = (term237 A _94157).
Proof. exact (MK_COMB (@lem7054204) (@lem7054203 A _94157)). Qed.
Lemma lem7054206 {A : Type'} (_94157 : type701 A) : (term238 A _94157) = (term238 A _94157).
Proof. exact (MK_COMB (@lem7054205 A _94157) (@lem7054193 A _94157)). Qed.
Lemma lem7054207 {A : Type'} : (term239 A) = (term239 A).
Proof. exact (fun_ext (fun _94157 : type701 A => @lem7054206 A _94157)). Qed.
Lemma lem7054208 {A : Type'} : (@all ((A -> nat) -> nat -> A -> nat)) = (@all ((A -> nat) -> nat -> A -> nat)).
Proof. exact (eq_refl (@all ((A -> nat) -> nat -> A -> nat))). Qed.
Lemma lem7054209 {A : Type'} : (term240 A) = (term240 A).
Proof. exact (MK_COMB (@lem7054208 A) (@lem7054207 A)). Qed.
Lemma lem7054346 {A : Type'} : (term5 A) = (term240 A).
Proof. exact (TRANS (@lem7054116 A) (@lem7054209 A)). Qed.
Lemma lem7054347 {A : Type'} : (term240 A) = (term5 A).
Proof. exact (SYM (@lem7054346 A)). Qed.
Lemma lem7054350 (_94156 : type1000) (h1 : term95 _94156) : term95 _94156.
Proof. exact (h1). Qed.
Lemma lem7054351 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem7054353 (_94156 : type1000) (h1 : term47 _94156) : term47 _94156.
Proof. exact (h1). Qed.
Lemma lem7054409 (P : nat -> Prop) : (term241 P) = (term242 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7054410 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term243 a b _94156 f) = (term244 a b _94156 f).
Proof. exact (@lem7054409 (term81 a b _94156 f)). Qed.
Lemma lem7054411 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term245 a b _94156 f n) = ((term79 a b f n) = (term77 a b _94156 f n)).
Proof. exact (eq_refl (term245 a b _94156 f n)). Qed.
Lemma lem7054412 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7054414 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term246 a b _94156 f n) = (term247 a b _94156 f n).
Proof. exact (MK_COMB (@lem7054412) (@lem7054411 a b _94156 f n)). Qed.
Lemma lem7054415 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term248 a b _94156 f) = (term249 a b _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7054414 a b _94156 f n)). Qed.
Lemma lem7054416 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7054417 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term244 a b _94156 f) = (term250 a b _94156 f).
Proof. exact (MK_COMB (@lem7054416) (@lem7054415 a b _94156 f)). Qed.
Lemma lem7054418 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term243 a b _94156 f) = (term250 a b _94156 f).
Proof. exact (TRANS (@lem7054410 a b _94156 f) (@lem7054417 a b _94156 f)). Qed.
Lemma lem7054419 (P : nat -> Prop) : (term241 P) = (term242 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7054420 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term251 a _94156 f) = (term252 a _94156 f).
Proof. exact (@lem7054419 (term85 a _94156 f)). Qed.
Lemma lem7054421 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term253 a _94156 f b) = (term83 a b _94156 f).
Proof. exact (eq_refl (term253 a _94156 f b)). Qed.
Lemma lem7054422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7054423 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term254 a _94156 f b) = (term243 a b _94156 f).
Proof. exact (MK_COMB (@lem7054422) (@lem7054421 a b _94156 f)). Qed.
Lemma lem7054424 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) : (term254 a _94156 f b) = (term250 a b _94156 f).
Proof. exact (TRANS (@lem7054423 a b _94156 f) (@lem7054418 a b _94156 f)). Qed.
Lemma lem7054425 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term255 a _94156 f) = (term256 a _94156 f).
Proof. exact (fun_ext (fun b : nat => @lem7054424 a b _94156 f)). Qed.
Lemma lem7054426 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7054427 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term252 a _94156 f) = (term257 a _94156 f).
Proof. exact (MK_COMB (@lem7054426) (@lem7054425 a _94156 f)). Qed.
Lemma lem7054428 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term251 a _94156 f) = (term257 a _94156 f).
Proof. exact (TRANS (@lem7054420 a _94156 f) (@lem7054427 a _94156 f)). Qed.
Lemma lem7054429 (P : nat -> Prop) : (term241 P) = (term242 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7054430 (_94156 : type1000) (f : nat -> nat) : (term258 _94156 f) = (term259 _94156 f).
Proof. exact (@lem7054429 (term89 _94156 f)). Qed.
Lemma lem7054431 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term260 _94156 f a) = (term87 a _94156 f).
Proof. exact (eq_refl (term260 _94156 f a)). Qed.
Lemma lem7054432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7054433 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term261 _94156 f a) = (term251 a _94156 f).
Proof. exact (MK_COMB (@lem7054432) (@lem7054431 a _94156 f)). Qed.
Lemma lem7054434 (a : nat) (_94156 : type1000) (f : nat -> nat) : (term261 _94156 f a) = (term257 a _94156 f).
Proof. exact (TRANS (@lem7054433 a _94156 f) (@lem7054428 a _94156 f)). Qed.
Lemma lem7054435 (_94156 : type1000) (f : nat -> nat) : (term262 _94156 f) = (term263 _94156 f).
Proof. exact (fun_ext (fun a : nat => @lem7054434 a _94156 f)). Qed.
Lemma lem7054436 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7054437 (_94156 : type1000) (f : nat -> nat) : (term259 _94156 f) = (term264 _94156 f).
Proof. exact (MK_COMB (@lem7054436) (@lem7054435 _94156 f)). Qed.
Lemma lem7054438 (_94156 : type1000) (f : nat -> nat) : (term258 _94156 f) = (term264 _94156 f).
Proof. exact (TRANS (@lem7054430 _94156 f) (@lem7054437 _94156 f)). Qed.
Lemma lem7054439 (P : type1002) : (term265 P) = (term266 P).
Proof. exact (@lem18392 (nat -> nat) P). Qed.
Lemma lem7054440 (_94156 : type1000) : (term95 _94156) = (term267 _94156).
Proof. exact (@lem7054439 (term93 _94156)). Qed.
Lemma lem7054441 (_94156 : type1000) (f : nat -> nat) : (term268 _94156 f) = (term91 _94156 f).
Proof. exact (eq_refl (term268 _94156 f)). Qed.
Lemma lem7054442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7054443 (_94156 : type1000) (f : nat -> nat) : (term269 _94156 f) = (term258 _94156 f).
Proof. exact (MK_COMB (@lem7054442) (@lem7054441 _94156 f)). Qed.
Lemma lem7054444 (_94156 : type1000) (f : nat -> nat) : (term269 _94156 f) = (term264 _94156 f).
Proof. exact (TRANS (@lem7054443 _94156 f) (@lem7054438 _94156 f)). Qed.
Lemma lem7054445 (_94156 : type1000) : (term270 _94156) = (term271 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7054444 _94156 f)). Qed.
Lemma lem7054446 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7054447 (_94156 : type1000) : (term267 _94156) = (term272 _94156).
Proof. exact (MK_COMB (@lem7054446) (@lem7054445 _94156)). Qed.
Lemma lem7054468 (_94156 : type1000) : (term95 _94156) = (term272 _94156).
Proof. exact (TRANS (@lem7054440 _94156) (@lem7054447 _94156)). Qed.
Lemma lem7054469 (_94156 : type1000) (h1 : term95 _94156) : term272 _94156.
Proof. exact (EQ_MP (@lem7054468 _94156) (@lem7054350 _94156 h1)). Qed.
Lemma lem7054470 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem7054471 (m : nat) : (term66 m) = (term66 m).
Proof. exact (fun_ext (fun n : nat => @lem7054470 m n)). Qed.
Lemma lem7054472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054473 (m : nat) : (term67 m) = (term67 m).
Proof. exact (MK_COMB (@lem7054472) (@lem7054471 m)). Qed.
Lemma lem7054474 : term68 = term68.
Proof. exact (fun_ext (fun m : nat => @lem7054473 m)). Qed.
Lemma lem7054475 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054488 : term69 = term69.
Proof. exact (MK_COMB (@lem7054475) (@lem7054474)). Qed.
Lemma lem7054489 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem7054488) (@lem7054351 h1)). Qed.
Lemma lem7054573 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term36 s _94156 f n) = (term273 s _94156 f n).
Proof. exact (@lem17265 (@FINITE nat s) ((term33 s f n) = (term31 s _94156 f n))). Qed.
Lemma lem7054574 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term38 _94156 f n) = (term274 _94156 f n).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7054573 s _94156 f n)). Qed.
Lemma lem7054575 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7054576 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term40 _94156 f n) = (term275 _94156 f n).
Proof. exact (MK_COMB (@lem7054575) (@lem7054574 _94156 f n)). Qed.
Lemma lem7054577 (_94156 : type1000) (f : nat -> nat) : (term42 _94156 f) = (term276 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7054576 _94156 f n)). Qed.
Lemma lem7054578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054579 (_94156 : type1000) (f : nat -> nat) : (term44 _94156 f) = (term277 _94156 f).
Proof. exact (MK_COMB (@lem7054578) (@lem7054577 _94156 f)). Qed.
Lemma lem7054580 (_94156 : type1000) : (term46 _94156) = (term278 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7054579 _94156 f)). Qed.
Lemma lem7054581 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7054642 (_94156 : type1000) : (term47 _94156) = (term279 _94156).
Proof. exact (MK_COMB (@lem7054581) (@lem7054580 _94156)). Qed.
Lemma lem7054643 (_94156 : type1000) (h1 : term47 _94156) : term279 _94156.
Proof. exact (EQ_MP (@lem7054642 _94156) (@lem7054353 _94156 h1)). Qed.
Lemma lem7054644 (_94156 : type1000) (f : nat -> nat) (h1 : term264 _94156 f) : term264 _94156 f.
Proof. exact (h1). Qed.
Lemma lem7054645 (a : nat) (_94156 : type1000) (f : nat -> nat) (h1 : term257 a _94156 f) : term257 a _94156 f.
Proof. exact (h1). Qed.
Lemma lem7054646 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (h1 : term250 a b _94156 f) : term250 a b _94156 f.
Proof. exact (h1). Qed.
Lemma lem7054647 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) (h1 : term247 a b _94156 f n) : term247 a b _94156 f n.
Proof. exact (h1). Qed.
Lemma lem7054774 : (@FINITE nat) = (@FINITE nat).
Proof. exact (eq_refl (@FINITE nat)). Qed.
Lemma lem7054781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054782 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7054781 nat type1605 f x). Qed.
Lemma lem7054783 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7054782 dotdot m). Qed.
Lemma lem7054784 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7054785 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7054783 m) (@lem7054784 n)). Qed.
Lemma lem7054787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054788 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7054787 nat (nat -> Prop) f x). Qed.
Lemma lem7054789 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term280 m n).
Proof. exact (@lem7054788 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7054791 (m : nat) (n : nat) : (dotdot m n) = (term280 m n).
Proof. exact (TRANS (@lem7054785 m n) (@lem7054789 m n)). Qed.
Lemma lem7054792 (m : nat) (n : nat) : (term65 m n) = (term281 m n).
Proof. exact (MK_COMB (@lem7054774) (@lem7054791 m n)). Qed.
Lemma lem7054794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054795 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7054794 (nat -> Prop) Prop f x). Qed.
Lemma lem7054796 (m : nat) (n : nat) : (term281 m n) = (term282 m n).
Proof. exact (@lem7054795 (@FINITE nat) (term280 m n)). Qed.
Lemma lem7054797 (m : nat) (n : nat) : (term65 m n) = (term282 m n).
Proof. exact (TRANS (@lem7054792 m n) (@lem7054796 m n)). Qed.
Lemma lem7054798 (m : nat) : (term66 m) = (term283 m).
Proof. exact (fun_ext (fun n : nat => @lem7054797 m n)). Qed.
Lemma lem7054799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054800 (m : nat) : (term67 m) = (term284 m).
Proof. exact (MK_COMB (@lem7054799) (@lem7054798 m)). Qed.
Lemma lem7054801 : term68 = term285.
Proof. exact (fun_ext (fun m : nat => @lem7054800 m)). Qed.
Lemma lem7054802 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7054803 : term69 = term286.
Proof. exact (MK_COMB (@lem7054802) (@lem7054801)). Qed.
Lemma lem7054804 (h1 : term69) : term286.
Proof. exact (EQ_MP (@lem7054803) (@lem7054489 h1)). Qed.
Lemma lem7054913 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7054914 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7054921 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054922 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7054921 (nat -> Prop) type1003 f x). Qed.
Lemma lem7054923 (s : nat -> Prop) : (@nsum nat s) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s).
Proof. exact (@lem7054922 (@nsum nat) s). Qed.
Lemma lem7054924 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7054925 (s : nat -> Prop) (f : nat -> nat) : (@nsum nat s f) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s f).
Proof. exact (MK_COMB (@lem7054923 s) (@lem7054924 f)). Qed.
Lemma lem7054927 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054928 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7054927 (nat -> nat) nat f x). Qed.
Lemma lem7054929 (s : nat -> Prop) (f : nat -> nat) : (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s f) = (term287 s f).
Proof. exact (@lem7054928 (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s) f). Qed.
Lemma lem7054931 (s : nat -> Prop) (f : nat -> nat) : (@nsum nat s f) = (term287 s f).
Proof. exact (TRANS (@lem7054925 s f) (@lem7054929 s f)). Qed.
Lemma lem7054932 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7054933 (s : nat -> Prop) (f : nat -> nat) : (term288 s f) = (term289 s f).
Proof. exact (MK_COMB (@lem7054914) (@lem7054931 s f)). Qed.
Lemma lem7054934 (s : nat -> Prop) (f : nat -> nat) (n : nat) : (term33 s f n) = (term290 s f n).
Proof. exact (MK_COMB (@lem7054933 s f) (@lem7054932 n)). Qed.
Lemma lem7054936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054937 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7054936 nat (nat -> nat) f x). Qed.
Lemma lem7054938 (s : nat -> Prop) (f : nat -> nat) : (term289 s f) = (term291 s f).
Proof. exact (@lem7054937 Nat.modulo (term287 s f)). Qed.
Lemma lem7054939 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7054940 (s : nat -> Prop) (f : nat -> nat) (n : nat) : (term290 s f n) = (term292 s f n).
Proof. exact (MK_COMB (@lem7054938 s f) (@lem7054939 n)). Qed.
Lemma lem7054942 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054943 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7054942 nat nat f x). Qed.
Lemma lem7054944 (s : nat -> Prop) (f : nat -> nat) (n : nat) : (term292 s f n) = (term293 s f n).
Proof. exact (@lem7054943 (term291 s f) n). Qed.
Lemma lem7054945 (s : nat -> Prop) (f : nat -> nat) (n : nat) : (term290 s f n) = (term293 s f n).
Proof. exact (TRANS (@lem7054940 s f n) (@lem7054944 s f n)). Qed.
Lemma lem7054946 (s : nat -> Prop) (f : nat -> nat) (n : nat) : (term33 s f n) = (term293 s f n).
Proof. exact (TRANS (@lem7054934 s f n) (@lem7054945 s f n)). Qed.
Lemma lem7054947 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7054956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054957 (f : type1000) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat -> nat -> nat) f x).
Proof. exact (@lem7054956 (nat -> nat) type1606 f x). Qed.
Lemma lem7054958 (_94156 : type1000) (f : nat -> nat) : (_94156 f) = (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f).
Proof. exact (@lem7054957 _94156 f). Qed.
Lemma lem7054959 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7054960 (_94156 : type1000) (f : nat -> nat) (n : nat) : (_94156 f n) = (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f n).
Proof. exact (MK_COMB (@lem7054958 _94156 f) (@lem7054959 n)). Qed.
Lemma lem7054962 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054963 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7054962 nat (nat -> nat) f x). Qed.
Lemma lem7054964 (_94156 : type1000) (f : nat -> nat) (n : nat) : (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f n) = (term294 _94156 f n).
Proof. exact (@lem7054963 (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f) n). Qed.
Lemma lem7054966 (_94156 : type1000) (f : nat -> nat) (n : nat) : (_94156 f n) = (term294 _94156 f n).
Proof. exact (TRANS (@lem7054960 _94156 f n) (@lem7054964 _94156 f n)). Qed.
Lemma lem7054967 (s : nat -> Prop) : (@nsum nat s) = (@nsum nat s).
Proof. exact (eq_refl (@nsum nat s)). Qed.
Lemma lem7054968 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term27 s _94156 f n) = (term295 s _94156 f n).
Proof. exact (MK_COMB (@lem7054967 s) (@lem7054966 _94156 f n)). Qed.
Lemma lem7054970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054971 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7054970 (nat -> Prop) type1003 f x). Qed.
Lemma lem7054972 (s : nat -> Prop) : (@nsum nat s) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s).
Proof. exact (@lem7054971 (@nsum nat) s). Qed.
Lemma lem7054973 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term294 _94156 f n) = (term294 _94156 f n).
Proof. exact (eq_refl (term294 _94156 f n)). Qed.
Lemma lem7054974 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term295 s _94156 f n) = (term296 s _94156 f n).
Proof. exact (MK_COMB (@lem7054972 s) (@lem7054973 _94156 f n)). Qed.
Lemma lem7054976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054977 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7054976 (nat -> nat) nat f x). Qed.
Lemma lem7054978 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term296 s _94156 f n) = (term297 s _94156 f n).
Proof. exact (@lem7054977 (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s) (term294 _94156 f n)). Qed.
Lemma lem7054979 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term295 s _94156 f n) = (term297 s _94156 f n).
Proof. exact (TRANS (@lem7054974 s _94156 f n) (@lem7054978 s _94156 f n)). Qed.
Lemma lem7054980 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term27 s _94156 f n) = (term297 s _94156 f n).
Proof. exact (TRANS (@lem7054968 s _94156 f n) (@lem7054979 s _94156 f n)). Qed.
Lemma lem7054981 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7054982 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term29 s _94156 f n) = (term298 s _94156 f n).
Proof. exact (MK_COMB (@lem7054947) (@lem7054980 s _94156 f n)). Qed.
Lemma lem7054983 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term31 s _94156 f n) = (term299 s _94156 f n).
Proof. exact (MK_COMB (@lem7054982 s _94156 f n) (@lem7054981 n)). Qed.
Lemma lem7054985 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054986 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7054985 nat (nat -> nat) f x). Qed.
Lemma lem7054987 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term298 s _94156 f n) = (term300 s _94156 f n).
Proof. exact (@lem7054986 Nat.modulo (term297 s _94156 f n)). Qed.
Lemma lem7054988 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7054989 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term299 s _94156 f n) = (term301 s _94156 f n).
Proof. exact (MK_COMB (@lem7054987 s _94156 f n) (@lem7054988 n)). Qed.
Lemma lem7054991 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7054992 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7054991 nat nat f x). Qed.
Lemma lem7054993 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term301 s _94156 f n) = (term302 s _94156 f n).
Proof. exact (@lem7054992 (term300 s _94156 f n) n). Qed.
Lemma lem7054994 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term299 s _94156 f n) = (term302 s _94156 f n).
Proof. exact (TRANS (@lem7054989 s _94156 f n) (@lem7054993 s _94156 f n)). Qed.
Lemma lem7054995 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term31 s _94156 f n) = (term302 s _94156 f n).
Proof. exact (TRANS (@lem7054983 s _94156 f n) (@lem7054994 s _94156 f n)). Qed.
Lemma lem7054996 (s : nat -> Prop) (f : nat -> nat) (n : nat) : (term32 s f n) = (term303 s f n).
Proof. exact (MK_COMB (@lem7054913) (@lem7054946 s f n)). Qed.
Lemma lem7054997 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : ((term33 s f n) = (term31 s _94156 f n)) = ((term293 s f n) = (term302 s _94156 f n)).
Proof. exact (MK_COMB (@lem7054996 s f n) (@lem7054995 s _94156 f n)). Qed.
Lemma lem7054998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7055003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055004 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7055003 (nat -> Prop) Prop f x). Qed.
Lemma lem7055006 (s : nat -> Prop) : (@FINITE nat s) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) s).
Proof. exact (@lem7055004 (@FINITE nat) s). Qed.
Lemma lem7055007 (s : nat -> Prop) : (term304 s) = (term305 s).
Proof. exact (MK_COMB (@lem7054998) (@lem7055006 s)). Qed.
Lemma lem7055008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7055009 (s : nat -> Prop) : (term306 s) = (term307 s).
Proof. exact (MK_COMB (@lem7055008) (@lem7055007 s)). Qed.
Lemma lem7055010 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term273 s _94156 f n) = (term308 s _94156 f n).
Proof. exact (MK_COMB (@lem7055009 s) (@lem7054997 s _94156 f n)). Qed.
Lemma lem7055011 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term274 _94156 f n) = (term309 _94156 f n).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7055010 s _94156 f n)). Qed.
Lemma lem7055012 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7055013 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term275 _94156 f n) = (term310 _94156 f n).
Proof. exact (MK_COMB (@lem7055012) (@lem7055011 _94156 f n)). Qed.
Lemma lem7055014 (_94156 : type1000) (f : nat -> nat) : (term276 _94156 f) = (term311 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7055013 _94156 f n)). Qed.
Lemma lem7055015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7055016 (_94156 : type1000) (f : nat -> nat) : (term277 _94156 f) = (term312 _94156 f).
Proof. exact (MK_COMB (@lem7055015) (@lem7055014 _94156 f)). Qed.
Lemma lem7055017 (_94156 : type1000) : (term278 _94156) = (term313 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7055016 _94156 f)). Qed.
Lemma lem7055018 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7055019 (_94156 : type1000) : (term279 _94156) = (term314 _94156).
Proof. exact (MK_COMB (@lem7055018) (@lem7055017 _94156)). Qed.
Lemma lem7055020 (_94156 : type1000) (h1 : term47 _94156) : term314 _94156.
Proof. exact (EQ_MP (@lem7055019 _94156) (@lem7054643 _94156 h1)). Qed.
Lemma lem7055021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7055022 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7055023 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7055024 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7055031 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055032 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7055031 nat type1605 f x). Qed.
Lemma lem7055033 (a : nat) : (dotdot a) = (@I (nat -> nat -> nat -> Prop) dotdot a).
Proof. exact (@lem7055032 dotdot a). Qed.
Lemma lem7055034 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7055035 (a : nat) (b : nat) : (dotdot a b) = (@I (nat -> nat -> nat -> Prop) dotdot a b).
Proof. exact (MK_COMB (@lem7055033 a) (@lem7055034 b)). Qed.
Lemma lem7055037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055038 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7055037 nat (nat -> Prop) f x). Qed.
Lemma lem7055039 (a : nat) (b : nat) : (@I (nat -> nat -> nat -> Prop) dotdot a b) = (term280 a b).
Proof. exact (@lem7055038 (@I (nat -> nat -> nat -> Prop) dotdot a) b). Qed.
Lemma lem7055041 (a : nat) (b : nat) : (dotdot a b) = (term280 a b).
Proof. exact (TRANS (@lem7055035 a b) (@lem7055039 a b)). Qed.
Lemma lem7055042 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7055043 (a : nat) (b : nat) : (term71 a b) = (term315 a b).
Proof. exact (MK_COMB (@lem7055024) (@lem7055041 a b)). Qed.
Lemma lem7055044 (a : nat) (b : nat) (f : nat -> nat) : (term316 a b f) = (term317 a b f).
Proof. exact (MK_COMB (@lem7055043 a b) (@lem7055042 f)). Qed.
Lemma lem7055046 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055047 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7055046 (nat -> Prop) type1003 f x). Qed.
Lemma lem7055048 (a : nat) (b : nat) : (term315 a b) = (term318 a b).
Proof. exact (@lem7055047 (@nsum nat) (term280 a b)). Qed.
Lemma lem7055049 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7055050 (a : nat) (b : nat) (f : nat -> nat) : (term317 a b f) = (term319 a b f).
Proof. exact (MK_COMB (@lem7055048 a b) (@lem7055049 f)). Qed.
Lemma lem7055052 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055053 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7055052 (nat -> nat) nat f x). Qed.
Lemma lem7055054 (a : nat) (b : nat) (f : nat -> nat) : (term319 a b f) = (term320 a b f).
Proof. exact (@lem7055053 (term318 a b) f). Qed.
Lemma lem7055055 (a : nat) (b : nat) (f : nat -> nat) : (term317 a b f) = (term320 a b f).
Proof. exact (TRANS (@lem7055050 a b f) (@lem7055054 a b f)). Qed.
Lemma lem7055056 (a : nat) (b : nat) (f : nat -> nat) : (term316 a b f) = (term320 a b f).
Proof. exact (TRANS (@lem7055044 a b f) (@lem7055055 a b f)). Qed.
Lemma lem7055057 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7055058 (a : nat) (b : nat) (f : nat -> nat) : (term321 a b f) = (term322 a b f).
Proof. exact (MK_COMB (@lem7055023) (@lem7055056 a b f)). Qed.
Lemma lem7055059 (a : nat) (b : nat) (f : nat -> nat) (n : nat) : (term79 a b f n) = (term323 a b f n).
Proof. exact (MK_COMB (@lem7055058 a b f) (@lem7055057 n)). Qed.
Lemma lem7055061 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055062 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7055061 nat (nat -> nat) f x). Qed.
Lemma lem7055063 (a : nat) (b : nat) (f : nat -> nat) : (term322 a b f) = (term324 a b f).
Proof. exact (@lem7055062 Nat.modulo (term320 a b f)). Qed.
Lemma lem7055064 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7055065 (a : nat) (b : nat) (f : nat -> nat) (n : nat) : (term323 a b f n) = (term325 a b f n).
Proof. exact (MK_COMB (@lem7055063 a b f) (@lem7055064 n)). Qed.
Lemma lem7055067 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055068 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7055067 nat nat f x). Qed.
Lemma lem7055069 (a : nat) (b : nat) (f : nat -> nat) (n : nat) : (term325 a b f n) = (term326 a b f n).
Proof. exact (@lem7055068 (term324 a b f) n). Qed.
Lemma lem7055070 (a : nat) (b : nat) (f : nat -> nat) (n : nat) : (term323 a b f n) = (term326 a b f n).
Proof. exact (TRANS (@lem7055065 a b f n) (@lem7055069 a b f n)). Qed.
Lemma lem7055071 (a : nat) (b : nat) (f : nat -> nat) (n : nat) : (term79 a b f n) = (term326 a b f n).
Proof. exact (TRANS (@lem7055059 a b f n) (@lem7055070 a b f n)). Qed.
Lemma lem7055072 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7055073 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7055080 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055081 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7055080 nat type1605 f x). Qed.
Lemma lem7055082 (a : nat) : (dotdot a) = (@I (nat -> nat -> nat -> Prop) dotdot a).
Proof. exact (@lem7055081 dotdot a). Qed.
Lemma lem7055083 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7055084 (a : nat) (b : nat) : (dotdot a b) = (@I (nat -> nat -> nat -> Prop) dotdot a b).
Proof. exact (MK_COMB (@lem7055082 a) (@lem7055083 b)). Qed.
Lemma lem7055086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055087 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7055086 nat (nat -> Prop) f x). Qed.
Lemma lem7055088 (a : nat) (b : nat) : (@I (nat -> nat -> nat -> Prop) dotdot a b) = (term280 a b).
Proof. exact (@lem7055087 (@I (nat -> nat -> nat -> Prop) dotdot a) b). Qed.
Lemma lem7055090 (a : nat) (b : nat) : (dotdot a b) = (term280 a b).
Proof. exact (TRANS (@lem7055084 a b) (@lem7055088 a b)). Qed.
Lemma lem7055097 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055098 (f : type1000) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat -> nat -> nat) f x).
Proof. exact (@lem7055097 (nat -> nat) type1606 f x). Qed.
Lemma lem7055099 (_94156 : type1000) (f : nat -> nat) : (_94156 f) = (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f).
Proof. exact (@lem7055098 _94156 f). Qed.
Lemma lem7055100 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7055101 (_94156 : type1000) (f : nat -> nat) (n : nat) : (_94156 f n) = (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f n).
Proof. exact (MK_COMB (@lem7055099 _94156 f) (@lem7055100 n)). Qed.
Lemma lem7055103 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055104 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7055103 nat (nat -> nat) f x). Qed.
Lemma lem7055105 (_94156 : type1000) (f : nat -> nat) (n : nat) : (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f n) = (term294 _94156 f n).
Proof. exact (@lem7055104 (@I ((nat -> nat) -> nat -> nat -> nat) _94156 f) n). Qed.
Lemma lem7055107 (_94156 : type1000) (f : nat -> nat) (n : nat) : (_94156 f n) = (term294 _94156 f n).
Proof. exact (TRANS (@lem7055101 _94156 f n) (@lem7055105 _94156 f n)). Qed.
Lemma lem7055108 (a : nat) (b : nat) : (term71 a b) = (term315 a b).
Proof. exact (MK_COMB (@lem7055073) (@lem7055090 a b)). Qed.
Lemma lem7055109 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term73 a b _94156 f n) = (term327 a b _94156 f n).
Proof. exact (MK_COMB (@lem7055108 a b) (@lem7055107 _94156 f n)). Qed.
Lemma lem7055111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055112 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7055111 (nat -> Prop) type1003 f x). Qed.
Lemma lem7055113 (a : nat) (b : nat) : (term315 a b) = (term318 a b).
Proof. exact (@lem7055112 (@nsum nat) (term280 a b)). Qed.
Lemma lem7055114 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term294 _94156 f n) = (term294 _94156 f n).
Proof. exact (eq_refl (term294 _94156 f n)). Qed.
Lemma lem7055115 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term327 a b _94156 f n) = (term328 a b _94156 f n).
Proof. exact (MK_COMB (@lem7055113 a b) (@lem7055114 _94156 f n)). Qed.
Lemma lem7055117 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055118 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7055117 (nat -> nat) nat f x). Qed.
Lemma lem7055119 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term328 a b _94156 f n) = (term329 a b _94156 f n).
Proof. exact (@lem7055118 (term318 a b) (term294 _94156 f n)). Qed.
Lemma lem7055120 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term327 a b _94156 f n) = (term329 a b _94156 f n).
Proof. exact (TRANS (@lem7055115 a b _94156 f n) (@lem7055119 a b _94156 f n)). Qed.
Lemma lem7055121 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term73 a b _94156 f n) = (term329 a b _94156 f n).
Proof. exact (TRANS (@lem7055109 a b _94156 f n) (@lem7055120 a b _94156 f n)). Qed.
Lemma lem7055122 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7055123 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term75 a b _94156 f n) = (term330 a b _94156 f n).
Proof. exact (MK_COMB (@lem7055072) (@lem7055121 a b _94156 f n)). Qed.
Lemma lem7055124 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term77 a b _94156 f n) = (term331 a b _94156 f n).
Proof. exact (MK_COMB (@lem7055123 a b _94156 f n) (@lem7055122 n)). Qed.
Lemma lem7055126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055127 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7055126 nat (nat -> nat) f x). Qed.
Lemma lem7055128 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term330 a b _94156 f n) = (term332 a b _94156 f n).
Proof. exact (@lem7055127 Nat.modulo (term329 a b _94156 f n)). Qed.
Lemma lem7055129 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7055130 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term331 a b _94156 f n) = (term333 a b _94156 f n).
Proof. exact (MK_COMB (@lem7055128 a b _94156 f n) (@lem7055129 n)). Qed.
Lemma lem7055132 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7055133 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7055132 nat nat f x). Qed.
Lemma lem7055134 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term333 a b _94156 f n) = (term334 a b _94156 f n).
Proof. exact (@lem7055133 (term332 a b _94156 f n) n). Qed.
Lemma lem7055135 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term331 a b _94156 f n) = (term334 a b _94156 f n).
Proof. exact (TRANS (@lem7055130 a b _94156 f n) (@lem7055134 a b _94156 f n)). Qed.
Lemma lem7055136 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term77 a b _94156 f n) = (term334 a b _94156 f n).
Proof. exact (TRANS (@lem7055124 a b _94156 f n) (@lem7055135 a b _94156 f n)). Qed.
Lemma lem7055137 (a : nat) (b : nat) (f : nat -> nat) (n : nat) : (term78 a b f n) = (term335 a b f n).
Proof. exact (MK_COMB (@lem7055022) (@lem7055071 a b f n)). Qed.
Lemma lem7055138 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : ((term79 a b f n) = (term77 a b _94156 f n)) = ((term326 a b f n) = (term334 a b _94156 f n)).
Proof. exact (MK_COMB (@lem7055137 a b f n) (@lem7055136 a b _94156 f n)). Qed.
Lemma lem7055139 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term247 a b _94156 f n) = (term336 a b _94156 f n).
Proof. exact (MK_COMB (@lem7055021) (@lem7055138 a b _94156 f n)). Qed.
Lemma lem7055168 (m : nat) (n : nat) : (term282 m n) = (term282 m n).
Proof. exact (eq_refl (term282 m n)). Qed.
Lemma lem7055169 (m : nat) : (term283 m) = (term283 m).
Proof. exact (fun_ext (fun n : nat => @lem7055168 m n)). Qed.
Lemma lem7055170 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7055171 (m : nat) : (term284 m) = (term284 m).
Proof. exact (MK_COMB (@lem7055170) (@lem7055169 m)). Qed.
Lemma lem7055172 : term285 = term285.
Proof. exact (fun_ext (fun m : nat => @lem7055171 m)). Qed.
Lemma lem7055173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7055175 : term286 = term286.
Proof. exact (MK_COMB (@lem7055173) (@lem7055172)). Qed.
Lemma lem7055176 (h1 : term69) : term286.
Proof. exact (EQ_MP (@lem7055175) (@lem7054804 h1)). Qed.
Lemma lem7055203 (s : nat -> Prop) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term308 s _94156 f n) = (term308 s _94156 f n).
Proof. exact (eq_refl (term308 s _94156 f n)). Qed.
Lemma lem7055204 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term309 _94156 f n) = (term309 _94156 f n).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7055203 s _94156 f n)). Qed.
Lemma lem7055205 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7055206 (_94156 : type1000) (f : nat -> nat) (n : nat) : (term310 _94156 f n) = (term310 _94156 f n).
Proof. exact (MK_COMB (@lem7055205) (@lem7055204 _94156 f n)). Qed.
Lemma lem7055207 (_94156 : type1000) (f : nat -> nat) : (term311 _94156 f) = (term311 _94156 f).
Proof. exact (fun_ext (fun n : nat => @lem7055206 _94156 f n)). Qed.
Lemma lem7055208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7055209 (_94156 : type1000) (f : nat -> nat) : (term312 _94156 f) = (term312 _94156 f).
Proof. exact (MK_COMB (@lem7055208) (@lem7055207 _94156 f)). Qed.
Lemma lem7055210 (_94156 : type1000) : (term313 _94156) = (term313 _94156).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7055209 _94156 f)). Qed.
Lemma lem7055211 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7055213 (_94156 : type1000) : (term314 _94156) = (term314 _94156).
Proof. exact (MK_COMB (@lem7055211) (@lem7055210 _94156)). Qed.
Lemma lem7055214 (_94156 : type1000) (h1 : term47 _94156) : term314 _94156.
Proof. exact (EQ_MP (@lem7055213 _94156) (@lem7055020 _94156 h1)). Qed.
Lemma lem7055237 (_94164 : nat) (h1 : term69) : term337 _94164.
Proof. exact (@lem7055176 h1 _94164). Qed.
Lemma lem7055238 (_94164 : nat) : (term337 _94164) = (term284 _94164).
Proof. exact (eq_refl (term337 _94164)). Qed.
Lemma lem7055239 (_94164 : nat) (h1 : term69) : term284 _94164.
Proof. exact (EQ_MP (@lem7055238 _94164) (@lem7055237 _94164 h1)). Qed.
Lemma lem7055240 (_94164 : nat) (_94165 : nat) (h1 : term69) : term338 _94164 _94165.
Proof. exact (@lem7055239 _94164 h1 _94165). Qed.
Lemma lem7055241 (_94164 : nat) (_94165 : nat) : (term338 _94164 _94165) = (term282 _94164 _94165).
Proof. exact (eq_refl (term338 _94164 _94165)). Qed.
Lemma lem7055252 (_94169 : nat -> nat) (_94156 : type1000) (h1 : term47 _94156) : term339 _94156 _94169.
Proof. exact (@lem7055214 _94156 h1 _94169). Qed.
Lemma lem7055253 (_94156 : type1000) (_94169 : nat -> nat) : (term339 _94156 _94169) = (term312 _94156 _94169).
Proof. exact (eq_refl (term339 _94156 _94169)). Qed.
Lemma lem7055254 (_94169 : nat -> nat) (_94156 : type1000) (h1 : term47 _94156) : term312 _94156 _94169.
Proof. exact (EQ_MP (@lem7055253 _94156 _94169) (@lem7055252 _94169 _94156 h1)). Qed.
Lemma lem7055255 (_94169 : nat -> nat) (_94170 : nat) (_94156 : type1000) (h1 : term47 _94156) : term340 _94156 _94169 _94170.
Proof. exact (@lem7055254 _94169 _94156 h1 _94170). Qed.
Lemma lem7055256 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) : (term340 _94156 _94169 _94170) = (term310 _94156 _94169 _94170).
Proof. exact (eq_refl (term340 _94156 _94169 _94170)). Qed.
Lemma lem7055257 (_94169 : nat -> nat) (_94170 : nat) (_94156 : type1000) (h1 : term47 _94156) : term310 _94156 _94169 _94170.
Proof. exact (EQ_MP (@lem7055256 _94156 _94169 _94170) (@lem7055255 _94169 _94170 _94156 h1)). Qed.
Lemma lem7055258 (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) (_94156 : type1000) (h1 : term47 _94156) : term341 _94156 _94169 _94170 _94171.
Proof. exact (@lem7055257 _94169 _94170 _94156 h1 _94171). Qed.
Lemma lem7055259 (_94171 : nat -> Prop) (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) : (term341 _94156 _94169 _94170 _94171) = (term308 _94171 _94156 _94169 _94170).
Proof. exact (eq_refl (term341 _94156 _94169 _94170 _94171)). Qed.
Lemma lem7055278 (_94171 : nat -> Prop) (_94169 : nat -> nat) (_94170 : nat) (_94156 : type1000) (h1 : term47 _94156) : term308 _94171 _94156 _94169 _94170.
Proof. exact (EQ_MP (@lem7055259 _94171 _94156 _94169 _94170) (@lem7055258 _94169 _94170 _94171 _94156 h1)). Qed.
Lemma lem7055280 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) (h1 : term247 a b _94156 f n) : term336 a b _94156 f n.
Proof. exact (EQ_MP (@lem7055139 a b _94156 f n) (@lem7054647 a b _94156 f n h1)). Qed.
Lemma lem7055536 (_94164 : nat) (_94165 : nat) (h1 : term69) : term282 _94164 _94165.
Proof. exact (EQ_MP (@lem7055241 _94164 _94165) (@lem7055240 _94164 _94165 h1)). Qed.
Lemma lem7055537 (a : nat) (b : nat) (h1 : term69) : term282 a b.
Proof. exact (@lem7055536 a b h1). Qed.
Lemma lem7055538 (a : nat) (b : nat) (h1 : term69) : term342 a b.
Proof. exact (fun h0 : term343 a b => @lem7055537 a b h1). Qed.
Lemma lem7055540 (p : Prop) : (term344 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7055541 (a : nat) (b : nat) : (term342 a b) = (term282 a b).
Proof. exact (@lem7055540 (term282 a b)). Qed.
Lemma lem7055542 (a : nat) (b : nat) (h1 : term69) : term282 a b.
Proof. exact (EQ_MP (@lem7055541 a b) (@lem7055538 a b h1)). Qed.
Lemma lem7055548 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7055549 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : (term308 _94171 _94156 _94169 _94170) = (term345 _94156 _94169 _94170 _94171).
Proof. exact (@lem7055548 ((term293 _94171 _94169 _94170) = (term302 _94171 _94156 _94169 _94170)) (term305 _94171)). Qed.
Lemma lem7055557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7055558 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : (term346 _94171 _94156 _94169 _94170) = (term347 _94156 _94169 _94170 _94171).
Proof. exact (MK_COMB (@lem7055557) (@lem7055549 _94156 _94169 _94170 _94171)). Qed.
Lemma lem7055566 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : (term345 _94156 _94169 _94170 _94171) = (term345 _94156 _94169 _94170 _94171).
Proof. exact (eq_refl (term345 _94156 _94169 _94170 _94171)). Qed.
Lemma lem7055567 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : ((term308 _94171 _94156 _94169 _94170) = (term345 _94156 _94169 _94170 _94171)) = ((term345 _94156 _94169 _94170 _94171) = (term345 _94156 _94169 _94170 _94171)).
Proof. exact (MK_COMB (@lem7055558 _94156 _94169 _94170 _94171) (@lem7055566 _94156 _94169 _94170 _94171)). Qed.
Lemma lem7055569 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7055570 (x : Prop) : (x = x) = True.
Proof. exact (@lem7055569 Prop x). Qed.
Lemma lem7055571 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : ((term345 _94156 _94169 _94170 _94171) = (term345 _94156 _94169 _94170 _94171)) = True.
Proof. exact (@lem7055570 (term345 _94156 _94169 _94170 _94171)). Qed.
Lemma lem7055572 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : ((term308 _94171 _94156 _94169 _94170) = (term345 _94156 _94169 _94170 _94171)) = True.
Proof. exact (TRANS (@lem7055567 _94156 _94169 _94170 _94171) (@lem7055571 _94156 _94169 _94170 _94171)). Qed.
Lemma lem7055573 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : True = ((term308 _94171 _94156 _94169 _94170) = (term345 _94156 _94169 _94170 _94171)).
Proof. exact (SYM (@lem7055572 _94156 _94169 _94170 _94171)). Qed.
Lemma lem7055574 (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) : (term308 _94171 _94156 _94169 _94170) = (term345 _94156 _94169 _94170 _94171).
Proof. exact (EQ_MP (@lem7055573 _94156 _94169 _94170 _94171) (@lem0)). Qed.
Lemma lem7055575 (_94169 : nat -> nat) (_94170 : nat) (_94171 : nat -> Prop) (_94156 : type1000) (h1 : term47 _94156) : term345 _94156 _94169 _94170 _94171.
Proof. exact (EQ_MP (@lem7055574 _94156 _94169 _94170 _94171) (@lem7055278 _94171 _94169 _94170 _94156 h1)). Qed.
Lemma lem7055577 (b : Prop) (a : Prop) : (a \/ b) = (term348 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7055578 (_94171 : nat -> Prop) (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) : (term345 _94156 _94169 _94170 _94171) = (term349 _94171 _94156 _94169 _94170).
Proof. exact (@lem7055577 (term305 _94171) ((term293 _94171 _94169 _94170) = (term302 _94171 _94156 _94169 _94170))). Qed.
Lemma lem7055580 (a : Prop) : (term350 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7055581 (_94171 : nat -> Prop) : (term351 _94171) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _94171).
Proof. exact (@lem7055580 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _94171)). Qed.
Lemma lem7055582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7055583 (_94171 : nat -> Prop) : (term352 _94171) = (term353 _94171).
Proof. exact (MK_COMB (@lem7055582) (@lem7055581 _94171)). Qed.
Lemma lem7055584 (_94171 : nat -> Prop) (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) : ((term293 _94171 _94169 _94170) = (term302 _94171 _94156 _94169 _94170)) = ((term293 _94171 _94169 _94170) = (term302 _94171 _94156 _94169 _94170)).
Proof. exact (eq_refl ((term293 _94171 _94169 _94170) = (term302 _94171 _94156 _94169 _94170))). Qed.
Lemma lem7055585 (_94171 : nat -> Prop) (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) : (term349 _94171 _94156 _94169 _94170) = (term354 _94171 _94156 _94169 _94170).
Proof. exact (MK_COMB (@lem7055583 _94171) (@lem7055584 _94171 _94156 _94169 _94170)). Qed.
Lemma lem7055586 (_94171 : nat -> Prop) (_94156 : type1000) (_94169 : nat -> nat) (_94170 : nat) : (term345 _94156 _94169 _94170 _94171) = (term354 _94171 _94156 _94169 _94170).
Proof. exact (TRANS (@lem7055578 _94171 _94156 _94169 _94170) (@lem7055585 _94171 _94156 _94169 _94170)). Qed.
Lemma lem7055589 (_94171 : nat -> Prop) (_94169 : nat -> nat) (_94170 : nat) (_94156 : type1000) (h1 : term47 _94156) : term354 _94171 _94156 _94169 _94170.
Proof. exact (EQ_MP (@lem7055586 _94171 _94156 _94169 _94170) (@lem7055575 _94169 _94170 _94171 _94156 h1)). Qed.
Lemma lem7055590 (a : nat) (b : nat) (_94169 : nat -> nat) (_94170 : nat) (_94156 : type1000) (h1 : term47 _94156) : term355 a b _94156 _94169 _94170.
Proof. exact (@lem7055589 (term280 a b) _94169 _94170 _94156 h1). Qed.
Lemma lem7055593 (a : nat) (b : nat) (_94169 : nat -> nat) (_94170 : nat) (_94156 : type1000) (h1 : term47 _94156) (h2 : term69) : (term326 a b _94169 _94170) = (term334 a b _94156 _94169 _94170).
Proof. exact (@lem7055590 a b _94169 _94170 _94156 h1 (@lem7055542 a b h2)). Qed.
Lemma lem7055594 (a : nat) (b : nat) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : term47 _94156) (h2 : term69) : (term326 a b f n) = (term334 a b _94156 f n).
Proof. exact (@lem7055593 a b f n _94156 h1 h2). Qed.
Lemma lem7055595 (a : nat) (b : nat) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : term47 _94156) (h2 : term69) : term356 a b _94156 f n.
Proof. exact (fun h0 : term336 a b _94156 f n => @lem7055594 a b f n _94156 h1 h2). Qed.
Lemma lem7055597 (p : Prop) : (term344 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7055598 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term356 a b _94156 f n) = ((term326 a b f n) = (term334 a b _94156 f n)).
Proof. exact (@lem7055597 ((term326 a b f n) = (term334 a b _94156 f n))). Qed.
Lemma lem7055599 (a : nat) (b : nat) (f : nat -> nat) (n : nat) (_94156 : type1000) (h1 : term47 _94156) (h2 : term69) : (term326 a b f n) = (term334 a b _94156 f n).
Proof. exact (EQ_MP (@lem7055598 a b _94156 f n) (@lem7055595 a b f n _94156 h1 h2)). Qed.
Lemma lem7055602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7055604 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) : (term336 a b _94156 f n) = (term357 a b _94156 f n).
Proof. exact (@lem7055602 ((term326 a b f n) = (term334 a b _94156 f n))). Qed.
Lemma lem7055607 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) (h1 : term247 a b _94156 f n) : term357 a b _94156 f n.
Proof. exact (EQ_MP (@lem7055604 a b _94156 f n) (@lem7055280 a b _94156 f n h1)). Qed.
Lemma lem7055610 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) (h1 : term47 _94156) (h2 : term69) (h3 : term247 a b _94156 f n) : False.
Proof. exact (@lem7055607 a b _94156 f n h3 (@lem7055599 a b f n _94156 h1 h2)). Qed.
Lemma lem7055611 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) (h1 : term47 _94156) (h2 : term69) (h3 : term247 a b _94156 f n) : term358.
Proof. exact (fun h0 : ~ False => @lem7055610 a b _94156 f n h1 h2 h3). Qed.
Lemma lem7055613 (p : Prop) : (term344 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7055614 : term358 = False.
Proof. exact (@lem7055613 False). Qed.
Lemma lem7055615 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (n : nat) (h1 : term47 _94156) (h2 : term69) (h3 : term247 a b _94156 f n) : False.
Proof. exact (EQ_MP (@lem7055614) (@lem7055611 a b _94156 f n h1 h2 h3)). Qed.
Lemma lem7055616 (a : nat) (b : nat) (_94156 : type1000) (f : nat -> nat) (h1 : term47 _94156) (h2 : term69) (h3 : term250 a b _94156 f) : False.
Proof. exact (ex_elim (@lem7054646 a b _94156 f h3) (fun n : nat => fun h0 : term249 a b _94156 f n => @lem7055615 a b _94156 f n h1 h2 h0)). Qed.
Lemma lem7055617 (a : nat) (_94156 : type1000) (f : nat -> nat) (h1 : term47 _94156) (h2 : term69) (h3 : term257 a _94156 f) : False.
Proof. exact (ex_elim (@lem7054645 a _94156 f h3) (fun b : nat => fun h0 : term256 a _94156 f b => @lem7055616 a b _94156 f h1 h2 h0)). Qed.
Lemma lem7055618 (_94156 : type1000) (f : nat -> nat) (h1 : term47 _94156) (h2 : term69) (h3 : term264 _94156 f) : False.
Proof. exact (ex_elim (@lem7054644 _94156 f h3) (fun a : nat => fun h0 : term263 _94156 f a => @lem7055617 a _94156 f h1 h2 h0)). Qed.
Lemma lem7055619 (_94156 : type1000) (h1 : term47 _94156) (h2 : term69) (h3 : term95 _94156) : False.
Proof. exact (ex_elim (@lem7054469 _94156 h3) (fun f : nat -> nat => fun h0 : term271 _94156 f => @lem7055618 _94156 f h1 h2 h0)). Qed.
Lemma lem7055620 (_94156 : type1000) (h1 : term47 _94156) (h2 : term69) (h3 : term95 _94156) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem7055619 _94156 h1 h2 h3) (fun h4 : False => @lem7054489 h2)). Qed.
Lemma lem7055621 (_94156 : type1000) (h1 : term47 _94156) (h2 : term69) (h3 : term95 _94156) : False.
Proof. exact (EQ_MP (@lem7055620 _94156 h1 h2 h3) (@lem7054489 h2)). Qed.
Lemma lem7055622 (_94156 : type1000) (h1 : term69) (h2 : term95 _94156) : term359 _94156.
Proof. exact (fun h0 : term47 _94156 => @lem7055621 _94156 h0 h1 h2). Qed.
Lemma lem7055623 (_94156 : type1000) : (term359 _94156) = (term48 _94156).
Proof. exact (@lem69 (term47 _94156)). Qed.
Lemma lem7055624 (_94156 : type1000) (h1 : term69) (h2 : term95 _94156) : term48 _94156.
Proof. exact (EQ_MP (@lem7055623 _94156) (@lem7055622 _94156 h1 h2)). Qed.
Lemma lem7055625 {A : Type'} (_94157 : type701 A) (_94156 : type1000) (h1 : term69) (h2 : term95 _94156) : term177 A _94157 _94156.
Proof. exact (fun h0 : term175 A _94157 => @lem7055624 _94156 h1 h2). Qed.
Lemma lem7055626 {A : Type'} (_94157 : type701 A) (_94156 : type1000) (h1 : term95 _94156) : term178 A _94157 _94156.
Proof. exact (fun h0 : term69 => @lem7055625 A _94157 _94156 h0 h1). Qed.
Lemma lem7055627 {A : Type'} (_94157 : type701 A) (_94156 : type1000) : term179 A _94157 _94156.
Proof. exact (fun h0 : term95 _94156 => @lem7055626 A _94157 _94156 h0). Qed.
Lemma lem7055628 {A : Type'} (_94157 : type701 A) (_94156 : type1000) : term180 A _94157 _94156.
Proof. exact (fun h0 : term155 _94156 => @lem7055627 A _94157 _94156). Qed.
Lemma lem7055633 {A : Type'} (_94157 : type701 A) : term182 A _94157.
Proof. exact (fun _94156 : type1000 => @lem7055628 A _94157 _94156). Qed.
Lemma lem7055634 {A : Type'} (_94157 : type701 A) : term238 A _94157.
Proof. exact (fun h0 : term236 A _94157 => @lem7055633 A _94157). Qed.
Lemma lem7055639 {A : Type'} : term240 A.
Proof. exact (fun _94157 : type701 A => @lem7055634 A _94157). Qed.
Lemma lem7055640 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem7054347 A) (@lem7055639 A)). Qed.
Lemma lem7055642 {A : Type'} : term5 A.
Proof. exact (@lem7053470 A (@lem7055640 A)). Qed.
Lemma lem7055643 {A : Type'} (h1 : term3) : term15 A.
Proof. exact (@lem7055642 A (@lem7053453 h1)). Qed.
Lemma lem7055644 {A : Type'} (h1 : term3) : term12 A.
Proof. exact (@lem7055643 A h1 (@lem5329299)). Qed.
Lemma lem7055645 (h1 : term3) : term9.
Proof. exact (@lem7055644 Prop h1 (@lem7053438 Prop)). Qed.
Lemma lem7055646 (h1 : term3) : False.
Proof. exact (@lem7055645 h1 (@lem7053454)). Qed.
Lemma lem7055647 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem7055646 h1) (fun h2 : False => @lem7053453 h1)). Qed.
Lemma lem7055648 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem7055647 h1) (@lem7053453 h1)). Qed.
Lemma lem7055649 : term2.
Proof. exact (fun h0 : term3 => @lem7055648 h0). Qed.
Lemma lem7055650 : term1.
Proof. exact (EQ_MP (@lem7053452) (@lem7055649)). Qed.
