Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3074596_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_ABS_MUL_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17362_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
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
Require Import thm3070925_spec.
Require Import thm3070926_spec.
Require Import thm3070930_spec.
Require Import thm3070931_spec.
Require Import thm3070937_spec.
Require Import thm3070956_spec.
Require Import thm3070957_spec.
Require Import thm3073366_spec.
Require Import thm3073385_spec.
Require Import thm3073386_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem3073438 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3073439 (b : nat) (a : nat) : (term1 b a) = (term2 b a).
Proof. exact (@lem3073438 (term1 b a)). Qed.
Lemma lem3073440 (b : nat) (a : nat) : (term2 b a) = (term1 b a).
Proof. exact (SYM (@lem3073439 b a)). Qed.
Lemma lem3073441 (b : nat) (a : nat) (h1 : term3 b a) : term3 b a.
Proof. exact (h1). Qed.
Lemma lem3073444 (b : nat) (a : nat) (h1 : term4 b a) : term4 b a.
Proof. exact (h1). Qed.
Lemma lem3073445 (b : nat) (a : nat) : term5 b a.
Proof. exact (fun h0 : term4 b a => @lem3073444 b a h0). Qed.
Lemma lem3073446 (b : nat) (a : nat) (h1 : term5 b a) : term5 b a.
Proof. exact (h1). Qed.
Lemma lem3073447 (b : nat) (a : nat) (h1 : term4 b a) : term4 b a.
Proof. exact (h1). Qed.
Lemma lem3073448 (b : nat) (a : nat) (h1 : term4 b a) (h2 : term5 b a) : term4 b a.
Proof. exact (@lem3073446 b a h2 (@lem3073447 b a h1)). Qed.
Lemma lem3073449 (b : nat) (a : nat) (h1 : term4 b a) : term6 b a.
Proof. exact (fun h0 : term5 b a => @lem3073448 b a h1 h0). Qed.
Lemma lem3073450 (b : nat) (a : nat) (h1 : term5 b a) : term5 b a.
Proof. exact (h1). Qed.
Lemma lem3073451 (b : nat) (a : nat) (h1 : term4 b a) (h2 : term5 b a) : term4 b a.
Proof. exact (@lem3073449 b a h1 (@lem3073450 b a h2)). Qed.
Lemma lem3073452 (b : nat) (a : nat) (h1 : term5 b a) : term5 b a.
Proof. exact (fun h0 : term4 b a => @lem3073451 b a h0 h1). Qed.
Lemma lem3073453 (b : nat) (a : nat) : term7 b a.
Proof. exact (fun h0 : term5 b a => @lem3073452 b a h0). Qed.
Lemma lem3073456 (b : nat) (a : nat) : term5 b a.
Proof. exact (@lem3073453 b a (@lem3073445 b a)). Qed.
Lemma lem3073488 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3073489 : term8 = term9.
Proof. exact (@lem3073488 term10). Qed.
Lemma lem3073498 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem3073499 : term12 = term13.
Proof. exact (MK_COMB (@lem3073498) (@lem3073489)). Qed.
Lemma lem3073502 (b : nat) (a : nat) : (term14 b a) = (term14 b a).
Proof. exact (eq_refl (term14 b a)). Qed.
Lemma lem3073503 (b : nat) (a : nat) : (term4 b a) = (term15 b a).
Proof. exact (MK_COMB (@lem3073502 b a) (@lem3073499)). Qed.
Lemma lem3073506 (a : nat) : (term16 a) = (term17 a).
Proof. exact (fun_ext (fun b : nat => @lem3073503 b a)). Qed.
Lemma lem3073507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073508 (a : nat) : (term18 a) = (term19 a).
Proof. exact (MK_COMB (@lem3073507) (@lem3073506 a)). Qed.
Lemma lem3073513 : term20 = term21.
Proof. exact (fun_ext (fun a : nat => @lem3073508 a)). Qed.
Lemma lem3073514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073523 : term22 = term23.
Proof. exact (MK_COMB (@lem3073514) (@lem3073513)). Qed.
Lemma lem3073524 (m : nat) (n : nat) : ((term24 m n) = (term25 m n)) = ((term24 m n) = (term25 m n)).
Proof. exact (eq_refl ((term24 m n) = (term25 m n))). Qed.
Lemma lem3073525 (m : nat) : (term26 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem3073524 m n)). Qed.
Lemma lem3073526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073527 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem3073526) (@lem3073525 m)). Qed.
Lemma lem3073528 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem3073527 m)). Qed.
Lemma lem3073529 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073530 : term10 = term10.
Proof. exact (MK_COMB (@lem3073529) (@lem3073528)). Qed.
Lemma lem3073531 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3073532 : term9 = term9.
Proof. exact (MK_COMB (@lem3073531) (@lem3073530)). Qed.
Lemma lem3073537 (m : nat) (n : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (((int_of_num m) = (int_of_num n)) = (m = n))). Qed.
Lemma lem3073538 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem3073537 m n)). Qed.
Lemma lem3073539 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073540 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem3073539) (@lem3073538 m)). Qed.
Lemma lem3073541 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem3073540 m)). Qed.
Lemma lem3073542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073543 : term32 = term32.
Proof. exact (MK_COMB (@lem3073542) (@lem3073541)). Qed.
Lemma lem3073544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3073545 : term11 = term11.
Proof. exact (MK_COMB (@lem3073544) (@lem3073543)). Qed.
Lemma lem3073546 : term13 = term13.
Proof. exact (MK_COMB (@lem3073545) (@lem3073532)). Qed.
Lemma lem3073547 (b : nat) (a : nat) (x : int) : ((int_of_num b) = (term33 a x)) = ((int_of_num b) = (term33 a x)).
Proof. exact (eq_refl ((int_of_num b) = (term33 a x))). Qed.
Lemma lem3073548 (b : nat) (a : nat) : (term34 b a) = (term34 b a).
Proof. exact (fun_ext (fun x : int => @lem3073547 b a x)). Qed.
Lemma lem3073549 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3073550 (b : nat) (a : nat) : (term35 b a) = (term35 b a).
Proof. exact (MK_COMB (@lem3073549) (@lem3073548 b a)). Qed.
Lemma lem3073551 (b : nat) (a : nat) (x : nat) : (b = (Nat.mul a x)) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (b = (Nat.mul a x))). Qed.
Lemma lem3073552 (b : nat) (a : nat) : (term36 b a) = (term36 b a).
Proof. exact (fun_ext (fun x : nat => @lem3073551 b a x)). Qed.
Lemma lem3073553 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3073554 (b : nat) (a : nat) : (term37 b a) = (term37 b a).
Proof. exact (MK_COMB (@lem3073553) (@lem3073552 b a)). Qed.
Lemma lem3073555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3073556 (b : nat) (a : nat) : (term38 b a) = (term38 b a).
Proof. exact (MK_COMB (@lem3073555) (@lem3073554 b a)). Qed.
Lemma lem3073557 (b : nat) (a : nat) : (term1 b a) = (term1 b a).
Proof. exact (MK_COMB (@lem3073556 b a) (@lem3073550 b a)). Qed.
Lemma lem3073558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3073559 (b : nat) (a : nat) : (term3 b a) = (term3 b a).
Proof. exact (MK_COMB (@lem3073558) (@lem3073557 b a)). Qed.
Lemma lem3073560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3073561 (b : nat) (a : nat) : (term14 b a) = (term14 b a).
Proof. exact (MK_COMB (@lem3073560) (@lem3073559 b a)). Qed.
Lemma lem3073562 (b : nat) (a : nat) : (term15 b a) = (term15 b a).
Proof. exact (MK_COMB (@lem3073561 b a) (@lem3073546)). Qed.
Lemma lem3073563 (a : nat) : (term17 a) = (term17 a).
Proof. exact (fun_ext (fun b : nat => @lem3073562 b a)). Qed.
Lemma lem3073564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073565 (a : nat) : (term19 a) = (term19 a).
Proof. exact (MK_COMB (@lem3073564) (@lem3073563 a)). Qed.
Lemma lem3073566 : term21 = term21.
Proof. exact (fun_ext (fun a : nat => @lem3073565 a)). Qed.
Lemma lem3073567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073568 : term23 = term23.
Proof. exact (MK_COMB (@lem3073567) (@lem3073566)). Qed.
Lemma lem3073625 : term22 = term23.
Proof. exact (TRANS (@lem3073523) (@lem3073568)). Qed.
Lemma lem3073626 : term23 = term22.
Proof. exact (SYM (@lem3073625)). Qed.
Lemma lem3073627 (b : nat) (a : nat) (h1 : term3 b a) : term3 b a.
Proof. exact (h1). Qed.
Lemma lem3073629 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem3073630 (b : nat) (a : nat) (x : nat) : (b = (Nat.mul a x)) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (b = (Nat.mul a x))). Qed.
Lemma lem3073631 (b : nat) (a : nat) : (term36 b a) = (term36 b a).
Proof. exact (fun_ext (fun x : nat => @lem3073630 b a x)). Qed.
Lemma lem3073632 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3073633 (b : nat) (a : nat) : (term37 b a) = (term37 b a).
Proof. exact (MK_COMB (@lem3073632) (@lem3073631 b a)). Qed.
Lemma lem3073635 (P : int -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18394 int P). Qed.
Lemma lem3073636 (b : nat) (a : nat) : (term41 b a) = (term42 b a).
Proof. exact (@lem3073635 (term34 b a)). Qed.
Lemma lem3073637 (b : nat) (a : nat) (x : int) : (term43 b a x) = ((int_of_num b) = (term33 a x)).
Proof. exact (eq_refl (term43 b a x)). Qed.
Lemma lem3073638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3073640 (b : nat) (a : nat) (x : int) : (term44 b a x) = (term45 b a x).
Proof. exact (MK_COMB (@lem3073638) (@lem3073637 b a x)). Qed.
Lemma lem3073641 (b : nat) (a : nat) : (term46 b a) = (term47 b a).
Proof. exact (fun_ext (fun x : int => @lem3073640 b a x)). Qed.
Lemma lem3073642 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3073643 (b : nat) (a : nat) : (term42 b a) = (term48 b a).
Proof. exact (MK_COMB (@lem3073642) (@lem3073641 b a)). Qed.
Lemma lem3073644 (b : nat) (a : nat) : (term41 b a) = (term48 b a).
Proof. exact (TRANS (@lem3073636 b a) (@lem3073643 b a)). Qed.
Lemma lem3073645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3073646 (b : nat) (a : nat) : (term49 b a) = (term49 b a).
Proof. exact (MK_COMB (@lem3073645) (@lem3073633 b a)). Qed.
Lemma lem3073647 (b : nat) (a : nat) : (term50 b a) = (term51 b a).
Proof. exact (MK_COMB (@lem3073646 b a) (@lem3073644 b a)). Qed.
Lemma lem3073648 (b : nat) (a : nat) : (term3 b a) = (term50 b a).
Proof. exact (@lem17362 (term37 b a) (term35 b a)). Qed.
Lemma lem3073649 (b : nat) (a : nat) : (term3 b a) = (term51 b a).
Proof. exact (TRANS (@lem3073648 b a) (@lem3073647 b a)). Qed.
Lemma lem3073660 {A : Type'} (P : A -> Prop) (Q : Prop) : (term52 A P Q) = (term53 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3073661 (P : nat -> Prop) (Q : Prop) : (term54 P Q) = (term55 P Q).
Proof. exact (@lem3073660 nat P Q). Qed.
Lemma lem3073662 (b : nat) (a : nat) : (term56 b a) = (term57 b a).
Proof. exact (@lem3073661 (term36 b a) (term48 b a)). Qed.
Lemma lem3073663 (b : nat) (a : nat) (x : nat) : (term58 b a x) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (term58 b a x)). Qed.
Lemma lem3073664 (b : nat) (a : nat) : (term59 b a) = (term36 b a).
Proof. exact (fun_ext (fun x : nat => @lem3073663 b a x)). Qed.
Lemma lem3073665 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3073666 (b : nat) (a : nat) : (term60 b a) = (term37 b a).
Proof. exact (MK_COMB (@lem3073665) (@lem3073664 b a)). Qed.
Lemma lem3073667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3073668 (b : nat) (a : nat) : (term61 b a) = (term49 b a).
Proof. exact (MK_COMB (@lem3073667) (@lem3073666 b a)). Qed.
Lemma lem3073669 (b : nat) (a : nat) : (term48 b a) = (term48 b a).
Proof. exact (eq_refl (term48 b a)). Qed.
Lemma lem3073670 (b : nat) (a : nat) : (term56 b a) = (term51 b a).
Proof. exact (MK_COMB (@lem3073668 b a) (@lem3073669 b a)). Qed.
Lemma lem3073671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3073672 (b : nat) (a : nat) : (term62 b a) = (term63 b a).
Proof. exact (MK_COMB (@lem3073671) (@lem3073670 b a)). Qed.
Lemma lem3073673 (b : nat) (a : nat) (x : nat) : (term58 b a x) = (b = (Nat.mul a x)).
Proof. exact (eq_refl (term58 b a x)). Qed.
Lemma lem3073674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3073675 (b : nat) (a : nat) (x : nat) : (term64 b a x) = (term65 b a x).
Proof. exact (MK_COMB (@lem3073674) (@lem3073673 b a x)). Qed.
Lemma lem3073676 (b : nat) (a : nat) : (term48 b a) = (term48 b a).
Proof. exact (eq_refl (term48 b a)). Qed.
Lemma lem3073677 (x : nat) (b : nat) (a : nat) : (term66 x b a) = (term67 x b a).
Proof. exact (MK_COMB (@lem3073675 b a x) (@lem3073676 b a)). Qed.
Lemma lem3073678 (b : nat) (a : nat) : (term68 b a) = (term69 b a).
Proof. exact (fun_ext (fun x : nat => @lem3073677 x b a)). Qed.
Lemma lem3073679 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3073680 (b : nat) (a : nat) : (term57 b a) = (term70 b a).
Proof. exact (MK_COMB (@lem3073679) (@lem3073678 b a)). Qed.
Lemma lem3073681 (b : nat) (a : nat) : ((term56 b a) = (term57 b a)) = ((term51 b a) = (term70 b a)).
Proof. exact (MK_COMB (@lem3073672 b a) (@lem3073680 b a)). Qed.
Lemma lem3073683 (b : nat) (a : nat) : (term51 b a) = (term70 b a).
Proof. exact (EQ_MP (@lem3073681 b a) (@lem3073662 b a)). Qed.
Lemma lem3073684 (b : nat) (a : nat) : (term3 b a) = (term70 b a).
Proof. exact (TRANS (@lem3073649 b a) (@lem3073683 b a)). Qed.
Lemma lem3073685 (b : nat) (a : nat) (h1 : term3 b a) : term70 b a.
Proof. exact (EQ_MP (@lem3073684 b a) (@lem3073627 b a h1)). Qed.
Lemma lem3073973 (m : nat) (n : nat) : ((term24 m n) = (term25 m n)) = ((term24 m n) = (term25 m n)).
Proof. exact (eq_refl ((term24 m n) = (term25 m n))). Qed.
Lemma lem3073974 (m : nat) : (term26 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem3073973 m n)). Qed.
Lemma lem3073975 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073976 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem3073975) (@lem3073974 m)). Qed.
Lemma lem3073977 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem3073976 m)). Qed.
Lemma lem3073978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073991 : term10 = term10.
Proof. exact (MK_COMB (@lem3073978) (@lem3073977)). Qed.
Lemma lem3073992 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem3073991) (@lem3073629 h1)). Qed.
Lemma lem3073993 (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term67 x b a.
Proof. exact (h1). Qed.
Lemma lem3074066 (m : nat) (n : nat) : ((term24 m n) = (term25 m n)) = ((term24 m n) = (term25 m n)).
Proof. exact (eq_refl ((term24 m n) = (term25 m n))). Qed.
Lemma lem3074067 (m : nat) : (term26 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem3074066 m n)). Qed.
Lemma lem3074068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3074069 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem3074068) (@lem3074067 m)). Qed.
Lemma lem3074070 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem3074069 m)). Qed.
Lemma lem3074071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3074072 : term10 = term10.
Proof. exact (MK_COMB (@lem3074071) (@lem3074070)). Qed.
Lemma lem3074073 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem3074072) (@lem3073992 h1)). Qed.
Lemma lem3074088 (b : nat) (a : nat) (x : int) : (term45 b a x) = (term45 b a x).
Proof. exact (eq_refl (term45 b a x)). Qed.
Lemma lem3074089 (b : nat) (a : nat) : (term47 b a) = (term47 b a).
Proof. exact (fun_ext (fun x : int => @lem3074088 b a x)). Qed.
Lemma lem3074090 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3074091 (b : nat) (a : nat) : (term48 b a) = (term48 b a).
Proof. exact (MK_COMB (@lem3074090) (@lem3074089 b a)). Qed.
Lemma lem3074102 (b : nat) (a : nat) (x : nat) : (term65 b a x) = (term65 b a x).
Proof. exact (eq_refl (term65 b a x)). Qed.
Lemma lem3074103 (x : nat) (b : nat) (a : nat) : (term67 x b a) = (term67 x b a).
Proof. exact (MK_COMB (@lem3074102 b a x) (@lem3074091 b a)). Qed.
Lemma lem3074104 (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term67 x b a.
Proof. exact (EQ_MP (@lem3074103 x b a) (@lem3073993 x b a h1)). Qed.
Lemma lem3074105 (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term48 b a.
Proof. exact (proj2 (@lem3074104 x b a h1)). Qed.
Lemma lem3074110 (m : nat) (n : nat) : ((term24 m n) = (term25 m n)) = ((term24 m n) = (term25 m n)).
Proof. exact (eq_refl ((term24 m n) = (term25 m n))). Qed.
Lemma lem3074111 (m : nat) : (term26 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem3074110 m n)). Qed.
Lemma lem3074112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3074113 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem3074112) (@lem3074111 m)). Qed.
Lemma lem3074114 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem3074113 m)). Qed.
Lemma lem3074115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3074117 : term10 = term10.
Proof. exact (MK_COMB (@lem3074115) (@lem3074114)). Qed.
Lemma lem3074118 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem3074117) (@lem3074073 h1)). Qed.
Lemma lem3074124 (b : nat) (a : nat) (x : int) : (term45 b a x) = (term45 b a x).
Proof. exact (eq_refl (term45 b a x)). Qed.
Lemma lem3074125 (b : nat) (a : nat) : (term47 b a) = (term47 b a).
Proof. exact (fun_ext (fun x : int => @lem3074124 b a x)). Qed.
Lemma lem3074126 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3074128 (b : nat) (a : nat) : (term48 b a) = (term48 b a).
Proof. exact (MK_COMB (@lem3074126) (@lem3074125 b a)). Qed.
Lemma lem3074129 (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term48 b a.
Proof. exact (EQ_MP (@lem3074128 b a) (@lem3074105 x b a h1)). Qed.
Lemma lem3074162 (_32005 : nat) (h1 : term10) : term71 _32005.
Proof. exact (@lem3074118 h1 _32005). Qed.
Lemma lem3074163 (_32005 : nat) : (term71 _32005) = (term27 _32005).
Proof. exact (eq_refl (term71 _32005)). Qed.
Lemma lem3074164 (_32005 : nat) (h1 : term10) : term27 _32005.
Proof. exact (EQ_MP (@lem3074163 _32005) (@lem3074162 _32005 h1)). Qed.
Lemma lem3074165 (_32005 : nat) (_32006 : nat) (h1 : term10) : term72 _32005 _32006.
Proof. exact (@lem3074164 _32005 h1 _32006). Qed.
Lemma lem3074166 (_32005 : nat) (_32006 : nat) : (term72 _32005 _32006) = ((term24 _32005 _32006) = (term25 _32005 _32006)).
Proof. exact (eq_refl (term72 _32005 _32006)). Qed.
Lemma lem3074168 (_32007 : int) (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term73 b a _32007.
Proof. exact (@lem3074129 x b a h1 _32007). Qed.
Lemma lem3074169 (b : nat) (a : nat) (_32007 : int) : (term73 b a _32007) = (term45 b a _32007).
Proof. exact (eq_refl (term73 b a _32007)). Qed.
Lemma lem3074186 (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : b = (Nat.mul a x).
Proof. exact (proj1 (@lem3074104 x b a h1)). Qed.
Lemma lem3074188 (_32007 : int) (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term45 b a _32007.
Proof. exact (EQ_MP (@lem3074169 b a _32007) (@lem3074168 _32007 x b a h1)). Qed.
Lemma lem3074229 (a : nat) (_32007 : int) : (term74 a _32007) = (term74 a _32007).
Proof. exact (eq_refl (term74 a _32007)). Qed.
Lemma lem3074230 (_32007 : int) (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : (term75 a _32007 b) = (term76 _32007 a x).
Proof. exact (MK_COMB (@lem3074229 a _32007) (@lem3074186 x b a h1)). Qed.
Lemma lem3074231 (x : nat) (a : nat) (_32007 : int) : (term76 _32007 a x) = (term77 x a _32007).
Proof. exact (eq_refl (term76 _32007 a x)). Qed.
Lemma lem3074232 (a : nat) (_32007 : int) (b : nat) : (term78 a _32007 b) = (term78 a _32007 b).
Proof. exact (eq_refl (term78 a _32007 b)). Qed.
Lemma lem3074233 (b : nat) (x : nat) (a : nat) (_32007 : int) : ((term75 a _32007 b) = (term76 _32007 a x)) = ((term75 a _32007 b) = (term77 x a _32007)).
Proof. exact (MK_COMB (@lem3074232 a _32007 b) (@lem3074231 x a _32007)). Qed.
Lemma lem3074234 (b : nat) (a : nat) (_32007 : int) : (term75 a _32007 b) = (term45 b a _32007).
Proof. exact (eq_refl (term75 a _32007 b)). Qed.
Lemma lem3074235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3074236 (b : nat) (a : nat) (_32007 : int) : (term78 a _32007 b) = (term79 b a _32007).
Proof. exact (MK_COMB (@lem3074235) (@lem3074234 b a _32007)). Qed.
Lemma lem3074237 (x : nat) (a : nat) (_32007 : int) : (term77 x a _32007) = (term77 x a _32007).
Proof. exact (eq_refl (term77 x a _32007)). Qed.
Lemma lem3074238 (b : nat) (x : nat) (a : nat) (_32007 : int) : ((term75 a _32007 b) = (term77 x a _32007)) = ((term45 b a _32007) = (term77 x a _32007)).
Proof. exact (MK_COMB (@lem3074236 b a _32007) (@lem3074237 x a _32007)). Qed.
Lemma lem3074239 (b : nat) (x : nat) (a : nat) (_32007 : int) : ((term75 a _32007 b) = (term76 _32007 a x)) = ((term45 b a _32007) = (term77 x a _32007)).
Proof. exact (TRANS (@lem3074233 b x a _32007) (@lem3074238 b x a _32007)). Qed.
Lemma lem3074240 (_32007 : int) (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : (term45 b a _32007) = (term77 x a _32007).
Proof. exact (EQ_MP (@lem3074239 b x a _32007) (@lem3074230 _32007 x b a h1)). Qed.
Lemma lem3074241 (_32007 : int) (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term77 x a _32007.
Proof. exact (EQ_MP (@lem3074240 _32007 x b a h1) (@lem3074188 _32007 x b a h1)). Qed.
Lemma lem3074309 (x : int) (y : int) (z : int) : term80 x y z.
Proof. exact (@lem21385 int x y z). Qed.
Lemma lem3074313 (_32005 : nat) (_32006 : nat) (h1 : term10) : (term24 _32005 _32006) = (term25 _32005 _32006).
Proof. exact (EQ_MP (@lem3074166 _32005 _32006) (@lem3074165 _32005 _32006 h1)). Qed.
Lemma lem3074314 (a : nat) (x : nat) (h1 : term10) : (term24 a x) = (term25 a x).
Proof. exact (@lem3074313 a x h1). Qed.
Lemma lem3074315 (a : nat) (x : nat) (h1 : term10) : term81 a x.
Proof. exact (fun h0 : term82 a x => @lem3074314 a x h1). Qed.
Lemma lem3074317 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3074318 (a : nat) (x : nat) : (term81 a x) = ((term24 a x) = (term25 a x)).
Proof. exact (@lem3074317 ((term24 a x) = (term25 a x))). Qed.
Lemma lem3074319 (a : nat) (x : nat) (h1 : term10) : (term24 a x) = (term25 a x).
Proof. exact (EQ_MP (@lem3074318 a x) (@lem3074315 a x h1)). Qed.
Lemma lem3074321 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem3074322 (a : nat) (x : nat) : (term24 a x) = (term24 a x).
Proof. exact (@lem3074321 (term24 a x)). Qed.
Lemma lem3074323 (a : nat) (x : nat) : term84 a x.
Proof. exact (fun h0 : term85 a x => @lem3074322 a x). Qed.
Lemma lem3074325 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3074326 (a : nat) (x : nat) : (term84 a x) = ((term24 a x) = (term24 a x)).
Proof. exact (@lem3074325 ((term24 a x) = (term24 a x))). Qed.
Lemma lem3074327 (a : nat) (x : nat) : (term24 a x) = (term24 a x).
Proof. exact (EQ_MP (@lem3074326 a x) (@lem3074323 a x)). Qed.
Lemma lem3074345 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3074346 (y : int) (x : int) (z : int) : (term86 x y z) = (term87 y x z).
Proof. exact (@lem3074345 (y = z) (term88 x z)). Qed.
Lemma lem3074356 (x : int) (y : int) : (term89 x y) = (term89 x y).
Proof. exact (eq_refl (term89 x y)). Qed.
Lemma lem3074357 (y : int) (x : int) (z : int) : (term80 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem3074356 x y) (@lem3074346 y x z)). Qed.
Lemma lem3074361 (q : Prop) (p : Prop) (r : Prop) : (term91 p q r) = (term91 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3074362 (y : int) (x : int) (z : int) : (term90 y x z) = (term92 y x z).
Proof. exact (@lem3074361 (y = z) (term88 x y) (term88 x z)). Qed.
Lemma lem3074384 (y : int) (x : int) (z : int) : (term80 x y z) = (term92 y x z).
Proof. exact (TRANS (@lem3074357 y x z) (@lem3074362 y x z)). Qed.
Lemma lem3074385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3074386 (y : int) (x : int) (z : int) : (term93 x y z) = (term94 y x z).
Proof. exact (MK_COMB (@lem3074385) (@lem3074384 y x z)). Qed.
Lemma lem3074408 (y : int) (x : int) (z : int) : (term92 y x z) = (term92 y x z).
Proof. exact (eq_refl (term92 y x z)). Qed.
Lemma lem3074409 (y : int) (x : int) (z : int) : ((term80 x y z) = (term92 y x z)) = ((term92 y x z) = (term92 y x z)).
Proof. exact (MK_COMB (@lem3074386 y x z) (@lem3074408 y x z)). Qed.
Lemma lem3074411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3074412 (x : Prop) : (x = x) = True.
Proof. exact (@lem3074411 Prop x). Qed.
Lemma lem3074413 (y : int) (x : int) (z : int) : ((term92 y x z) = (term92 y x z)) = True.
Proof. exact (@lem3074412 (term92 y x z)). Qed.
Lemma lem3074414 (y : int) (x : int) (z : int) : ((term80 x y z) = (term92 y x z)) = True.
Proof. exact (TRANS (@lem3074409 y x z) (@lem3074413 y x z)). Qed.
Lemma lem3074415 (y : int) (x : int) (z : int) : True = ((term80 x y z) = (term92 y x z)).
Proof. exact (SYM (@lem3074414 y x z)). Qed.
Lemma lem3074416 (y : int) (x : int) (z : int) : (term80 x y z) = (term92 y x z).
Proof. exact (EQ_MP (@lem3074415 y x z) (@lem0)). Qed.
Lemma lem3074417 (y : int) (x : int) (z : int) : term92 y x z.
Proof. exact (EQ_MP (@lem3074416 y x z) (@lem3074309 x y z)). Qed.
Lemma lem3074419 (b : Prop) (a : Prop) : (a \/ b) = (term95 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3074420 (x : int) (y : int) (z : int) : (term92 y x z) = (term96 x y z).
Proof. exact (@lem3074419 (term97 y x z) (y = z)). Qed.
Lemma lem3074422 (a : Prop) (b : Prop) : (term98 a b) = (term99 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3074423 (y : int) (x : int) (z : int) : (term100 y x z) = (term101 y x z).
Proof. exact (@lem3074422 (term88 x y) (term88 x z)). Qed.
Lemma lem3074425 (a : Prop) : (term102 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3074426 (x : int) (y : int) : (term103 x y) = (x = y).
Proof. exact (@lem3074425 (x = y)). Qed.
Lemma lem3074427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3074428 (x : int) (y : int) : (term104 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem3074427) (@lem3074426 x y)). Qed.
Lemma lem3074430 (a : Prop) : (term102 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3074431 (x : int) (z : int) : (term103 x z) = (x = z).
Proof. exact (@lem3074430 (x = z)). Qed.
Lemma lem3074432 (y : int) (x : int) (z : int) : (term101 y x z) = (term106 y x z).
Proof. exact (MK_COMB (@lem3074428 x y) (@lem3074431 x z)). Qed.
Lemma lem3074433 (y : int) (x : int) (z : int) : (term100 y x z) = (term106 y x z).
Proof. exact (TRANS (@lem3074423 y x z) (@lem3074432 y x z)). Qed.
Lemma lem3074434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3074435 (y : int) (x : int) (z : int) : (term107 y x z) = (term108 y x z).
Proof. exact (MK_COMB (@lem3074434) (@lem3074433 y x z)). Qed.
Lemma lem3074436 (y : int) (z : int) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3074437 (x : int) (y : int) (z : int) : (term96 x y z) = (term109 x y z).
Proof. exact (MK_COMB (@lem3074435 y x z) (@lem3074436 y z)). Qed.
Lemma lem3074438 (x : int) (y : int) (z : int) : (term92 y x z) = (term109 x y z).
Proof. exact (TRANS (@lem3074420 x y z) (@lem3074437 x y z)). Qed.
Lemma lem3074440 (a : nat) (x : nat) (h1 : term10) : term110 a x.
Proof. exact (conj (@lem3074319 a x h1) (@lem3074327 a x)). Qed.
Lemma lem3074442 (x : int) (y : int) (z : int) : term109 x y z.
Proof. exact (EQ_MP (@lem3074438 x y z) (@lem3074417 y x z)). Qed.
Lemma lem3074443 (a : nat) (x : nat) : term111 a x.
Proof. exact (@lem3074442 (term24 a x) (term25 a x) (term24 a x)). Qed.
Lemma lem3074446 (a : nat) (x : nat) (h1 : term10) : (term25 a x) = (term24 a x).
Proof. exact (@lem3074443 a x (@lem3074440 a x h1)). Qed.
Lemma lem3074447 (a : nat) (x : nat) (h1 : term10) : term112 a x.
Proof. exact (fun h0 : term113 a x => @lem3074446 a x h1). Qed.
Lemma lem3074449 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3074450 (a : nat) (x : nat) : (term112 a x) = ((term25 a x) = (term24 a x)).
Proof. exact (@lem3074449 ((term25 a x) = (term24 a x))). Qed.
Lemma lem3074451 (a : nat) (x : nat) (h1 : term10) : (term25 a x) = (term24 a x).
Proof. exact (EQ_MP (@lem3074450 a x) (@lem3074447 a x h1)). Qed.
Lemma lem3074454 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3074456 (x : nat) (a : nat) (_32007 : int) : (term77 x a _32007) = (term114 x a _32007).
Proof. exact (@lem3074454 ((term25 a x) = (term33 a _32007))). Qed.
Lemma lem3074459 (_32007 : int) (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term114 x a _32007.
Proof. exact (EQ_MP (@lem3074456 x a _32007) (@lem3074241 _32007 x b a h1)). Qed.
Lemma lem3074460 (x : nat) (b : nat) (a : nat) (h1 : term67 x b a) : term115 a x.
Proof. exact (@lem3074459 (int_of_num x) x b a h1). Qed.
Lemma lem3074463 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : False.
Proof. exact (@lem3074460 x b a h2 (@lem3074451 a x h1)). Qed.
Lemma lem3074464 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : term116.
Proof. exact (fun h0 : ~ False => @lem3074463 x b a h1 h2). Qed.
Lemma lem3074466 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3074467 : term116 = False.
Proof. exact (@lem3074466 False). Qed.
Lemma lem3074469 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : False.
Proof. exact (EQ_MP (@lem3074467) (@lem3074464 x b a h1 h2)). Qed.
Lemma lem3074470 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem3074469 x b a h1 h2) (fun h3 : False => @lem3074118 h1)). Qed.
Lemma lem3074471 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : False.
Proof. exact (EQ_MP (@lem3074470 x b a h1 h2) (@lem3074118 h1)). Qed.
Lemma lem3074472 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : (term67 x b a) = False.
Proof. exact (prop_ext (fun h3 : term67 x b a => @lem3074471 x b a h1 h2) (fun h3 : False => @lem3074104 x b a h2)). Qed.
Lemma lem3074473 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : False.
Proof. exact (EQ_MP (@lem3074472 x b a h1 h2) (@lem3074104 x b a h2)). Qed.
Lemma lem3074474 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem3074473 x b a h1 h2) (fun h3 : False => @lem3074073 h1)). Qed.
Lemma lem3074475 (x : nat) (b : nat) (a : nat) (h1 : term10) (h2 : term67 x b a) : False.
Proof. exact (EQ_MP (@lem3074474 x b a h1 h2) (@lem3074073 h1)). Qed.
Lemma lem3074476 (b : nat) (a : nat) (h1 : term10) (h2 : term3 b a) : False.
Proof. exact (ex_elim (@lem3073685 b a h2) (fun x : nat => fun h0 : term69 b a x => @lem3074475 x b a h1 h0)). Qed.
Lemma lem3074477 (b : nat) (a : nat) (h1 : term10) (h2 : term3 b a) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem3074476 b a h1 h2) (fun h3 : False => @lem3073992 h1)). Qed.
Lemma lem3074478 (b : nat) (a : nat) (h1 : term10) (h2 : term3 b a) : False.
Proof. exact (EQ_MP (@lem3074477 b a h1 h2) (@lem3073992 h1)). Qed.
Lemma lem3074479 (b : nat) (a : nat) (h1 : term3 b a) : term8.
Proof. exact (fun h0 : term10 => @lem3074478 b a h0 h1). Qed.
Lemma lem3074480 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem3074481 (b : nat) (a : nat) (h1 : term3 b a) : term9.
Proof. exact (EQ_MP (@lem3074480) (@lem3074479 b a h1)). Qed.
Lemma lem3074482 (b : nat) (a : nat) (h1 : term3 b a) : term13.
Proof. exact (fun h0 : term32 => @lem3074481 b a h1). Qed.
Lemma lem3074483 (b : nat) (a : nat) : term15 b a.
Proof. exact (fun h0 : term3 b a => @lem3074482 b a h0). Qed.
Lemma lem3074488 (a : nat) : term19 a.
Proof. exact (fun b : nat => @lem3074483 b a). Qed.
Lemma lem3074493 : term23.
Proof. exact (fun a : nat => @lem3074488 a). Qed.
Lemma lem3074494 : term22.
Proof. exact (EQ_MP (@lem3073626) (@lem3074493)). Qed.
Lemma lem3074495 (a : nat) : term117 a.
Proof. exact (@lem3074494 a). Qed.
Lemma lem3074496 (a : nat) : (term117 a) = (term18 a).
Proof. exact (eq_refl (term117 a)). Qed.
Lemma lem3074497 (a : nat) : term18 a.
Proof. exact (EQ_MP (@lem3074496 a) (@lem3074495 a)). Qed.
Lemma lem3074498 (a : nat) (b : nat) : term118 a b.
Proof. exact (@lem3074497 a b). Qed.
Lemma lem3074499 (b : nat) (a : nat) : (term118 a b) = (term4 b a).
Proof. exact (eq_refl (term118 a b)). Qed.
Lemma lem3074500 (b : nat) (a : nat) : term4 b a.
Proof. exact (EQ_MP (@lem3074499 b a) (@lem3074498 a b)). Qed.
Lemma lem3074502 (b : nat) (a : nat) : term4 b a.
Proof. exact (@lem3073456 b a (@lem3074500 b a)). Qed.
Lemma lem3074503 (b : nat) (a : nat) (h1 : term3 b a) : term12.
Proof. exact (@lem3074502 b a (@lem3073441 b a h1)). Qed.
Lemma lem3074504 (b : nat) (a : nat) (h1 : term3 b a) : term8.
Proof. exact (@lem3074503 b a h1 (@lem2307147)). Qed.
Lemma lem3074505 (b : nat) (a : nat) (h1 : term3 b a) : False.
Proof. exact (@lem3074504 b a h1 (@lem2307381)). Qed.
Lemma lem3074506 (b : nat) (a : nat) (h1 : term3 b a) : (term3 b a) = False.
Proof. exact (prop_ext (fun h2 : term3 b a => @lem3074505 b a h1) (fun h2 : False => @lem3073441 b a h1)). Qed.
Lemma lem3074507 (b : nat) (a : nat) (h1 : term3 b a) : False.
Proof. exact (EQ_MP (@lem3074506 b a h1) (@lem3073441 b a h1)). Qed.
Lemma lem3074508 (b : nat) (a : nat) : term2 b a.
Proof. exact (fun h0 : term3 b a => @lem3074507 b a h0). Qed.
Lemma lem3074509 (b : nat) (a : nat) : term1 b a.
Proof. exact (EQ_MP (@lem3073440 b a) (@lem3074508 b a)). Qed.
Lemma lem3074510 (b : nat) (a : nat) (h1 : term35 b a) : term35 b a.
Proof. exact (h1). Qed.
Lemma lem3074515 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem3073386 m n) (@lem3073385 m n)). Qed.
Lemma lem3074516 (b : nat) (a : nat) (x : int) : (b = (term119 a x)) = ((int_of_num b) = (term120 a x)).
Proof. exact (@lem3074515 b (term119 a x)). Qed.
Lemma lem3074518 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = ((term121 m) = (term121 n)).
Proof. exact (EQ_MP (@lem3070957 m n) (@lem3073366 m n)). Qed.
Lemma lem3074519 (b : nat) (a : nat) (x : int) : ((int_of_num b) = (term120 a x)) = ((term121 b) = (term122 a x)).
Proof. exact (@lem3074518 b (term119 a x)). Qed.
Lemma lem3074524 (b : nat) (a : nat) (x : int) : (b = (term119 a x)) = ((term121 b) = (term122 a x)).
Proof. exact (TRANS (@lem3074516 b a x) (@lem3074519 b a x)). Qed.
Lemma lem3074525 (b : nat) (a : nat) (x : int) : ((term121 b) = (term122 a x)) = (b = (term119 a x)).
Proof. exact (SYM (@lem3074524 b a x)). Qed.
Lemma lem3074526 (x : int) : term123 x.
Proof. exact (@lem2300430 x). Qed.
Lemma lem3074527 (x : int) : (term123 x) = (term124 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem3074528 (x : int) : term124 x.
Proof. exact (EQ_MP (@lem3074527 x) (@lem3074526 x)). Qed.
Lemma lem3074529 (x : int) (y : int) : term125 x y.
Proof. exact (@lem3074528 x y). Qed.
Lemma lem3074530 (x : int) (y : int) : (term125 x y) = ((term126 x y) = (term127 x y)).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem3074532 (m : nat) : term128 m.
Proof. exact (@lem3070956 m). Qed.
Lemma lem3074533 (m : nat) : (term128 m) = (term129 m).
Proof. exact (eq_refl (term128 m)). Qed.
Lemma lem3074534 (m : nat) : term129 m.
Proof. exact (EQ_MP (@lem3074533 m) (@lem3074532 m)). Qed.
Lemma lem3074535 (m : nat) (n : nat) : term130 m n.
Proof. exact (@lem3074534 m n). Qed.
Lemma lem3074536 (m : nat) (n : nat) : (term130 m n) = ((term25 m n) = (term24 m n)).
Proof. exact (eq_refl (term130 m n)). Qed.
Lemma lem3074541 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : (int_of_num b) = (term33 a x).
Proof. exact (h1). Qed.
Lemma lem3074542 : int_abs = int_abs.
Proof. exact (eq_refl int_abs). Qed.
Lemma lem3074543 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : (term121 b) = (term131 a x).
Proof. exact (MK_COMB (@lem3074542) (@lem3074541 b a x h1)). Qed.
Lemma lem3074545 (x : int) (y : int) : (term126 x y) = (term127 x y).
Proof. exact (EQ_MP (@lem3074530 x y) (@lem3074529 x y)). Qed.
Lemma lem3074546 (a : nat) (x : int) : (term131 a x) = (term132 a x).
Proof. exact (@lem3074545 (int_of_num a) x). Qed.
Lemma lem3074547 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : (term121 b) = (term132 a x).
Proof. exact (TRANS (@lem3074543 b a x h1) (@lem3074546 a x)). Qed.
Lemma lem3074548 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3074549 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : (term133 b) = (term134 a x).
Proof. exact (MK_COMB (@lem3074548) (@lem3074547 b a x h1)). Qed.
Lemma lem3074551 (m : nat) (n : nat) : (term25 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem3074536 m n) (@lem3074535 m n)). Qed.
Lemma lem3074552 (a : nat) (x : int) : (term120 a x) = (term135 a x).
Proof. exact (@lem3074551 a (term136 x)). Qed.
Lemma lem3074553 : int_abs = int_abs.
Proof. exact (eq_refl int_abs). Qed.
Lemma lem3074554 (a : nat) (x : int) : (term122 a x) = (term137 a x).
Proof. exact (MK_COMB (@lem3074553) (@lem3074552 a x)). Qed.
Lemma lem3074556 (x : int) (y : int) : (term126 x y) = (term127 x y).
Proof. exact (EQ_MP (@lem3074530 x y) (@lem3074529 x y)). Qed.
Lemma lem3074557 (a : nat) (x : int) : (term137 a x) = (term138 a x).
Proof. exact (@lem3074556 (int_of_num a) (term139 x)). Qed.
Lemma lem3074558 (a : nat) (x : int) : (term122 a x) = (term138 a x).
Proof. exact (TRANS (@lem3074554 a x) (@lem3074557 a x)). Qed.
Lemma lem3074559 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : ((term121 b) = (term122 a x)) = ((term132 a x) = (term138 a x)).
Proof. exact (MK_COMB (@lem3074549 b a x h1) (@lem3074558 a x)). Qed.
Lemma lem3074562 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : ((term132 a x) = (term138 a x)) = ((term121 b) = (term122 a x)).
Proof. exact (SYM (@lem3074559 b a x h1)). Qed.
Lemma lem3074566 (x : int) : term140 x.
Proof. exact (fun h0 : term141 x => @lem3070937 x h0). Qed.
Lemma lem3074567 (x : int) : term142 x.
Proof. exact (@lem3074566 (int_abs x)). Qed.
Lemma lem3074569 (x : int) : (term143 x) = True.
Proof. exact (EQ_MP (@lem3070931 x) (@lem3070930 x)). Qed.
Lemma lem3074570 (x : int) : True = (term143 x).
Proof. exact (SYM (@lem3074569 x)). Qed.
Lemma lem3074571 (x : int) : term143 x.
Proof. exact (EQ_MP (@lem3074570 x) (@lem0)). Qed.
Lemma lem3074572 (x : int) : (term139 x) = (int_abs x).
Proof. exact (@lem3074567 x (@lem3074571 x)). Qed.
Lemma lem3074573 : int_abs = int_abs.
Proof. exact (eq_refl int_abs). Qed.
Lemma lem3074574 (x : int) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem3074573) (@lem3074572 x)). Qed.
Lemma lem3074576 (x : int) : (term145 x) = (int_abs x).
Proof. exact (EQ_MP (@lem3070926 x) (@lem3070925 x)). Qed.
Lemma lem3074577 (x : int) : (term144 x) = (int_abs x).
Proof. exact (TRANS (@lem3074574 x) (@lem3074576 x)). Qed.
Lemma lem3074578 (a : nat) : (term146 a) = (term146 a).
Proof. exact (eq_refl (term146 a)). Qed.
Lemma lem3074579 (a : nat) (x : int) : (term138 a x) = (term132 a x).
Proof. exact (MK_COMB (@lem3074578 a) (@lem3074577 x)). Qed.
Lemma lem3074580 (a : nat) (x : int) : (term134 a x) = (term134 a x).
Proof. exact (eq_refl (term134 a x)). Qed.
Lemma lem3074581 (a : nat) (x : int) : ((term132 a x) = (term138 a x)) = ((term132 a x) = (term132 a x)).
Proof. exact (MK_COMB (@lem3074580 a x) (@lem3074579 a x)). Qed.
Lemma lem3074583 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3074584 (x : int) : (x = x) = True.
Proof. exact (@lem3074583 int x). Qed.
Lemma lem3074585 (a : nat) (x : int) : ((term132 a x) = (term132 a x)) = True.
Proof. exact (@lem3074584 (term132 a x)). Qed.
Lemma lem3074586 (a : nat) (x : int) : ((term132 a x) = (term138 a x)) = True.
Proof. exact (TRANS (@lem3074581 a x) (@lem3074585 a x)). Qed.
Lemma lem3074587 (a : nat) (x : int) : True = ((term132 a x) = (term138 a x)).
Proof. exact (SYM (@lem3074586 a x)). Qed.
Lemma lem3074588 (a : nat) (x : int) : (term132 a x) = (term138 a x).
Proof. exact (EQ_MP (@lem3074587 a x) (@lem0)). Qed.
Lemma lem3074589 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : (term121 b) = (term122 a x).
Proof. exact (EQ_MP (@lem3074562 b a x h1) (@lem3074588 a x)). Qed.
Lemma lem3074590 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : b = (term119 a x).
Proof. exact (EQ_MP (@lem3074525 b a x) (@lem3074589 b a x h1)). Qed.
Lemma lem3074591 (b : nat) (a : nat) (x : int) (h1 : (int_of_num b) = (term33 a x)) : term37 b a.
Proof. exact (ex_intro (term36 b a) (term136 x) (@lem3074590 b a x h1)). Qed.
Lemma lem3074592 (b : nat) (a : nat) (h1 : term35 b a) : term37 b a.
Proof. exact (ex_elim (@lem3074510 b a h1) (fun x : int => fun h0 : term34 b a x => @lem3074591 b a x h0)). Qed.
Lemma lem3074593 (b : nat) (a : nat) : term147 b a.
Proof. exact (fun h0 : term35 b a => @lem3074592 b a h0). Qed.
Lemma lem3074594 (b : nat) (a : nat) : term148 b a.
Proof. exact (conj (@lem3074593 b a) (@lem3074509 b a)). Qed.
Lemma lem3074595 (b : nat) (a : nat) : (term148 b a) = ((term35 b a) = (term37 b a)).
Proof. exact (@lem32 (term35 b a) (term37 b a)). Qed.
Lemma lem3074596 (b : nat) (a : nat) : (term35 b a) = (term37 b a).
Proof. exact (EQ_MP (@lem3074595 b a) (@lem3074594 b a)). Qed.
