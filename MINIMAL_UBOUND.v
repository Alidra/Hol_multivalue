Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MINIMAL_UBOUND_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MINIMAL_spec.
Require Import NOT_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
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
Lemma lem278407 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem278408 : term1 = term2.
Proof. exact (@lem278407 term1). Qed.
Lemma lem278409 : term2 = term1.
Proof. exact (SYM (@lem278408)). Qed.
Lemma lem278410 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem278413 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem278414 : term5.
Proof. exact (fun h0 : term4 => @lem278413 h0). Qed.
Lemma lem278415 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem278416 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem278417 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem278415 h2 (@lem278416 h1)). Qed.
Lemma lem278418 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem278417 h1 h0). Qed.
Lemma lem278419 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem278420 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem278418 h1 (@lem278419 h2)). Qed.
Lemma lem278421 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem278420 h0 h1). Qed.
Lemma lem278422 : term7.
Proof. exact (fun h0 : term5 => @lem278421 h0). Qed.
Lemma lem278425 : term5.
Proof. exact (@lem278422 (@lem278414)). Qed.
Lemma lem278449 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem278450 : term8 = term9.
Proof. exact (@lem278449 term10). Qed.
Lemma lem278467 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem278468 : term12 = term13.
Proof. exact (MK_COMB (@lem278467) (@lem278450)). Qed.
Lemma lem278471 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem278478 : term4 = term15.
Proof. exact (MK_COMB (@lem278471) (@lem278468)). Qed.
Lemma lem278485 (P : nat -> Prop) (m : nat) : (term16 P m) = (term16 P m).
Proof. exact (eq_refl (term16 P m)). Qed.
Lemma lem278486 (P : nat -> Prop) : (term17 P) = (term17 P).
Proof. exact (fun_ext (fun m : nat => @lem278485 P m)). Qed.
Lemma lem278487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278488 (P : nat -> Prop) : (term18 P) = (term18 P).
Proof. exact (MK_COMB (@lem278487) (@lem278486 P)). Qed.
Lemma lem278491 (P : nat -> Prop) : (term19 P) = (term19 P).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem278492 (P : nat -> Prop) : (term20 P) = (term20 P).
Proof. exact (MK_COMB (@lem278491 P) (@lem278488 P)). Qed.
Lemma lem278493 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem278494 (P : nat -> Prop) : (term21 P) = (term21 P).
Proof. exact (fun_ext (fun n : nat => @lem278493 P n)). Qed.
Lemma lem278495 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278496 (P : nat -> Prop) : (term22 P) = (term22 P).
Proof. exact (MK_COMB (@lem278495) (@lem278494 P)). Qed.
Lemma lem278497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem278498 (P : nat -> Prop) : (term23 P) = (term23 P).
Proof. exact (MK_COMB (@lem278497) (@lem278496 P)). Qed.
Lemma lem278499 (P : nat -> Prop) : ((term22 P) = (term20 P)) = ((term22 P) = (term20 P)).
Proof. exact (MK_COMB (@lem278498 P) (@lem278492 P)). Qed.
Lemma lem278500 : term24 = term24.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem278499 P)). Qed.
Lemma lem278501 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem278502 : term10 = term10.
Proof. exact (MK_COMB (@lem278501) (@lem278500)). Qed.
Lemma lem278503 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem278504 : term9 = term9.
Proof. exact (MK_COMB (@lem278503) (@lem278502)). Qed.
Lemma lem278511 (n : nat) (m : nat) : ((term25 m n) = (Peano.le n m)) = ((term25 m n) = (Peano.le n m)).
Proof. exact (eq_refl ((term25 m n) = (Peano.le n m))). Qed.
Lemma lem278512 (m : nat) : (term26 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem278511 n m)). Qed.
Lemma lem278513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278514 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem278513) (@lem278512 m)). Qed.
Lemma lem278515 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem278514 m)). Qed.
Lemma lem278516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278517 : term29 = term29.
Proof. exact (MK_COMB (@lem278516) (@lem278515)). Qed.
Lemma lem278518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem278519 : term11 = term11.
Proof. exact (MK_COMB (@lem278518) (@lem278517)). Qed.
Lemma lem278520 : term13 = term13.
Proof. exact (MK_COMB (@lem278519) (@lem278504)). Qed.
Lemma lem278525 (P : nat -> Prop) (n : nat) : (term30 P n) = (term30 P n).
Proof. exact (eq_refl (term30 P n)). Qed.
Lemma lem278526 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (fun_ext (fun n : nat => @lem278525 P n)). Qed.
Lemma lem278527 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278528 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (MK_COMB (@lem278527) (@lem278526 P)). Qed.
Lemma lem278529 : term33 = term33.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem278528 P)). Qed.
Lemma lem278530 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem278531 : term1 = term1.
Proof. exact (MK_COMB (@lem278530) (@lem278529)). Qed.
Lemma lem278532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem278533 : term3 = term3.
Proof. exact (MK_COMB (@lem278532) (@lem278531)). Qed.
Lemma lem278534 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem278535 : term14 = term14.
Proof. exact (MK_COMB (@lem278534) (@lem278533)). Qed.
Lemma lem278536 : term15 = term15.
Proof. exact (MK_COMB (@lem278535) (@lem278520)). Qed.
Lemma lem278591 : term4 = term15.
Proof. exact (TRANS (@lem278478) (@lem278536)). Qed.
Lemma lem278592 : term15 = term4.
Proof. exact (SYM (@lem278591)). Qed.
Lemma lem278593 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem278594 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem278595 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem278602 (P : nat -> Prop) (n : nat) : (term34 P n) = (term35 P n).
Proof. exact (@lem17362 (P n) (term36 P n)). Qed.
Lemma lem278603 (P : nat -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem278604 (P : nat -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem278603 (term31 P)). Qed.
Lemma lem278605 (P : nat -> Prop) (n : nat) : (term41 P n) = (term30 P n).
Proof. exact (eq_refl (term41 P n)). Qed.
Lemma lem278606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem278607 (P : nat -> Prop) (n : nat) : (term42 P n) = (term34 P n).
Proof. exact (MK_COMB (@lem278606) (@lem278605 P n)). Qed.
Lemma lem278608 (P : nat -> Prop) (n : nat) : (term42 P n) = (term35 P n).
Proof. exact (TRANS (@lem278607 P n) (@lem278602 P n)). Qed.
Lemma lem278609 (P : nat -> Prop) : (term43 P) = (term44 P).
Proof. exact (fun_ext (fun n : nat => @lem278608 P n)). Qed.
Lemma lem278610 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278611 (P : nat -> Prop) : (term40 P) = (term45 P).
Proof. exact (MK_COMB (@lem278610) (@lem278609 P)). Qed.
Lemma lem278612 (P : nat -> Prop) : (term39 P) = (term45 P).
Proof. exact (TRANS (@lem278604 P) (@lem278611 P)). Qed.
Lemma lem278613 (P : type993) : (term46 P) = (term47 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem278614 : term3 = term48.
Proof. exact (@lem278613 term33). Qed.
Lemma lem278615 (P : nat -> Prop) : (term49 P) = (term32 P).
Proof. exact (eq_refl (term49 P)). Qed.
Lemma lem278616 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem278617 (P : nat -> Prop) : (term50 P) = (term39 P).
Proof. exact (MK_COMB (@lem278616) (@lem278615 P)). Qed.
Lemma lem278618 (P : nat -> Prop) : (term50 P) = (term45 P).
Proof. exact (TRANS (@lem278617 P) (@lem278612 P)). Qed.
Lemma lem278619 : term51 = term52.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem278618 P)). Qed.
Lemma lem278620 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem278621 : term48 = term53.
Proof. exact (MK_COMB (@lem278620) (@lem278619)). Qed.
Lemma lem278658 : term3 = term53.
Proof. exact (TRANS (@lem278614) (@lem278621)). Qed.
Lemma lem278659 (h1 : term3) : term53.
Proof. exact (EQ_MP (@lem278658) (@lem278593 h1)). Qed.
Lemma lem278663 (m : nat) (n : nat) : (term54 m n) = (Peano.lt m n).
Proof. exact (@lem16933 (Peano.lt m n)). Qed.
Lemma lem278665 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem278666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem278667 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem278666) (@lem278663 m n)). Qed.
Lemma lem278668 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem278667 m n) (@lem278665 n m)). Qed.
Lemma lem278673 (n : nat) (m : nat) : (term59 n m) = (term59 n m).
Proof. exact (eq_refl (term59 n m)). Qed.
Lemma lem278674 (n : nat) (m : nat) : (term60 n m) = (term61 n m).
Proof. exact (MK_COMB (@lem278673 n m) (@lem278668 n m)). Qed.
Lemma lem278675 (n : nat) (m : nat) : ((term25 m n) = (Peano.le n m)) = (term60 n m).
Proof. exact (@lem17784 (term25 m n) (Peano.le n m)). Qed.
Lemma lem278676 (n : nat) (m : nat) : ((term25 m n) = (Peano.le n m)) = (term61 n m).
Proof. exact (TRANS (@lem278675 n m) (@lem278674 n m)). Qed.
Lemma lem278677 (m : nat) : (term26 m) = (term62 m).
Proof. exact (fun_ext (fun n : nat => @lem278676 n m)). Qed.
Lemma lem278678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278679 (m : nat) : (term27 m) = (term63 m).
Proof. exact (MK_COMB (@lem278678) (@lem278677 m)). Qed.
Lemma lem278680 : term28 = term64.
Proof. exact (fun_ext (fun m : nat => @lem278679 m)). Qed.
Lemma lem278681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278682 : term29 = term65.
Proof. exact (MK_COMB (@lem278681) (@lem278680)). Qed.
Lemma lem278688 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem278689 (P : nat -> Prop) (Q : nat -> Prop) : (term68 P Q) = (term69 P Q).
Proof. exact (@lem278688 nat P Q). Qed.
Lemma lem278690 (m : nat) : (term70 m) = (term71 m).
Proof. exact (@lem278689 (term72 m) (term73 m)). Qed.
Lemma lem278691 (n : nat) (m : nat) : (term74 m n) = (term75 n m).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem278692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem278693 (n : nat) (m : nat) : (term76 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem278692) (@lem278691 n m)). Qed.
Lemma lem278694 (n : nat) (m : nat) : (term77 m n) = (term58 n m).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem278695 (n : nat) (m : nat) : (term78 m n) = (term61 n m).
Proof. exact (MK_COMB (@lem278693 n m) (@lem278694 n m)). Qed.
Lemma lem278696 (m : nat) : (term79 m) = (term62 m).
Proof. exact (fun_ext (fun n : nat => @lem278695 n m)). Qed.
Lemma lem278697 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278698 (m : nat) : (term70 m) = (term63 m).
Proof. exact (MK_COMB (@lem278697) (@lem278696 m)). Qed.
Lemma lem278699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem278700 (m : nat) : (term80 m) = (term81 m).
Proof. exact (MK_COMB (@lem278699) (@lem278698 m)). Qed.
Lemma lem278701 (n : nat) (m : nat) : (term74 m n) = (term75 n m).
Proof. exact (eq_refl (term74 m n)). Qed.
Lemma lem278702 (m : nat) : (term82 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem278701 n m)). Qed.
Lemma lem278703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278704 (m : nat) : (term83 m) = (term84 m).
Proof. exact (MK_COMB (@lem278703) (@lem278702 m)). Qed.
Lemma lem278705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem278706 (m : nat) : (term85 m) = (term86 m).
Proof. exact (MK_COMB (@lem278705) (@lem278704 m)). Qed.
Lemma lem278707 (n : nat) (m : nat) : (term77 m n) = (term58 n m).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem278708 (m : nat) : (term87 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem278707 n m)). Qed.
Lemma lem278709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278710 (m : nat) : (term88 m) = (term89 m).
Proof. exact (MK_COMB (@lem278709) (@lem278708 m)). Qed.
Lemma lem278711 (m : nat) : (term71 m) = (term90 m).
Proof. exact (MK_COMB (@lem278706 m) (@lem278710 m)). Qed.
Lemma lem278712 (m : nat) : ((term70 m) = (term71 m)) = ((term63 m) = (term90 m)).
Proof. exact (MK_COMB (@lem278700 m) (@lem278711 m)). Qed.
Lemma lem278713 (m : nat) : (term63 m) = (term90 m).
Proof. exact (EQ_MP (@lem278712 m) (@lem278690 m)). Qed.
Lemma lem278810 : term64 = term91.
Proof. exact (fun_ext (fun m : nat => @lem278713 m)). Qed.
Lemma lem278811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278812 : term65 = term92.
Proof. exact (MK_COMB (@lem278811) (@lem278810)). Qed.
Lemma lem278814 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem278815 (P : nat -> Prop) (Q : nat -> Prop) : (term68 P Q) = (term69 P Q).
Proof. exact (@lem278814 nat P Q). Qed.
Lemma lem278816 : term93 = term94.
Proof. exact (@lem278815 term95 term96). Qed.
Lemma lem278817 (m : nat) : (term97 m) = (term84 m).
Proof. exact (eq_refl (term97 m)). Qed.
Lemma lem278818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem278819 (m : nat) : (term98 m) = (term86 m).
Proof. exact (MK_COMB (@lem278818) (@lem278817 m)). Qed.
Lemma lem278820 (m : nat) : (term99 m) = (term89 m).
Proof. exact (eq_refl (term99 m)). Qed.
Lemma lem278821 (m : nat) : (term100 m) = (term90 m).
Proof. exact (MK_COMB (@lem278819 m) (@lem278820 m)). Qed.
Lemma lem278822 : term101 = term91.
Proof. exact (fun_ext (fun m : nat => @lem278821 m)). Qed.
Lemma lem278823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278824 : term93 = term92.
Proof. exact (MK_COMB (@lem278823) (@lem278822)). Qed.
Lemma lem278825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem278826 : term102 = term103.
Proof. exact (MK_COMB (@lem278825) (@lem278824)). Qed.
Lemma lem278827 (m : nat) : (term97 m) = (term84 m).
Proof. exact (eq_refl (term97 m)). Qed.
Lemma lem278828 : term104 = term95.
Proof. exact (fun_ext (fun m : nat => @lem278827 m)). Qed.
Lemma lem278829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278830 : term105 = term106.
Proof. exact (MK_COMB (@lem278829) (@lem278828)). Qed.
Lemma lem278831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem278832 : term107 = term108.
Proof. exact (MK_COMB (@lem278831) (@lem278830)). Qed.
Lemma lem278833 (m : nat) : (term99 m) = (term89 m).
Proof. exact (eq_refl (term99 m)). Qed.
Lemma lem278834 : term109 = term96.
Proof. exact (fun_ext (fun m : nat => @lem278833 m)). Qed.
Lemma lem278835 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278836 : term110 = term111.
Proof. exact (MK_COMB (@lem278835) (@lem278834)). Qed.
Lemma lem278837 : term94 = term112.
Proof. exact (MK_COMB (@lem278832) (@lem278836)). Qed.
Lemma lem278838 : (term93 = term94) = (term92 = term112).
Proof. exact (MK_COMB (@lem278826) (@lem278837)). Qed.
Lemma lem278839 : term92 = term112.
Proof. exact (EQ_MP (@lem278838) (@lem278816)). Qed.
Lemma lem278946 : term65 = term112.
Proof. exact (TRANS (@lem278812) (@lem278839)). Qed.
Lemma lem278947 : term29 = term112.
Proof. exact (TRANS (@lem278682) (@lem278946)). Qed.
Lemma lem278948 (h1 : term29) : term112.
Proof. exact (EQ_MP (@lem278947) (@lem278594 h1)). Qed.
Lemma lem278950 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem278951 (P : nat -> Prop) : (term113 P) = (term114 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem278952 (P : nat -> Prop) : (term115 P) = (term116 P).
Proof. exact (@lem278951 (term21 P)). Qed.
Lemma lem278953 (P : nat -> Prop) (n : nat) : (term117 P n) = (P n).
Proof. exact (eq_refl (term117 P n)). Qed.
Lemma lem278954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem278956 (P : nat -> Prop) (n : nat) : (term118 P n) = (term119 P n).
Proof. exact (MK_COMB (@lem278954) (@lem278953 P n)). Qed.
Lemma lem278957 (P : nat -> Prop) : (term120 P) = (term121 P).
Proof. exact (fun_ext (fun n : nat => @lem278956 P n)). Qed.
Lemma lem278958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278959 (P : nat -> Prop) : (term116 P) = (term114 P).
Proof. exact (MK_COMB (@lem278958) (@lem278957 P)). Qed.
Lemma lem278960 (P : nat -> Prop) : (term115 P) = (term114 P).
Proof. exact (TRANS (@lem278952 P) (@lem278959 P)). Qed.
Lemma lem278961 (P : nat -> Prop) : (term21 P) = (term21 P).
Proof. exact (fun_ext (fun n : nat => @lem278950 P n)). Qed.
Lemma lem278962 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278963 (P : nat -> Prop) : (term22 P) = (term22 P).
Proof. exact (MK_COMB (@lem278962) (@lem278961 P)). Qed.
Lemma lem278971 (P : nat -> Prop) (m : nat) : (term122 P m) = (P m).
Proof. exact (@lem16933 (P m)). Qed.
Lemma lem278973 (m : nat) (P : nat -> Prop) : (term123 m P) = (term123 m P).
Proof. exact (eq_refl (term123 m P)). Qed.
Lemma lem278974 (P : nat -> Prop) (m : nat) : (term124 P m) = (term125 P m).
Proof. exact (MK_COMB (@lem278973 m P) (@lem278971 P m)). Qed.
Lemma lem278975 (P : nat -> Prop) (m : nat) : (term126 P m) = (term124 P m).
Proof. exact (@lem17362 (term127 m P) (term119 P m)). Qed.
Lemma lem278976 (P : nat -> Prop) (m : nat) : (term126 P m) = (term125 P m).
Proof. exact (TRANS (@lem278975 P m) (@lem278974 P m)). Qed.
Lemma lem278981 (P : nat -> Prop) (m : nat) : (term16 P m) = (term128 P m).
Proof. exact (@lem17265 (term127 m P) (term119 P m)). Qed.
Lemma lem278982 (P : nat -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem278983 (P : nat -> Prop) : (term129 P) = (term130 P).
Proof. exact (@lem278982 (term17 P)). Qed.
Lemma lem278984 (P : nat -> Prop) (m : nat) : (term131 P m) = (term16 P m).
Proof. exact (eq_refl (term131 P m)). Qed.
Lemma lem278985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem278986 (P : nat -> Prop) (m : nat) : (term132 P m) = (term126 P m).
Proof. exact (MK_COMB (@lem278985) (@lem278984 P m)). Qed.
Lemma lem278987 (P : nat -> Prop) (m : nat) : (term132 P m) = (term125 P m).
Proof. exact (TRANS (@lem278986 P m) (@lem278976 P m)). Qed.
Lemma lem278988 (P : nat -> Prop) : (term133 P) = (term134 P).
Proof. exact (fun_ext (fun m : nat => @lem278987 P m)). Qed.
Lemma lem278989 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem278990 (P : nat -> Prop) : (term130 P) = (term135 P).
Proof. exact (MK_COMB (@lem278989) (@lem278988 P)). Qed.
Lemma lem278991 (P : nat -> Prop) : (term129 P) = (term135 P).
Proof. exact (TRANS (@lem278983 P) (@lem278990 P)). Qed.
Lemma lem278992 (P : nat -> Prop) : (term17 P) = (term136 P).
Proof. exact (fun_ext (fun m : nat => @lem278981 P m)). Qed.
Lemma lem278993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem278994 (P : nat -> Prop) : (term18 P) = (term137 P).
Proof. exact (MK_COMB (@lem278993) (@lem278992 P)). Qed.
Lemma lem278996 (P : nat -> Prop) : (term138 P) = (term138 P).
Proof. exact (eq_refl (term138 P)). Qed.
Lemma lem278997 (P : nat -> Prop) : (term139 P) = (term140 P).
Proof. exact (MK_COMB (@lem278996 P) (@lem278991 P)). Qed.
Lemma lem278998 (P : nat -> Prop) : (term141 P) = (term139 P).
Proof. exact (@lem17045 (term142 P) (term18 P)). Qed.
Lemma lem278999 (P : nat -> Prop) : (term141 P) = (term140 P).
Proof. exact (TRANS (@lem278998 P) (@lem278997 P)). Qed.
Lemma lem279001 (P : nat -> Prop) : (term19 P) = (term19 P).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem279002 (P : nat -> Prop) : (term20 P) = (term143 P).
Proof. exact (MK_COMB (@lem279001 P) (@lem278994 P)). Qed.
Lemma lem279003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279004 (P : nat -> Prop) : (term144 P) = (term145 P).
Proof. exact (MK_COMB (@lem279003) (@lem278960 P)). Qed.
Lemma lem279005 (P : nat -> Prop) : (term146 P) = (term147 P).
Proof. exact (MK_COMB (@lem279004 P) (@lem279002 P)). Qed.
Lemma lem279006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279007 (P : nat -> Prop) : (term148 P) = (term148 P).
Proof. exact (MK_COMB (@lem279006) (@lem278963 P)). Qed.
Lemma lem279008 (P : nat -> Prop) : (term149 P) = (term150 P).
Proof. exact (MK_COMB (@lem279007 P) (@lem278999 P)). Qed.
Lemma lem279009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279010 (P : nat -> Prop) : (term151 P) = (term152 P).
Proof. exact (MK_COMB (@lem279009) (@lem279008 P)). Qed.
Lemma lem279011 (P : nat -> Prop) : (term153 P) = (term154 P).
Proof. exact (MK_COMB (@lem279010 P) (@lem279005 P)). Qed.
Lemma lem279012 (P : nat -> Prop) : ((term22 P) = (term20 P)) = (term153 P).
Proof. exact (@lem17784 (term22 P) (term20 P)). Qed.
Lemma lem279013 (P : nat -> Prop) : ((term22 P) = (term20 P)) = (term154 P).
Proof. exact (TRANS (@lem279012 P) (@lem279011 P)). Qed.
Lemma lem279014 : term24 = term155.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279013 P)). Qed.
Lemma lem279015 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279016 : term10 = term156.
Proof. exact (MK_COMB (@lem279015) (@lem279014)). Qed.
Lemma lem279018 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem279019 (P : type993) (Q : type993) : (term157 P Q) = (term158 P Q).
Proof. exact (@lem279018 (nat -> Prop) P Q). Qed.
Lemma lem279020 : term159 = term160.
Proof. exact (@lem279019 term161 term162). Qed.
Lemma lem279021 (P : nat -> Prop) : (term163 P) = (term150 P).
Proof. exact (eq_refl (term163 P)). Qed.
Lemma lem279022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279023 (P : nat -> Prop) : (term164 P) = (term152 P).
Proof. exact (MK_COMB (@lem279022) (@lem279021 P)). Qed.
Lemma lem279024 (P : nat -> Prop) : (term165 P) = (term147 P).
Proof. exact (eq_refl (term165 P)). Qed.
Lemma lem279025 (P : nat -> Prop) : (term166 P) = (term154 P).
Proof. exact (MK_COMB (@lem279023 P) (@lem279024 P)). Qed.
Lemma lem279026 : term167 = term155.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279025 P)). Qed.
Lemma lem279027 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279028 : term159 = term156.
Proof. exact (MK_COMB (@lem279027) (@lem279026)). Qed.
Lemma lem279029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279030 : term168 = term169.
Proof. exact (MK_COMB (@lem279029) (@lem279028)). Qed.
Lemma lem279031 (P : nat -> Prop) : (term163 P) = (term150 P).
Proof. exact (eq_refl (term163 P)). Qed.
Lemma lem279032 : term170 = term161.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279031 P)). Qed.
Lemma lem279033 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279034 : term171 = term172.
Proof. exact (MK_COMB (@lem279033) (@lem279032)). Qed.
Lemma lem279035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279036 : term173 = term174.
Proof. exact (MK_COMB (@lem279035) (@lem279034)). Qed.
Lemma lem279037 (P : nat -> Prop) : (term165 P) = (term147 P).
Proof. exact (eq_refl (term165 P)). Qed.
Lemma lem279038 : term175 = term162.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279037 P)). Qed.
Lemma lem279039 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279040 : term176 = term177.
Proof. exact (MK_COMB (@lem279039) (@lem279038)). Qed.
Lemma lem279041 : term160 = term178.
Proof. exact (MK_COMB (@lem279036) (@lem279040)). Qed.
Lemma lem279042 : (term159 = term160) = (term156 = term178).
Proof. exact (MK_COMB (@lem279030) (@lem279041)). Qed.
Lemma lem279043 : term156 = term178.
Proof. exact (EQ_MP (@lem279042) (@lem279020)). Qed.
Lemma lem279229 {A : Type'} (P : Prop) (Q : A -> Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem279230 (P : Prop) (Q : nat -> Prop) : (term181 P Q) = (term182 P Q).
Proof. exact (@lem279229 nat P Q). Qed.
Lemma lem279231 (P : nat -> Prop) : (term183 P) = (term184 P).
Proof. exact (@lem279230 (term185 P) (term134 P)). Qed.
Lemma lem279232 (P : nat -> Prop) (m : nat) : (term186 P m) = (term125 P m).
Proof. exact (eq_refl (term186 P m)). Qed.
Lemma lem279233 (P : nat -> Prop) : (term187 P) = (term134 P).
Proof. exact (fun_ext (fun m : nat => @lem279232 P m)). Qed.
Lemma lem279234 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem279235 (P : nat -> Prop) : (term188 P) = (term135 P).
Proof. exact (MK_COMB (@lem279234) (@lem279233 P)). Qed.
Lemma lem279236 (P : nat -> Prop) : (term138 P) = (term138 P).
Proof. exact (eq_refl (term138 P)). Qed.
Lemma lem279237 (P : nat -> Prop) : (term183 P) = (term140 P).
Proof. exact (MK_COMB (@lem279236 P) (@lem279235 P)). Qed.
Lemma lem279238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279239 (P : nat -> Prop) : (term189 P) = (term190 P).
Proof. exact (MK_COMB (@lem279238) (@lem279237 P)). Qed.
Lemma lem279240 (P : nat -> Prop) (m : nat) : (term186 P m) = (term125 P m).
Proof. exact (eq_refl (term186 P m)). Qed.
Lemma lem279241 (P : nat -> Prop) : (term138 P) = (term138 P).
Proof. exact (eq_refl (term138 P)). Qed.
Lemma lem279242 (P : nat -> Prop) (m : nat) : (term191 P m) = (term192 P m).
Proof. exact (MK_COMB (@lem279241 P) (@lem279240 P m)). Qed.
Lemma lem279243 (P : nat -> Prop) : (term193 P) = (term194 P).
Proof. exact (fun_ext (fun m : nat => @lem279242 P m)). Qed.
Lemma lem279244 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem279245 (P : nat -> Prop) : (term184 P) = (term195 P).
Proof. exact (MK_COMB (@lem279244) (@lem279243 P)). Qed.
Lemma lem279246 (P : nat -> Prop) : ((term183 P) = (term184 P)) = ((term140 P) = (term195 P)).
Proof. exact (MK_COMB (@lem279239 P) (@lem279245 P)). Qed.
Lemma lem279247 (P : nat -> Prop) : (term140 P) = (term195 P).
Proof. exact (EQ_MP (@lem279246 P) (@lem279231 P)). Qed.
Lemma lem279248 (P : nat -> Prop) : (term148 P) = (term148 P).
Proof. exact (eq_refl (term148 P)). Qed.
Lemma lem279249 (P : nat -> Prop) : (term150 P) = (term196 P).
Proof. exact (MK_COMB (@lem279248 P) (@lem279247 P)). Qed.
Lemma lem279251 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem279252 (P : nat -> Prop) (Q : nat -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem279251 nat P Q). Qed.
Lemma lem279253 (P : nat -> Prop) : (term201 P) = (term202 P).
Proof. exact (@lem279252 P (term194 P)). Qed.
Lemma lem279254 (P : nat -> Prop) (n : nat) : (term203 P n) = (term192 P n).
Proof. exact (eq_refl (term203 P n)). Qed.
Lemma lem279255 (P : nat -> Prop) : (term204 P) = (term194 P).
Proof. exact (fun_ext (fun n : nat => @lem279254 P n)). Qed.
Lemma lem279256 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem279257 (P : nat -> Prop) : (term205 P) = (term195 P).
Proof. exact (MK_COMB (@lem279256) (@lem279255 P)). Qed.
Lemma lem279258 (P : nat -> Prop) : (term148 P) = (term148 P).
Proof. exact (eq_refl (term148 P)). Qed.
Lemma lem279259 (P : nat -> Prop) : (term201 P) = (term196 P).
Proof. exact (MK_COMB (@lem279258 P) (@lem279257 P)). Qed.
Lemma lem279260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279261 (P : nat -> Prop) : (term206 P) = (term207 P).
Proof. exact (MK_COMB (@lem279260) (@lem279259 P)). Qed.
Lemma lem279262 (P : nat -> Prop) (n : nat) : (term203 P n) = (term192 P n).
Proof. exact (eq_refl (term203 P n)). Qed.
Lemma lem279263 (P : nat -> Prop) (n : nat) : (term208 P n) = (term208 P n).
Proof. exact (eq_refl (term208 P n)). Qed.
Lemma lem279264 (P : nat -> Prop) (n : nat) : (term209 P n) = (term210 P n).
Proof. exact (MK_COMB (@lem279263 P n) (@lem279262 P n)). Qed.
Lemma lem279265 (P : nat -> Prop) : (term211 P) = (term212 P).
Proof. exact (fun_ext (fun n : nat => @lem279264 P n)). Qed.
Lemma lem279266 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem279267 (P : nat -> Prop) : (term202 P) = (term213 P).
Proof. exact (MK_COMB (@lem279266) (@lem279265 P)). Qed.
Lemma lem279268 (P : nat -> Prop) : ((term201 P) = (term202 P)) = ((term196 P) = (term213 P)).
Proof. exact (MK_COMB (@lem279261 P) (@lem279267 P)). Qed.
Lemma lem279269 (P : nat -> Prop) : (term196 P) = (term213 P).
Proof. exact (EQ_MP (@lem279268 P) (@lem279253 P)). Qed.
Lemma lem279272 (P : nat -> Prop) : (term214 P) = (term214 P).
Proof. exact (eq_refl (term214 P)). Qed.
Lemma lem279273 (P : nat -> Prop) : (term214 P) = ((term196 P) = (term213 P)).
Proof. exact (eq_refl (term214 P)). Qed.
Lemma lem279274 (P : nat -> Prop) : (term215 P) = (term215 P).
Proof. exact (eq_refl (term215 P)). Qed.
Lemma lem279275 (P : nat -> Prop) : ((term214 P) = (term214 P)) = ((term214 P) = ((term196 P) = (term213 P))).
Proof. exact (MK_COMB (@lem279274 P) (@lem279273 P)). Qed.
Lemma lem279276 (P : nat -> Prop) : (term214 P) = ((term196 P) = (term213 P)).
Proof. exact (eq_refl (term214 P)). Qed.
Lemma lem279277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279278 (P : nat -> Prop) : (term215 P) = (term216 P).
Proof. exact (MK_COMB (@lem279277) (@lem279276 P)). Qed.
Lemma lem279279 (P : nat -> Prop) : ((term196 P) = (term213 P)) = ((term196 P) = (term213 P)).
Proof. exact (eq_refl ((term196 P) = (term213 P))). Qed.
Lemma lem279280 (P : nat -> Prop) : ((term214 P) = ((term196 P) = (term213 P))) = (((term196 P) = (term213 P)) = ((term196 P) = (term213 P))).
Proof. exact (MK_COMB (@lem279278 P) (@lem279279 P)). Qed.
Lemma lem279281 (P : nat -> Prop) : ((term214 P) = (term214 P)) = (((term196 P) = (term213 P)) = ((term196 P) = (term213 P))).
Proof. exact (TRANS (@lem279275 P) (@lem279280 P)). Qed.
Lemma lem279282 (P : nat -> Prop) : ((term196 P) = (term213 P)) = ((term196 P) = (term213 P)).
Proof. exact (EQ_MP (@lem279281 P) (@lem279272 P)). Qed.
Lemma lem279283 (P : nat -> Prop) : (term196 P) = (term213 P).
Proof. exact (EQ_MP (@lem279282 P) (@lem279269 P)). Qed.
Lemma lem279284 (P : nat -> Prop) : (term150 P) = (term213 P).
Proof. exact (TRANS (@lem279249 P) (@lem279283 P)). Qed.
Lemma lem279285 : term161 = term217.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279284 P)). Qed.
Lemma lem279286 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279287 : term172 = term218.
Proof. exact (MK_COMB (@lem279286) (@lem279285)). Qed.
Lemma lem279289 {A B : Type'} (P : type1413 A B) : (term219 A B P) = (term220 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem279290 (P : type991) : (term221 P) = (term222 P).
Proof. exact (@lem279289 (nat -> Prop) nat P). Qed.
Lemma lem279291 : term223 = term224.
Proof. exact (@lem279290 term225). Qed.
Lemma lem279292 (P : nat -> Prop) : (term226 P) = (term212 P).
Proof. exact (eq_refl (term226 P)). Qed.
Lemma lem279293 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem279294 (P : nat -> Prop) (n : nat) : (term227 P n) = (term228 P n).
Proof. exact (MK_COMB (@lem279292 P) (@lem279293 n)). Qed.
Lemma lem279295 (P : nat -> Prop) (n : nat) : (term228 P n) = (term210 P n).
Proof. exact (eq_refl (term228 P n)). Qed.
Lemma lem279296 (P : nat -> Prop) (n : nat) : (term227 P n) = (term210 P n).
Proof. exact (TRANS (@lem279294 P n) (@lem279295 P n)). Qed.
Lemma lem279297 (P : nat -> Prop) : (term229 P) = (term212 P).
Proof. exact (fun_ext (fun n : nat => @lem279296 P n)). Qed.
Lemma lem279298 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem279299 (P : nat -> Prop) : (term230 P) = (term213 P).
Proof. exact (MK_COMB (@lem279298) (@lem279297 P)). Qed.
Lemma lem279300 : term231 = term217.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279299 P)). Qed.
Lemma lem279301 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279302 : term223 = term218.
Proof. exact (MK_COMB (@lem279301) (@lem279300)). Qed.
Lemma lem279303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279304 : term232 = term233.
Proof. exact (MK_COMB (@lem279303) (@lem279302)). Qed.
Lemma lem279305 (P : nat -> Prop) : (term226 P) = (term212 P).
Proof. exact (eq_refl (term226 P)). Qed.
Lemma lem279306 (n : type994) (P : nat -> Prop) : (n P) = (n P).
Proof. exact (eq_refl (n P)). Qed.
Lemma lem279307 (n : type994) (P : nat -> Prop) : (term234 n P) = (term235 n P).
Proof. exact (MK_COMB (@lem279305 P) (@lem279306 n P)). Qed.
Lemma lem279308 (n : type994) (P : nat -> Prop) : (term235 n P) = (term236 n P).
Proof. exact (eq_refl (term235 n P)). Qed.
Lemma lem279309 (n : type994) (P : nat -> Prop) : (term234 n P) = (term236 n P).
Proof. exact (TRANS (@lem279307 n P) (@lem279308 n P)). Qed.
Lemma lem279310 (n : type994) : (term237 n) = (term238 n).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279309 n P)). Qed.
Lemma lem279311 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279312 (n : type994) : (term239 n) = (term240 n).
Proof. exact (MK_COMB (@lem279311) (@lem279310 n)). Qed.
Lemma lem279313 : term241 = term242.
Proof. exact (fun_ext (fun n : type994 => @lem279312 n)). Qed.
Lemma lem279314 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem279315 : term224 = term243.
Proof. exact (MK_COMB (@lem279314) (@lem279313)). Qed.
Lemma lem279316 : (term223 = term224) = (term218 = term243).
Proof. exact (MK_COMB (@lem279304) (@lem279315)). Qed.
Lemma lem279317 : term218 = term243.
Proof. exact (EQ_MP (@lem279316) (@lem279291)). Qed.
Lemma lem279318 : term172 = term243.
Proof. exact (TRANS (@lem279287) (@lem279317)). Qed.
Lemma lem279319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279320 : term174 = term244.
Proof. exact (MK_COMB (@lem279319) (@lem279318)). Qed.
Lemma lem279321 : term177 = term177.
Proof. exact (eq_refl term177). Qed.
Lemma lem279322 : term178 = term245.
Proof. exact (MK_COMB (@lem279320) (@lem279321)). Qed.
Lemma lem279324 {A : Type'} (P : A -> Prop) (Q : Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem279325 (P : type252) (Q : Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem279324 type994 P Q). Qed.
Lemma lem279326 : term250 = term251.
Proof. exact (@lem279325 term242 term177). Qed.
Lemma lem279327 (n : type994) : (term252 n) = (term240 n).
Proof. exact (eq_refl (term252 n)). Qed.
Lemma lem279328 : term253 = term242.
Proof. exact (fun_ext (fun n : type994 => @lem279327 n)). Qed.
Lemma lem279329 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem279330 : term254 = term243.
Proof. exact (MK_COMB (@lem279329) (@lem279328)). Qed.
Lemma lem279331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279332 : term255 = term244.
Proof. exact (MK_COMB (@lem279331) (@lem279330)). Qed.
Lemma lem279333 : term177 = term177.
Proof. exact (eq_refl term177). Qed.
Lemma lem279334 : term250 = term245.
Proof. exact (MK_COMB (@lem279332) (@lem279333)). Qed.
Lemma lem279335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279336 : term256 = term257.
Proof. exact (MK_COMB (@lem279335) (@lem279334)). Qed.
Lemma lem279337 (n : type994) : (term252 n) = (term240 n).
Proof. exact (eq_refl (term252 n)). Qed.
Lemma lem279338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279339 (n : type994) : (term258 n) = (term259 n).
Proof. exact (MK_COMB (@lem279338) (@lem279337 n)). Qed.
Lemma lem279340 : term177 = term177.
Proof. exact (eq_refl term177). Qed.
Lemma lem279341 (n : type994) : (term260 n) = (term261 n).
Proof. exact (MK_COMB (@lem279339 n) (@lem279340)). Qed.
Lemma lem279342 : term262 = term263.
Proof. exact (fun_ext (fun n : type994 => @lem279341 n)). Qed.
Lemma lem279343 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem279344 : term251 = term264.
Proof. exact (MK_COMB (@lem279343) (@lem279342)). Qed.
Lemma lem279345 : (term250 = term251) = (term245 = term264).
Proof. exact (MK_COMB (@lem279336) (@lem279344)). Qed.
Lemma lem279346 : term245 = term264.
Proof. exact (EQ_MP (@lem279345) (@lem279326)). Qed.
Lemma lem279347 : term178 = term264.
Proof. exact (TRANS (@lem279322) (@lem279346)). Qed.
Lemma lem279348 : term156 = term264.
Proof. exact (TRANS (@lem279043) (@lem279347)). Qed.
Lemma lem279349 : term10 = term264.
Proof. exact (TRANS (@lem279016) (@lem279348)). Qed.
Lemma lem279350 (h1 : term10) : term264.
Proof. exact (EQ_MP (@lem279349) (@lem278595 h1)). Qed.
Lemma lem279351 (n : type994) (h1 : term261 n) : term261 n.
Proof. exact (h1). Qed.
Lemma lem279352 (P : nat -> Prop) (h1 : term45 P) : term45 P.
Proof. exact (h1). Qed.
Lemma lem279353 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : term35 P n'.
Proof. exact (h1). Qed.
Lemma lem279360 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279361 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem279360 nat (nat -> Prop) f x). Qed.
Lemma lem279362 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem279361 Peano.le n). Qed.
Lemma lem279363 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem279364 (n : nat) (m : nat) : (Peano.le n m) = (@I (nat -> nat -> Prop) Peano.le n m).
Proof. exact (MK_COMB (@lem279362 n) (@lem279363 m)). Qed.
Lemma lem279366 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279367 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279366 nat Prop f x). Qed.
Lemma lem279368 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.le n m) = (term265 n m).
Proof. exact (@lem279367 (@I (nat -> nat -> Prop) Peano.le n) m). Qed.
Lemma lem279370 (n : nat) (m : nat) : (Peano.le n m) = (term265 n m).
Proof. exact (TRANS (@lem279364 n m) (@lem279368 n m)). Qed.
Lemma lem279377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279378 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem279377 nat (nat -> Prop) f x). Qed.
Lemma lem279379 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem279378 Peano.lt m). Qed.
Lemma lem279380 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem279381 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem279379 m) (@lem279380 n)). Qed.
Lemma lem279383 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279384 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279383 nat Prop f x). Qed.
Lemma lem279385 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term266 m n).
Proof. exact (@lem279384 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem279387 (m : nat) (n : nat) : (Peano.lt m n) = (term266 m n).
Proof. exact (TRANS (@lem279381 m n) (@lem279385 m n)). Qed.
Lemma lem279388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279389 (m : nat) (n : nat) : (term56 m n) = (term267 m n).
Proof. exact (MK_COMB (@lem279388) (@lem279387 m n)). Qed.
Lemma lem279390 (n : nat) (m : nat) : (term58 n m) = (term268 n m).
Proof. exact (MK_COMB (@lem279389 m n) (@lem279370 n m)). Qed.
Lemma lem279391 (m : nat) : (term73 m) = (term269 m).
Proof. exact (fun_ext (fun n : nat => @lem279390 n m)). Qed.
Lemma lem279392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279393 (m : nat) : (term89 m) = (term270 m).
Proof. exact (MK_COMB (@lem279392) (@lem279391 m)). Qed.
Lemma lem279394 : term96 = term271.
Proof. exact (fun_ext (fun m : nat => @lem279393 m)). Qed.
Lemma lem279395 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279396 : term111 = term272.
Proof. exact (MK_COMB (@lem279395) (@lem279394)). Qed.
Lemma lem279397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem279404 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279405 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem279404 nat (nat -> Prop) f x). Qed.
Lemma lem279406 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem279405 Peano.le n). Qed.
Lemma lem279407 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem279408 (n : nat) (m : nat) : (Peano.le n m) = (@I (nat -> nat -> Prop) Peano.le n m).
Proof. exact (MK_COMB (@lem279406 n) (@lem279407 m)). Qed.
Lemma lem279410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279411 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279410 nat Prop f x). Qed.
Lemma lem279412 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.le n m) = (term265 n m).
Proof. exact (@lem279411 (@I (nat -> nat -> Prop) Peano.le n) m). Qed.
Lemma lem279414 (n : nat) (m : nat) : (Peano.le n m) = (term265 n m).
Proof. exact (TRANS (@lem279408 n m) (@lem279412 n m)). Qed.
Lemma lem279415 (n : nat) (m : nat) : (term273 n m) = (term274 n m).
Proof. exact (MK_COMB (@lem279397) (@lem279414 n m)). Qed.
Lemma lem279416 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem279423 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279424 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem279423 nat (nat -> Prop) f x). Qed.
Lemma lem279425 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem279424 Peano.lt m). Qed.
Lemma lem279426 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem279427 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem279425 m) (@lem279426 n)). Qed.
Lemma lem279429 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279430 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279429 nat Prop f x). Qed.
Lemma lem279431 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term266 m n).
Proof. exact (@lem279430 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem279433 (m : nat) (n : nat) : (Peano.lt m n) = (term266 m n).
Proof. exact (TRANS (@lem279427 m n) (@lem279431 m n)). Qed.
Lemma lem279434 (m : nat) (n : nat) : (term25 m n) = (term275 m n).
Proof. exact (MK_COMB (@lem279416) (@lem279433 m n)). Qed.
Lemma lem279435 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279436 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (MK_COMB (@lem279435) (@lem279434 m n)). Qed.
Lemma lem279437 (n : nat) (m : nat) : (term75 n m) = (term278 n m).
Proof. exact (MK_COMB (@lem279436 m n) (@lem279415 n m)). Qed.
Lemma lem279438 (m : nat) : (term72 m) = (term279 m).
Proof. exact (fun_ext (fun n : nat => @lem279437 n m)). Qed.
Lemma lem279439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279440 (m : nat) : (term84 m) = (term280 m).
Proof. exact (MK_COMB (@lem279439) (@lem279438 m)). Qed.
Lemma lem279441 : term95 = term281.
Proof. exact (fun_ext (fun m : nat => @lem279440 m)). Qed.
Lemma lem279442 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279443 : term106 = term282.
Proof. exact (MK_COMB (@lem279442) (@lem279441)). Qed.
Lemma lem279444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279445 : term108 = term283.
Proof. exact (MK_COMB (@lem279444) (@lem279443)). Qed.
Lemma lem279446 : term112 = term284.
Proof. exact (MK_COMB (@lem279445) (@lem279396)). Qed.
Lemma lem279447 (h1 : term29) : term284.
Proof. exact (EQ_MP (@lem279446) (@lem278948 h1)). Qed.
Lemma lem279448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem279453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279454 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279453 nat Prop f x). Qed.
Lemma lem279456 (P : nat -> Prop) (m : nat) : (P m) = (@I (nat -> Prop) P m).
Proof. exact (@lem279454 P m). Qed.
Lemma lem279457 (P : nat -> Prop) (m : nat) : (term119 P m) = (term285 P m).
Proof. exact (MK_COMB (@lem279448) (@lem279456 P m)). Qed.
Lemma lem279458 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem279465 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279466 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279465 (nat -> Prop) nat f x). Qed.
Lemma lem279468 (P : nat -> Prop) : (minimal P) = (@I ((nat -> Prop) -> nat) minimal P).
Proof. exact (@lem279466 minimal P). Qed.
Lemma lem279469 (m : nat) : (Peano.lt m) = (Peano.lt m).
Proof. exact (eq_refl (Peano.lt m)). Qed.
Lemma lem279470 (m : nat) (P : nat -> Prop) : (term127 m P) = (term286 m P).
Proof. exact (MK_COMB (@lem279469 m) (@lem279468 P)). Qed.
Lemma lem279472 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279473 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem279472 nat (nat -> Prop) f x). Qed.
Lemma lem279474 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem279473 Peano.lt m). Qed.
Lemma lem279475 (P : nat -> Prop) : (@I ((nat -> Prop) -> nat) minimal P) = (@I ((nat -> Prop) -> nat) minimal P).
Proof. exact (eq_refl (@I ((nat -> Prop) -> nat) minimal P)). Qed.
Lemma lem279476 (m : nat) (P : nat -> Prop) : (term286 m P) = (term287 m P).
Proof. exact (MK_COMB (@lem279474 m) (@lem279475 P)). Qed.
Lemma lem279478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279479 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279478 nat Prop f x). Qed.
Lemma lem279480 (m : nat) (P : nat -> Prop) : (term287 m P) = (term288 m P).
Proof. exact (@lem279479 (@I (nat -> nat -> Prop) Peano.lt m) (@I ((nat -> Prop) -> nat) minimal P)). Qed.
Lemma lem279481 (m : nat) (P : nat -> Prop) : (term286 m P) = (term288 m P).
Proof. exact (TRANS (@lem279476 m P) (@lem279480 m P)). Qed.
Lemma lem279482 (m : nat) (P : nat -> Prop) : (term127 m P) = (term288 m P).
Proof. exact (TRANS (@lem279470 m P) (@lem279481 m P)). Qed.
Lemma lem279483 (m : nat) (P : nat -> Prop) : (term289 m P) = (term290 m P).
Proof. exact (MK_COMB (@lem279458) (@lem279482 m P)). Qed.
Lemma lem279484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279485 (m : nat) (P : nat -> Prop) : (term291 m P) = (term292 m P).
Proof. exact (MK_COMB (@lem279484) (@lem279483 m P)). Qed.
Lemma lem279486 (P : nat -> Prop) (m : nat) : (term128 P m) = (term293 P m).
Proof. exact (MK_COMB (@lem279485 m P) (@lem279457 P m)). Qed.
Lemma lem279487 (P : nat -> Prop) : (term136 P) = (term294 P).
Proof. exact (fun_ext (fun m : nat => @lem279486 P m)). Qed.
Lemma lem279488 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279489 (P : nat -> Prop) : (term137 P) = (term295 P).
Proof. exact (MK_COMB (@lem279488) (@lem279487 P)). Qed.
Lemma lem279490 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem279495 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279496 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279495 (nat -> Prop) nat f x). Qed.
Lemma lem279498 (P : nat -> Prop) : (minimal P) = (@I ((nat -> Prop) -> nat) minimal P).
Proof. exact (@lem279496 minimal P). Qed.
Lemma lem279499 (P : nat -> Prop) : (term142 P) = (term296 P).
Proof. exact (MK_COMB (@lem279490 P) (@lem279498 P)). Qed.
Lemma lem279501 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279502 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279501 nat Prop f x). Qed.
Lemma lem279503 (P : nat -> Prop) : (term296 P) = (term297 P).
Proof. exact (@lem279502 P (@I ((nat -> Prop) -> nat) minimal P)). Qed.
Lemma lem279504 (P : nat -> Prop) : (term142 P) = (term297 P).
Proof. exact (TRANS (@lem279499 P) (@lem279503 P)). Qed.
Lemma lem279505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279506 (P : nat -> Prop) : (term19 P) = (term298 P).
Proof. exact (MK_COMB (@lem279505) (@lem279504 P)). Qed.
Lemma lem279507 (P : nat -> Prop) : (term143 P) = (term299 P).
Proof. exact (MK_COMB (@lem279506 P) (@lem279489 P)). Qed.
Lemma lem279508 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem279513 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279514 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279513 nat Prop f x). Qed.
Lemma lem279516 (P : nat -> Prop) (n : nat) : (P n) = (@I (nat -> Prop) P n).
Proof. exact (@lem279514 P n). Qed.
Lemma lem279517 (P : nat -> Prop) (n : nat) : (term119 P n) = (term285 P n).
Proof. exact (MK_COMB (@lem279508) (@lem279516 P n)). Qed.
Lemma lem279518 (P : nat -> Prop) : (term121 P) = (term300 P).
Proof. exact (fun_ext (fun n : nat => @lem279517 P n)). Qed.
Lemma lem279519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279520 (P : nat -> Prop) : (term114 P) = (term301 P).
Proof. exact (MK_COMB (@lem279519) (@lem279518 P)). Qed.
Lemma lem279521 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279522 (P : nat -> Prop) : (term145 P) = (term302 P).
Proof. exact (MK_COMB (@lem279521) (@lem279520 P)). Qed.
Lemma lem279523 (P : nat -> Prop) : (term147 P) = (term303 P).
Proof. exact (MK_COMB (@lem279522 P) (@lem279507 P)). Qed.
Lemma lem279524 : term162 = term304.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279523 P)). Qed.
Lemma lem279525 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279526 : term177 = term305.
Proof. exact (MK_COMB (@lem279525) (@lem279524)). Qed.
Lemma lem279527 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem279532 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279533 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279532 (nat -> Prop) nat f x). Qed.
Lemma lem279535 (n : type994) (P : nat -> Prop) : (n P) = (@I ((nat -> Prop) -> nat) n P).
Proof. exact (@lem279533 n P). Qed.
Lemma lem279536 (n : type994) (P : nat -> Prop) : (term306 n P) = (term307 n P).
Proof. exact (MK_COMB (@lem279527 P) (@lem279535 n P)). Qed.
Lemma lem279538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279539 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279538 nat Prop f x). Qed.
Lemma lem279540 (n : type994) (P : nat -> Prop) : (term307 n P) = (term308 n P).
Proof. exact (@lem279539 P (@I ((nat -> Prop) -> nat) n P)). Qed.
Lemma lem279541 (n : type994) (P : nat -> Prop) : (term306 n P) = (term308 n P).
Proof. exact (TRANS (@lem279536 n P) (@lem279540 n P)). Qed.
Lemma lem279542 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem279547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279548 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279547 (nat -> Prop) nat f x). Qed.
Lemma lem279550 (n : type994) (P : nat -> Prop) : (n P) = (@I ((nat -> Prop) -> nat) n P).
Proof. exact (@lem279548 n P). Qed.
Lemma lem279555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279556 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279555 (nat -> Prop) nat f x). Qed.
Lemma lem279558 (P : nat -> Prop) : (minimal P) = (@I ((nat -> Prop) -> nat) minimal P).
Proof. exact (@lem279556 minimal P). Qed.
Lemma lem279559 (n : type994) (P : nat -> Prop) : (term309 n P) = (term310 n P).
Proof. exact (MK_COMB (@lem279542) (@lem279550 n P)). Qed.
Lemma lem279560 (n : type994) (P : nat -> Prop) : (term311 n P) = (term312 n P).
Proof. exact (MK_COMB (@lem279559 n P) (@lem279558 P)). Qed.
Lemma lem279562 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279563 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem279562 nat (nat -> Prop) f x). Qed.
Lemma lem279564 (n : type994) (P : nat -> Prop) : (term310 n P) = (term313 n P).
Proof. exact (@lem279563 Peano.lt (@I ((nat -> Prop) -> nat) n P)). Qed.
Lemma lem279565 (P : nat -> Prop) : (@I ((nat -> Prop) -> nat) minimal P) = (@I ((nat -> Prop) -> nat) minimal P).
Proof. exact (eq_refl (@I ((nat -> Prop) -> nat) minimal P)). Qed.
Lemma lem279566 (n : type994) (P : nat -> Prop) : (term312 n P) = (term314 n P).
Proof. exact (MK_COMB (@lem279564 n P) (@lem279565 P)). Qed.
Lemma lem279568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279569 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279568 nat Prop f x). Qed.
Lemma lem279570 (n : type994) (P : nat -> Prop) : (term314 n P) = (term315 n P).
Proof. exact (@lem279569 (term313 n P) (@I ((nat -> Prop) -> nat) minimal P)). Qed.
Lemma lem279571 (n : type994) (P : nat -> Prop) : (term312 n P) = (term315 n P).
Proof. exact (TRANS (@lem279566 n P) (@lem279570 n P)). Qed.
Lemma lem279572 (n : type994) (P : nat -> Prop) : (term311 n P) = (term315 n P).
Proof. exact (TRANS (@lem279560 n P) (@lem279571 n P)). Qed.
Lemma lem279573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279574 (n : type994) (P : nat -> Prop) : (term316 n P) = (term317 n P).
Proof. exact (MK_COMB (@lem279573) (@lem279572 n P)). Qed.
Lemma lem279575 (n : type994) (P : nat -> Prop) : (term318 n P) = (term319 n P).
Proof. exact (MK_COMB (@lem279574 n P) (@lem279541 n P)). Qed.
Lemma lem279576 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem279577 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem279582 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279583 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279582 (nat -> Prop) nat f x). Qed.
Lemma lem279585 (P : nat -> Prop) : (minimal P) = (@I ((nat -> Prop) -> nat) minimal P).
Proof. exact (@lem279583 minimal P). Qed.
Lemma lem279586 (P : nat -> Prop) : (term142 P) = (term296 P).
Proof. exact (MK_COMB (@lem279577 P) (@lem279585 P)). Qed.
Lemma lem279588 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279589 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279588 nat Prop f x). Qed.
Lemma lem279590 (P : nat -> Prop) : (term296 P) = (term297 P).
Proof. exact (@lem279589 P (@I ((nat -> Prop) -> nat) minimal P)). Qed.
Lemma lem279591 (P : nat -> Prop) : (term142 P) = (term297 P).
Proof. exact (TRANS (@lem279586 P) (@lem279590 P)). Qed.
Lemma lem279592 (P : nat -> Prop) : (term185 P) = (term320 P).
Proof. exact (MK_COMB (@lem279576) (@lem279591 P)). Qed.
Lemma lem279593 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279594 (P : nat -> Prop) : (term138 P) = (term321 P).
Proof. exact (MK_COMB (@lem279593) (@lem279592 P)). Qed.
Lemma lem279595 (n : type994) (P : nat -> Prop) : (term322 n P) = (term323 n P).
Proof. exact (MK_COMB (@lem279594 P) (@lem279575 n P)). Qed.
Lemma lem279596 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem279601 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279602 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279601 (nat -> Prop) nat f x). Qed.
Lemma lem279604 (n : type994) (P : nat -> Prop) : (n P) = (@I ((nat -> Prop) -> nat) n P).
Proof. exact (@lem279602 n P). Qed.
Lemma lem279605 (n : type994) (P : nat -> Prop) : (term306 n P) = (term307 n P).
Proof. exact (MK_COMB (@lem279596 P) (@lem279604 n P)). Qed.
Lemma lem279607 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279608 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279607 nat Prop f x). Qed.
Lemma lem279609 (n : type994) (P : nat -> Prop) : (term307 n P) = (term308 n P).
Proof. exact (@lem279608 P (@I ((nat -> Prop) -> nat) n P)). Qed.
Lemma lem279610 (n : type994) (P : nat -> Prop) : (term306 n P) = (term308 n P).
Proof. exact (TRANS (@lem279605 n P) (@lem279609 n P)). Qed.
Lemma lem279611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279612 (n : type994) (P : nat -> Prop) : (term324 n P) = (term325 n P).
Proof. exact (MK_COMB (@lem279611) (@lem279610 n P)). Qed.
Lemma lem279613 (n : type994) (P : nat -> Prop) : (term236 n P) = (term326 n P).
Proof. exact (MK_COMB (@lem279612 n P) (@lem279595 n P)). Qed.
Lemma lem279614 (n : type994) : (term238 n) = (term327 n).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279613 n P)). Qed.
Lemma lem279615 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279616 (n : type994) : (term240 n) = (term328 n).
Proof. exact (MK_COMB (@lem279615) (@lem279614 n)). Qed.
Lemma lem279617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279618 (n : type994) : (term259 n) = (term329 n).
Proof. exact (MK_COMB (@lem279617) (@lem279616 n)). Qed.
Lemma lem279619 (n : type994) : (term261 n) = (term330 n).
Proof. exact (MK_COMB (@lem279618 n) (@lem279526)). Qed.
Lemma lem279620 (n : type994) (h1 : term261 n) : term330 n.
Proof. exact (EQ_MP (@lem279619 n) (@lem279351 n h1)). Qed.
Lemma lem279621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem279622 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem279627 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279628 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem279627 (nat -> Prop) nat f x). Qed.
Lemma lem279630 (P : nat -> Prop) : (minimal P) = (@I ((nat -> Prop) -> nat) minimal P).
Proof. exact (@lem279628 minimal P). Qed.
Lemma lem279631 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem279632 (P : nat -> Prop) : (term331 P) = (term332 P).
Proof. exact (MK_COMB (@lem279622) (@lem279630 P)). Qed.
Lemma lem279633 (P : nat -> Prop) (n' : nat) : (term36 P n') = (term333 P n').
Proof. exact (MK_COMB (@lem279632 P) (@lem279631 n')). Qed.
Lemma lem279635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279636 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem279635 nat (nat -> Prop) f x). Qed.
Lemma lem279637 (P : nat -> Prop) : (term332 P) = (term334 P).
Proof. exact (@lem279636 Peano.le (@I ((nat -> Prop) -> nat) minimal P)). Qed.
Lemma lem279638 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem279639 (P : nat -> Prop) (n' : nat) : (term333 P n') = (term335 P n').
Proof. exact (MK_COMB (@lem279637 P) (@lem279638 n')). Qed.
Lemma lem279641 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279642 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279641 nat Prop f x). Qed.
Lemma lem279643 (P : nat -> Prop) (n' : nat) : (term335 P n') = (term336 P n').
Proof. exact (@lem279642 (term334 P) n'). Qed.
Lemma lem279644 (P : nat -> Prop) (n' : nat) : (term333 P n') = (term336 P n').
Proof. exact (TRANS (@lem279639 P n') (@lem279643 P n')). Qed.
Lemma lem279645 (P : nat -> Prop) (n' : nat) : (term36 P n') = (term336 P n').
Proof. exact (TRANS (@lem279633 P n') (@lem279644 P n')). Qed.
Lemma lem279646 (P : nat -> Prop) (n' : nat) : (term337 P n') = (term338 P n').
Proof. exact (MK_COMB (@lem279621) (@lem279645 P n')). Qed.
Lemma lem279651 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem279652 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem279651 nat Prop f x). Qed.
Lemma lem279654 (P : nat -> Prop) (n' : nat) : (P n') = (@I (nat -> Prop) P n').
Proof. exact (@lem279652 P n'). Qed.
Lemma lem279655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem279656 (P : nat -> Prop) (n' : nat) : (term339 P n') = (term340 P n').
Proof. exact (MK_COMB (@lem279655) (@lem279654 P n')). Qed.
Lemma lem279657 (P : nat -> Prop) (n' : nat) : (term35 P n') = (term341 P n').
Proof. exact (MK_COMB (@lem279656 P n') (@lem279646 P n')). Qed.
Lemma lem279658 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : term341 P n'.
Proof. exact (EQ_MP (@lem279657 P n') (@lem279353 P n' h1)). Qed.
Lemma lem279661 (n : type994) (h1 : term261 n) : term305.
Proof. exact (proj2 (@lem279620 n h1)). Qed.
Lemma lem279663 (h1 : term29) : term272.
Proof. exact (proj2 (@lem279447 h1)). Qed.
Lemma lem279709 {A : Type'} (P : Prop) (Q : A -> Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem279710 (P : Prop) (Q : nat -> Prop) : (term344 P Q) = (term345 P Q).
Proof. exact (@lem279709 nat P Q). Qed.
Lemma lem279711 (P : nat -> Prop) : (term346 P) = (term347 P).
Proof. exact (@lem279710 (term297 P) (term294 P)). Qed.
Lemma lem279712 (P : nat -> Prop) (m : nat) : (term348 P m) = (term293 P m).
Proof. exact (eq_refl (term348 P m)). Qed.
Lemma lem279713 (P : nat -> Prop) : (term349 P) = (term294 P).
Proof. exact (fun_ext (fun m : nat => @lem279712 P m)). Qed.
Lemma lem279714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279715 (P : nat -> Prop) : (term350 P) = (term295 P).
Proof. exact (MK_COMB (@lem279714) (@lem279713 P)). Qed.
Lemma lem279716 (P : nat -> Prop) : (term298 P) = (term298 P).
Proof. exact (eq_refl (term298 P)). Qed.
Lemma lem279717 (P : nat -> Prop) : (term346 P) = (term299 P).
Proof. exact (MK_COMB (@lem279716 P) (@lem279715 P)). Qed.
Lemma lem279718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279719 (P : nat -> Prop) : (term351 P) = (term352 P).
Proof. exact (MK_COMB (@lem279718) (@lem279717 P)). Qed.
Lemma lem279720 (P : nat -> Prop) (m : nat) : (term348 P m) = (term293 P m).
Proof. exact (eq_refl (term348 P m)). Qed.
Lemma lem279721 (P : nat -> Prop) : (term298 P) = (term298 P).
Proof. exact (eq_refl (term298 P)). Qed.
Lemma lem279722 (P : nat -> Prop) (m : nat) : (term353 P m) = (term354 P m).
Proof. exact (MK_COMB (@lem279721 P) (@lem279720 P m)). Qed.
Lemma lem279723 (P : nat -> Prop) : (term355 P) = (term356 P).
Proof. exact (fun_ext (fun m : nat => @lem279722 P m)). Qed.
Lemma lem279724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279725 (P : nat -> Prop) : (term347 P) = (term357 P).
Proof. exact (MK_COMB (@lem279724) (@lem279723 P)). Qed.
Lemma lem279726 (P : nat -> Prop) : ((term346 P) = (term347 P)) = ((term299 P) = (term357 P)).
Proof. exact (MK_COMB (@lem279719 P) (@lem279725 P)). Qed.
Lemma lem279727 (P : nat -> Prop) : (term299 P) = (term357 P).
Proof. exact (EQ_MP (@lem279726 P) (@lem279711 P)). Qed.
Lemma lem279728 (P : nat -> Prop) : (term302 P) = (term302 P).
Proof. exact (eq_refl (term302 P)). Qed.
Lemma lem279729 (P : nat -> Prop) : (term303 P) = (term358 P).
Proof. exact (MK_COMB (@lem279728 P) (@lem279727 P)). Qed.
Lemma lem279731 {A : Type'} (P : A -> Prop) (Q : Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem279732 (P : nat -> Prop) (Q : Prop) : (term361 P Q) = (term362 P Q).
Proof. exact (@lem279731 nat P Q). Qed.
Lemma lem279733 (P : nat -> Prop) : (term363 P) = (term364 P).
Proof. exact (@lem279732 (term300 P) (term357 P)). Qed.
Lemma lem279734 (P : nat -> Prop) (n : nat) : (term365 P n) = (term285 P n).
Proof. exact (eq_refl (term365 P n)). Qed.
Lemma lem279735 (P : nat -> Prop) : (term366 P) = (term300 P).
Proof. exact (fun_ext (fun n : nat => @lem279734 P n)). Qed.
Lemma lem279736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279737 (P : nat -> Prop) : (term367 P) = (term301 P).
Proof. exact (MK_COMB (@lem279736) (@lem279735 P)). Qed.
Lemma lem279738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279739 (P : nat -> Prop) : (term368 P) = (term302 P).
Proof. exact (MK_COMB (@lem279738) (@lem279737 P)). Qed.
Lemma lem279740 (P : nat -> Prop) : (term357 P) = (term357 P).
Proof. exact (eq_refl (term357 P)). Qed.
Lemma lem279741 (P : nat -> Prop) : (term363 P) = (term358 P).
Proof. exact (MK_COMB (@lem279739 P) (@lem279740 P)). Qed.
Lemma lem279742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279743 (P : nat -> Prop) : (term369 P) = (term370 P).
Proof. exact (MK_COMB (@lem279742) (@lem279741 P)). Qed.
Lemma lem279744 (P : nat -> Prop) (n : nat) : (term365 P n) = (term285 P n).
Proof. exact (eq_refl (term365 P n)). Qed.
Lemma lem279745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem279746 (P : nat -> Prop) (n : nat) : (term371 P n) = (term372 P n).
Proof. exact (MK_COMB (@lem279745) (@lem279744 P n)). Qed.
Lemma lem279747 (P : nat -> Prop) : (term357 P) = (term357 P).
Proof. exact (eq_refl (term357 P)). Qed.
Lemma lem279748 (n : nat) (P : nat -> Prop) : (term373 n P) = (term374 n P).
Proof. exact (MK_COMB (@lem279746 P n) (@lem279747 P)). Qed.
Lemma lem279749 (P : nat -> Prop) : (term375 P) = (term376 P).
Proof. exact (fun_ext (fun n : nat => @lem279748 n P)). Qed.
Lemma lem279750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279751 (P : nat -> Prop) : (term364 P) = (term377 P).
Proof. exact (MK_COMB (@lem279750) (@lem279749 P)). Qed.
Lemma lem279752 (P : nat -> Prop) : ((term363 P) = (term364 P)) = ((term358 P) = (term377 P)).
Proof. exact (MK_COMB (@lem279743 P) (@lem279751 P)). Qed.
Lemma lem279753 (P : nat -> Prop) : (term358 P) = (term377 P).
Proof. exact (EQ_MP (@lem279752 P) (@lem279733 P)). Qed.
Lemma lem279755 {A : Type'} (P : Prop) (Q : A -> Prop) : (term378 A P Q) = (term379 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem279756 (P : Prop) (Q : nat -> Prop) : (term380 P Q) = (term381 P Q).
Proof. exact (@lem279755 nat P Q). Qed.
Lemma lem279757 (n : nat) (P : nat -> Prop) : (term382 n P) = (term383 n P).
Proof. exact (@lem279756 (term285 P n) (term356 P)). Qed.
Lemma lem279758 (P : nat -> Prop) (m : nat) : (term384 P m) = (term354 P m).
Proof. exact (eq_refl (term384 P m)). Qed.
Lemma lem279759 (P : nat -> Prop) : (term385 P) = (term356 P).
Proof. exact (fun_ext (fun m : nat => @lem279758 P m)). Qed.
Lemma lem279760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279761 (P : nat -> Prop) : (term386 P) = (term357 P).
Proof. exact (MK_COMB (@lem279760) (@lem279759 P)). Qed.
Lemma lem279762 (P : nat -> Prop) (n : nat) : (term372 P n) = (term372 P n).
Proof. exact (eq_refl (term372 P n)). Qed.
Lemma lem279763 (n : nat) (P : nat -> Prop) : (term382 n P) = (term374 n P).
Proof. exact (MK_COMB (@lem279762 P n) (@lem279761 P)). Qed.
Lemma lem279764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279765 (n : nat) (P : nat -> Prop) : (term387 n P) = (term388 n P).
Proof. exact (MK_COMB (@lem279764) (@lem279763 n P)). Qed.
Lemma lem279766 (P : nat -> Prop) (m : nat) : (term384 P m) = (term354 P m).
Proof. exact (eq_refl (term384 P m)). Qed.
Lemma lem279767 (P : nat -> Prop) (n : nat) : (term372 P n) = (term372 P n).
Proof. exact (eq_refl (term372 P n)). Qed.
Lemma lem279768 (n : nat) (P : nat -> Prop) (m : nat) : (term389 n P m) = (term390 n P m).
Proof. exact (MK_COMB (@lem279767 P n) (@lem279766 P m)). Qed.
Lemma lem279769 (n : nat) (P : nat -> Prop) : (term391 n P) = (term392 n P).
Proof. exact (fun_ext (fun m : nat => @lem279768 n P m)). Qed.
Lemma lem279770 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279771 (n : nat) (P : nat -> Prop) : (term383 n P) = (term393 n P).
Proof. exact (MK_COMB (@lem279770) (@lem279769 n P)). Qed.
Lemma lem279772 (n : nat) (P : nat -> Prop) : ((term382 n P) = (term383 n P)) = ((term374 n P) = (term393 n P)).
Proof. exact (MK_COMB (@lem279765 n P) (@lem279771 n P)). Qed.
Lemma lem279773 (n : nat) (P : nat -> Prop) : (term374 n P) = (term393 n P).
Proof. exact (EQ_MP (@lem279772 n P) (@lem279757 n P)). Qed.
Lemma lem279774 (P : nat -> Prop) : (term376 P) = (term394 P).
Proof. exact (fun_ext (fun n : nat => @lem279773 n P)). Qed.
Lemma lem279775 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279776 (P : nat -> Prop) : (term377 P) = (term395 P).
Proof. exact (MK_COMB (@lem279775) (@lem279774 P)). Qed.
Lemma lem279777 (P : nat -> Prop) : (term358 P) = (term395 P).
Proof. exact (TRANS (@lem279753 P) (@lem279776 P)). Qed.
Lemma lem279778 (P : nat -> Prop) : (term303 P) = (term395 P).
Proof. exact (TRANS (@lem279729 P) (@lem279777 P)). Qed.
Lemma lem279779 : term304 = term396.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279778 P)). Qed.
Lemma lem279780 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279781 : term305 = term397.
Proof. exact (MK_COMB (@lem279780) (@lem279779)). Qed.
Lemma lem279804 (n : nat) (P : nat -> Prop) (m : nat) : (term390 n P m) = (term398 n P m).
Proof. exact (@lem19490 (term297 P) (term285 P n) (term293 P m)). Qed.
Lemma lem279805 (n : nat) (P : nat -> Prop) : (term392 n P) = (term399 n P).
Proof. exact (fun_ext (fun m : nat => @lem279804 n P m)). Qed.
Lemma lem279806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279807 (n : nat) (P : nat -> Prop) : (term393 n P) = (term400 n P).
Proof. exact (MK_COMB (@lem279806) (@lem279805 n P)). Qed.
Lemma lem279808 (P : nat -> Prop) : (term394 P) = (term401 P).
Proof. exact (fun_ext (fun n : nat => @lem279807 n P)). Qed.
Lemma lem279809 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279810 (P : nat -> Prop) : (term395 P) = (term402 P).
Proof. exact (MK_COMB (@lem279809) (@lem279808 P)). Qed.
Lemma lem279811 : term396 = term403.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem279810 P)). Qed.
Lemma lem279812 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem279813 : term397 = term404.
Proof. exact (MK_COMB (@lem279812) (@lem279811)). Qed.
Lemma lem279814 : term305 = term404.
Proof. exact (TRANS (@lem279781) (@lem279813)). Qed.
Lemma lem279815 (n : type994) (h1 : term261 n) : term404.
Proof. exact (EQ_MP (@lem279814) (@lem279661 n h1)). Qed.
Lemma lem279839 (n : nat) (m : nat) : (term268 n m) = (term268 n m).
Proof. exact (eq_refl (term268 n m)). Qed.
Lemma lem279840 (m : nat) : (term269 m) = (term269 m).
Proof. exact (fun_ext (fun n : nat => @lem279839 n m)). Qed.
Lemma lem279841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279842 (m : nat) : (term270 m) = (term270 m).
Proof. exact (MK_COMB (@lem279841) (@lem279840 m)). Qed.
Lemma lem279843 : term271 = term271.
Proof. exact (fun_ext (fun m : nat => @lem279842 m)). Qed.
Lemma lem279844 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem279846 : term272 = term272.
Proof. exact (MK_COMB (@lem279844) (@lem279843)). Qed.
Lemma lem279847 (h1 : term29) : term272.
Proof. exact (EQ_MP (@lem279846) (@lem279663 h1)). Qed.
Lemma lem279851 (_6450 : nat -> Prop) (n : type994) (h1 : term261 n) : term405 _6450.
Proof. exact (@lem279815 n h1 _6450). Qed.
Lemma lem279852 (_6450 : nat -> Prop) : (term405 _6450) = (term402 _6450).
Proof. exact (eq_refl (term405 _6450)). Qed.
Lemma lem279853 (_6450 : nat -> Prop) (n : type994) (h1 : term261 n) : term402 _6450.
Proof. exact (EQ_MP (@lem279852 _6450) (@lem279851 _6450 n h1)). Qed.
Lemma lem279854 (_6450 : nat -> Prop) (_6451 : nat) (n : type994) (h1 : term261 n) : term406 _6450 _6451.
Proof. exact (@lem279853 _6450 n h1 _6451). Qed.
Lemma lem279855 (_6451 : nat) (_6450 : nat -> Prop) : (term406 _6450 _6451) = (term400 _6451 _6450).
Proof. exact (eq_refl (term406 _6450 _6451)). Qed.
Lemma lem279856 (_6451 : nat) (_6450 : nat -> Prop) (n : type994) (h1 : term261 n) : term400 _6451 _6450.
Proof. exact (EQ_MP (@lem279855 _6451 _6450) (@lem279854 _6450 _6451 n h1)). Qed.
Lemma lem279857 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) (n : type994) (h1 : term261 n) : term407 _6451 _6450 _6452.
Proof. exact (@lem279856 _6451 _6450 n h1 _6452). Qed.
Lemma lem279858 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : (term407 _6451 _6450 _6452) = (term398 _6451 _6450 _6452).
Proof. exact (eq_refl (term407 _6451 _6450 _6452)). Qed.
Lemma lem279859 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) (n : type994) (h1 : term261 n) : term398 _6451 _6450 _6452.
Proof. exact (EQ_MP (@lem279858 _6451 _6450 _6452) (@lem279857 _6451 _6450 _6452 n h1)). Qed.
Lemma lem279866 (_6455 : nat) (h1 : term29) : term408 _6455.
Proof. exact (@lem279847 h1 _6455). Qed.
Lemma lem279867 (_6455 : nat) : (term408 _6455) = (term270 _6455).
Proof. exact (eq_refl (term408 _6455)). Qed.
Lemma lem279868 (_6455 : nat) (h1 : term29) : term270 _6455.
Proof. exact (EQ_MP (@lem279867 _6455) (@lem279866 _6455 h1)). Qed.
Lemma lem279869 (_6455 : nat) (_6456 : nat) (h1 : term29) : term409 _6455 _6456.
Proof. exact (@lem279868 _6455 h1 _6456). Qed.
Lemma lem279870 (_6456 : nat) (_6455 : nat) : (term409 _6455 _6456) = (term268 _6456 _6455).
Proof. exact (eq_refl (term409 _6455 _6456)). Qed.
Lemma lem279879 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : term338 P n'.
Proof. exact (proj2 (@lem279658 P n' h1)). Qed.
Lemma lem279891 (_6456 : nat) (_6455 : nat) (h1 : term29) : term268 _6456 _6455.
Proof. exact (EQ_MP (@lem279870 _6456 _6455) (@lem279869 _6455 _6456 h1)). Qed.
Lemma lem279907 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) (n : type994) (h1 : term261 n) : term410 _6451 _6450 _6452.
Proof. exact (proj2 (@lem279859 _6451 _6450 _6452 n h1)). Qed.
Lemma lem279929 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : @I (nat -> Prop) P n'.
Proof. exact (proj1 (@lem279658 P n' h1)). Qed.
Lemma lem279930 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : term411 P n'.
Proof. exact (fun h0 : term285 P n' => @lem279929 P n' h1). Qed.
Lemma lem279932 (p : Prop) : (term412 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem279933 (P : nat -> Prop) (n' : nat) : (term411 P n') = (@I (nat -> Prop) P n').
Proof. exact (@lem279932 (@I (nat -> Prop) P n')). Qed.
Lemma lem279934 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : @I (nat -> Prop) P n'.
Proof. exact (EQ_MP (@lem279933 P n') (@lem279930 P n' h1)). Qed.
Lemma lem279936 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : @I (nat -> Prop) P n'.
Proof. exact (proj1 (@lem279658 P n' h1)). Qed.
Lemma lem279937 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : term411 P n'.
Proof. exact (fun h0 : term285 P n' => @lem279936 P n' h1). Qed.
Lemma lem279939 (p : Prop) : (term412 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem279940 (P : nat -> Prop) (n' : nat) : (term411 P n') = (@I (nat -> Prop) P n').
Proof. exact (@lem279939 (@I (nat -> Prop) P n')). Qed.
Lemma lem279941 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : @I (nat -> Prop) P n'.
Proof. exact (EQ_MP (@lem279940 P n') (@lem279937 P n' h1)). Qed.
Lemma lem279957 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem279958 (_6452 : nat) (_6450 : nat -> Prop) : (term293 _6450 _6452) = (term413 _6452 _6450).
Proof. exact (@lem279957 (term285 _6450 _6452) (term290 _6452 _6450)). Qed.
Lemma lem279964 (_6450 : nat -> Prop) (_6451 : nat) : (term372 _6450 _6451) = (term372 _6450 _6451).
Proof. exact (eq_refl (term372 _6450 _6451)). Qed.
Lemma lem279965 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : (term410 _6451 _6450 _6452) = (term414 _6451 _6452 _6450).
Proof. exact (MK_COMB (@lem279964 _6450 _6451) (@lem279958 _6452 _6450)). Qed.
Lemma lem279976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem279977 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : (term415 _6451 _6450 _6452) = (term416 _6451 _6452 _6450).
Proof. exact (MK_COMB (@lem279976) (@lem279965 _6451 _6452 _6450)). Qed.
Lemma lem279981 (q : Prop) (p : Prop) (r : Prop) : (term417 p q r) = (term417 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem279982 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : (term418 _6451 _6450 _6452) = (term410 _6451 _6450 _6452).
Proof. exact (@lem279981 (term285 _6450 _6451) (term290 _6452 _6450) (term285 _6450 _6452)). Qed.
Lemma lem279996 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem279997 (_6452 : nat) (_6450 : nat -> Prop) : (term293 _6450 _6452) = (term413 _6452 _6450).
Proof. exact (@lem279996 (term285 _6450 _6452) (term290 _6452 _6450)). Qed.
Lemma lem280003 (_6450 : nat -> Prop) (_6451 : nat) : (term372 _6450 _6451) = (term372 _6450 _6451).
Proof. exact (eq_refl (term372 _6450 _6451)). Qed.
Lemma lem280004 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : (term410 _6451 _6450 _6452) = (term414 _6451 _6452 _6450).
Proof. exact (MK_COMB (@lem280003 _6450 _6451) (@lem279997 _6452 _6450)). Qed.
Lemma lem280015 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : (term418 _6451 _6450 _6452) = (term414 _6451 _6452 _6450).
Proof. exact (TRANS (@lem279982 _6451 _6450 _6452) (@lem280004 _6451 _6452 _6450)). Qed.
Lemma lem280016 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : ((term410 _6451 _6450 _6452) = (term418 _6451 _6450 _6452)) = ((term414 _6451 _6452 _6450) = (term414 _6451 _6452 _6450)).
Proof. exact (MK_COMB (@lem279977 _6451 _6452 _6450) (@lem280015 _6451 _6452 _6450)). Qed.
Lemma lem280018 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem280019 (x : Prop) : (x = x) = True.
Proof. exact (@lem280018 Prop x). Qed.
Lemma lem280020 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : ((term414 _6451 _6452 _6450) = (term414 _6451 _6452 _6450)) = True.
Proof. exact (@lem280019 (term414 _6451 _6452 _6450)). Qed.
Lemma lem280021 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : ((term410 _6451 _6450 _6452) = (term418 _6451 _6450 _6452)) = True.
Proof. exact (TRANS (@lem280016 _6451 _6452 _6450) (@lem280020 _6451 _6452 _6450)). Qed.
Lemma lem280022 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : True = ((term410 _6451 _6450 _6452) = (term418 _6451 _6450 _6452)).
Proof. exact (SYM (@lem280021 _6451 _6450 _6452)). Qed.
Lemma lem280023 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : (term410 _6451 _6450 _6452) = (term418 _6451 _6450 _6452).
Proof. exact (EQ_MP (@lem280022 _6451 _6450 _6452) (@lem0)). Qed.
Lemma lem280024 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) (n : type994) (h1 : term261 n) : term418 _6451 _6450 _6452.
Proof. exact (EQ_MP (@lem280023 _6451 _6450 _6452) (@lem279907 _6451 _6450 _6452 n h1)). Qed.
Lemma lem280026 (b : Prop) (a : Prop) : (a \/ b) = (term419 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem280027 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : (term418 _6451 _6450 _6452) = (term420 _6451 _6452 _6450).
Proof. exact (@lem280026 (term421 _6451 _6450 _6452) (term290 _6452 _6450)). Qed.
Lemma lem280029 (a : Prop) (b : Prop) : (term422 a b) = (term423 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem280030 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : (term424 _6451 _6450 _6452) = (term425 _6451 _6450 _6452).
Proof. exact (@lem280029 (term285 _6450 _6451) (term285 _6450 _6452)). Qed.
Lemma lem280032 (a : Prop) : (term426 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem280033 (_6450 : nat -> Prop) (_6451 : nat) : (term427 _6450 _6451) = (@I (nat -> Prop) _6450 _6451).
Proof. exact (@lem280032 (@I (nat -> Prop) _6450 _6451)). Qed.
Lemma lem280034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem280035 (_6450 : nat -> Prop) (_6451 : nat) : (term428 _6450 _6451) = (term340 _6450 _6451).
Proof. exact (MK_COMB (@lem280034) (@lem280033 _6450 _6451)). Qed.
Lemma lem280037 (a : Prop) : (term426 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem280038 (_6450 : nat -> Prop) (_6452 : nat) : (term427 _6450 _6452) = (@I (nat -> Prop) _6450 _6452).
Proof. exact (@lem280037 (@I (nat -> Prop) _6450 _6452)). Qed.
Lemma lem280039 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : (term425 _6451 _6450 _6452) = (term429 _6451 _6450 _6452).
Proof. exact (MK_COMB (@lem280035 _6450 _6451) (@lem280038 _6450 _6452)). Qed.
Lemma lem280040 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : (term424 _6451 _6450 _6452) = (term429 _6451 _6450 _6452).
Proof. exact (TRANS (@lem280030 _6451 _6450 _6452) (@lem280039 _6451 _6450 _6452)). Qed.
Lemma lem280041 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem280042 (_6451 : nat) (_6450 : nat -> Prop) (_6452 : nat) : (term430 _6451 _6450 _6452) = (term431 _6451 _6450 _6452).
Proof. exact (MK_COMB (@lem280041) (@lem280040 _6451 _6450 _6452)). Qed.
Lemma lem280043 (_6452 : nat) (_6450 : nat -> Prop) : (term290 _6452 _6450) = (term290 _6452 _6450).
Proof. exact (eq_refl (term290 _6452 _6450)). Qed.
Lemma lem280044 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : (term420 _6451 _6452 _6450) = (term432 _6451 _6452 _6450).
Proof. exact (MK_COMB (@lem280042 _6451 _6450 _6452) (@lem280043 _6452 _6450)). Qed.
Lemma lem280045 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) : (term418 _6451 _6450 _6452) = (term432 _6451 _6452 _6450).
Proof. exact (TRANS (@lem280027 _6451 _6452 _6450) (@lem280044 _6451 _6452 _6450)). Qed.
Lemma lem280047 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : term433 P n'.
Proof. exact (conj (@lem279934 P n' h1) (@lem279941 P n' h1)). Qed.
Lemma lem280049 (_6451 : nat) (_6452 : nat) (_6450 : nat -> Prop) (n : type994) (h1 : term261 n) : term432 _6451 _6452 _6450.
Proof. exact (EQ_MP (@lem280045 _6451 _6452 _6450) (@lem280024 _6451 _6450 _6452 n h1)). Qed.
Lemma lem280050 (n' : nat) (P : nat -> Prop) (n : type994) (h1 : term261 n) : term434 n' P.
Proof. exact (@lem280049 n' n' P n h1). Qed.
Lemma lem280053 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term261 n) (h2 : term35 P n') : term290 n' P.
Proof. exact (@lem280050 n' P n h1 (@lem280047 P n' h2)). Qed.
Lemma lem280054 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term261 n) (h2 : term35 P n') : term435 n' P.
Proof. exact (fun h0 : term288 n' P => @lem280053 n P n' h1 h2). Qed.
Lemma lem280056 (p : Prop) : (term436 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem280057 (n' : nat) (P : nat -> Prop) : (term435 n' P) = (term290 n' P).
Proof. exact (@lem280056 (term288 n' P)). Qed.
Lemma lem280058 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term261 n) (h2 : term35 P n') : term290 n' P.
Proof. exact (EQ_MP (@lem280057 n' P) (@lem280054 n P n' h1 h2)). Qed.
Lemma lem280069 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem280070 (_6456 : nat) (_6455 : nat) : (term437 _6455 _6456) = (term268 _6456 _6455).
Proof. exact (@lem280069 (term266 _6455 _6456) (term265 _6456 _6455)). Qed.
Lemma lem280076 (_6456 : nat) (_6455 : nat) : (term438 _6456 _6455) = (term438 _6456 _6455).
Proof. exact (eq_refl (term438 _6456 _6455)). Qed.
Lemma lem280077 (_6456 : nat) (_6455 : nat) : ((term268 _6456 _6455) = (term437 _6455 _6456)) = ((term268 _6456 _6455) = (term268 _6456 _6455)).
Proof. exact (MK_COMB (@lem280076 _6456 _6455) (@lem280070 _6456 _6455)). Qed.
Lemma lem280079 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem280080 (x : Prop) : (x = x) = True.
Proof. exact (@lem280079 Prop x). Qed.
Lemma lem280081 (_6456 : nat) (_6455 : nat) : ((term268 _6456 _6455) = (term268 _6456 _6455)) = True.
Proof. exact (@lem280080 (term268 _6456 _6455)). Qed.
Lemma lem280082 (_6455 : nat) (_6456 : nat) : ((term268 _6456 _6455) = (term437 _6455 _6456)) = True.
Proof. exact (TRANS (@lem280077 _6456 _6455) (@lem280081 _6456 _6455)). Qed.
Lemma lem280083 (_6455 : nat) (_6456 : nat) : True = ((term268 _6456 _6455) = (term437 _6455 _6456)).
Proof. exact (SYM (@lem280082 _6455 _6456)). Qed.
Lemma lem280084 (_6455 : nat) (_6456 : nat) : (term268 _6456 _6455) = (term437 _6455 _6456).
Proof. exact (EQ_MP (@lem280083 _6455 _6456) (@lem0)). Qed.
Lemma lem280085 (_6455 : nat) (_6456 : nat) (h1 : term29) : term437 _6455 _6456.
Proof. exact (EQ_MP (@lem280084 _6455 _6456) (@lem279891 _6456 _6455 h1)). Qed.
Lemma lem280087 (b : Prop) (a : Prop) : (a \/ b) = (term419 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem280090 (_6456 : nat) (_6455 : nat) : (term437 _6455 _6456) = (term439 _6456 _6455).
Proof. exact (@lem280087 (term266 _6455 _6456) (term265 _6456 _6455)). Qed.
Lemma lem280093 (_6456 : nat) (_6455 : nat) (h1 : term29) : term439 _6456 _6455.
Proof. exact (EQ_MP (@lem280090 _6456 _6455) (@lem280085 _6455 _6456 h1)). Qed.
Lemma lem280094 (P : nat -> Prop) (n' : nat) (h1 : term29) : term440 P n'.
Proof. exact (@lem280093 (@I ((nat -> Prop) -> nat) minimal P) n' h1). Qed.
Lemma lem280097 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term29) (h2 : term261 n) (h3 : term35 P n') : term336 P n'.
Proof. exact (@lem280094 P n' h1 (@lem280058 n P n' h2 h3)). Qed.
Lemma lem280098 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term29) (h2 : term261 n) (h3 : term35 P n') : term441 P n'.
Proof. exact (fun h0 : term338 P n' => @lem280097 n P n' h1 h2 h3). Qed.
Lemma lem280100 (p : Prop) : (term412 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem280101 (P : nat -> Prop) (n' : nat) : (term441 P n') = (term336 P n').
Proof. exact (@lem280100 (term336 P n')). Qed.
Lemma lem280102 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term29) (h2 : term261 n) (h3 : term35 P n') : term336 P n'.
Proof. exact (EQ_MP (@lem280101 P n') (@lem280098 n P n' h1 h2 h3)). Qed.
Lemma lem280105 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem280107 (P : nat -> Prop) (n' : nat) : (term338 P n') = (term442 P n').
Proof. exact (@lem280105 (term336 P n')). Qed.
Lemma lem280110 (P : nat -> Prop) (n' : nat) (h1 : term35 P n') : term442 P n'.
Proof. exact (EQ_MP (@lem280107 P n') (@lem279879 P n' h1)). Qed.
Lemma lem280113 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term29) (h2 : term261 n) (h3 : term35 P n') : False.
Proof. exact (@lem280110 P n' h3 (@lem280102 n P n' h1 h2 h3)). Qed.
Lemma lem280114 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term29) (h2 : term261 n) (h3 : term35 P n') : term443.
Proof. exact (fun h0 : ~ False => @lem280113 n P n' h1 h2 h3). Qed.
Lemma lem280116 (p : Prop) : (term412 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem280117 : term443 = False.
Proof. exact (@lem280116 False). Qed.
Lemma lem280118 (n : type994) (P : nat -> Prop) (n' : nat) (h1 : term29) (h2 : term261 n) (h3 : term35 P n') : False.
Proof. exact (EQ_MP (@lem280117) (@lem280114 n P n' h1 h2 h3)). Qed.
Lemma lem280119 (P : nat -> Prop) (n : type994) (h1 : term29) (h2 : term45 P) (h3 : term261 n) : False.
Proof. exact (ex_elim (@lem279352 P h2) (fun n' : nat => fun h0 : term44 P n' => @lem280118 n P n' h1 h3 h0)). Qed.
Lemma lem280120 (n : type994) (h1 : term29) (h2 : term3) (h3 : term261 n) : False.
Proof. exact (ex_elim (@lem278659 h2) (fun P : nat -> Prop => fun h0 : term52 P => @lem280119 P n h1 h0 h3)). Qed.
Lemma lem280121 (h1 : term10) (h2 : term29) (h3 : term3) : False.
Proof. exact (ex_elim (@lem279350 h1) (fun n : type994 => fun h0 : term263 n => @lem280120 n h2 h3 h0)). Qed.
Lemma lem280122 (h1 : term29) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem280121 h0 h1 h2). Qed.
Lemma lem280123 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem280124 (h1 : term29) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem280123) (@lem280122 h1 h2)). Qed.
Lemma lem280125 (h1 : term3) : term13.
Proof. exact (fun h0 : term29 => @lem280124 h0 h1). Qed.
Lemma lem280126 : term15.
Proof. exact (fun h0 : term3 => @lem280125 h0). Qed.
Lemma lem280127 : term4.
Proof. exact (EQ_MP (@lem278592) (@lem280126)). Qed.
Lemma lem280129 : term4.
Proof. exact (@lem278425 (@lem280127)). Qed.
Lemma lem280130 (h1 : term3) : term12.
Proof. exact (@lem280129 (@lem278410 h1)). Qed.
Lemma lem280131 (h1 : term3) : term8.
Proof. exact (@lem280130 h1 (@lem98377)). Qed.
Lemma lem280132 (h1 : term3) : False.
Proof. exact (@lem280131 h1 (@lem273176)). Qed.
Lemma lem280133 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem280132 h1) (fun h2 : False => @lem278410 h1)). Qed.
Lemma lem280134 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem280133 h1) (@lem278410 h1)). Qed.
Lemma lem280135 : term2.
Proof. exact (fun h0 : term3 => @lem280134 h0). Qed.
Lemma lem280136 : term1.
Proof. exact (EQ_MP (@lem278409) (@lem280135)). Qed.
