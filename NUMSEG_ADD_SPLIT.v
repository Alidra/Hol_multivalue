Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_ADD_SPLIT_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import IN_UNION_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
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
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5451442 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5451443 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5451444 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5451443 m) (@lem5451442 m)). Qed.
Lemma lem5451445 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5451444 m n). Qed.
Lemma lem5451446 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5451447 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem5451446 m n) (@lem5451445 m n)). Qed.
Lemma lem5451448 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem5451447 m n p). Qed.
Lemma lem5451449 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem5451451 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem5451452 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem5451453 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem5451452 A s) (@lem5451451 A s)). Qed.
Lemma lem5451454 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem5451453 A s t). Qed.
Lemma lem5451455 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term10 A s t).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem5451456 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (EQ_MP (@lem5451455 A s t) (@lem5451454 A s t)). Qed.
Lemma lem5451457 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term11 A s t x.
Proof. exact (@lem5451456 A s t x). Qed.
Lemma lem5451458 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s t x) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl (term11 A s t x)). Qed.
Lemma lem5451460 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5451461 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem5451462 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem5451461 A s) (@lem5451460 A s)). Qed.
Lemma lem5451463 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem5451462 A s t). Qed.
Lemma lem5451464 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem5451483 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem5451464 A s t) (@lem5451463 A s t)). Qed.
Lemma lem5451484 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term18 s t).
Proof. exact (@lem5451483 nat s t). Qed.
Lemma lem5451485 (m : nat) (n : nat) (p : nat) : ((term19 m n p) = (term20 m n p)) = (term21 m n p).
Proof. exact (@lem5451484 (term19 m n p) (term20 m n p)). Qed.
Lemma lem5451495 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem5451449 m p n) (@lem5451448 m n p)). Qed.
Lemma lem5451496 (m : nat) (x : nat) (n : nat) (p : nat) : (term22 x m n p) = (term23 m x n p).
Proof. exact (@lem5451495 m x (Nat.add n p)). Qed.
Lemma lem5451499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5451500 (m : nat) (x : nat) (n : nat) (p : nat) : (term24 x m n p) = (term25 m x n p).
Proof. exact (MK_COMB (@lem5451499) (@lem5451496 m x n p)). Qed.
Lemma lem5451502 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem5451458 A s x t) (@lem5451457 A s t x)). Qed.
Lemma lem5451503 (s : nat -> Prop) (x : nat) (t : nat -> Prop) : (term26 x s t) = (term27 s x t).
Proof. exact (@lem5451502 nat s x t). Qed.
Lemma lem5451504 (m : nat) (x : nat) (n : nat) (p : nat) : (term28 x m n p) = (term29 m x n p).
Proof. exact (@lem5451503 (dotdot m n) x (term30 n p)). Qed.
Lemma lem5451508 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem5451449 m p n) (@lem5451448 m n p)). Qed.
Lemma lem5451509 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem5451508 m x n). Qed.
Lemma lem5451512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5451513 (m : nat) (x : nat) (n : nat) : (term31 x m n) = (term32 m x n).
Proof. exact (MK_COMB (@lem5451512) (@lem5451509 m x n)). Qed.
Lemma lem5451515 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem5451449 m p n) (@lem5451448 m n p)). Qed.
Lemma lem5451516 (x : nat) (n : nat) (p : nat) : (term33 x n p) = (term34 x n p).
Proof. exact (@lem5451515 (term35 n) x (Nat.add n p)). Qed.
Lemma lem5451519 (m : nat) (x : nat) (n : nat) (p : nat) : (term29 m x n p) = (term36 m x n p).
Proof. exact (MK_COMB (@lem5451513 m x n) (@lem5451516 x n p)). Qed.
Lemma lem5451522 (m : nat) (x : nat) (n : nat) (p : nat) : (term28 x m n p) = (term36 m x n p).
Proof. exact (TRANS (@lem5451504 m x n p) (@lem5451519 m x n p)). Qed.
Lemma lem5451523 (m : nat) (x : nat) (n : nat) (p : nat) : ((term22 x m n p) = (term28 x m n p)) = ((term23 m x n p) = (term36 m x n p)).
Proof. exact (MK_COMB (@lem5451500 m x n p) (@lem5451522 m x n p)). Qed.
Lemma lem5451528 (m : nat) (n : nat) (p : nat) : (term37 m n p) = (term38 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5451523 m x n p)). Qed.
Lemma lem5451529 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451530 (m : nat) (n : nat) (p : nat) : (term21 m n p) = (term39 m n p).
Proof. exact (MK_COMB (@lem5451529) (@lem5451528 m n p)). Qed.
Lemma lem5451535 (m : nat) (n : nat) (p : nat) : ((term19 m n p) = (term20 m n p)) = (term39 m n p).
Proof. exact (TRANS (@lem5451485 m n p) (@lem5451530 m n p)). Qed.
Lemma lem5451536 (m : nat) (n : nat) : (term40 m n) = (term40 m n).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem5451537 (m : nat) (n : nat) (p : nat) : (term41 m n p) = (term42 m n p).
Proof. exact (MK_COMB (@lem5451536 m n) (@lem5451535 m n p)). Qed.
Lemma lem5451540 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (fun_ext (fun p : nat => @lem5451537 m n p)). Qed.
Lemma lem5451541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451542 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem5451541) (@lem5451540 m n)). Qed.
Lemma lem5451547 (m : nat) : (term47 m) = (term48 m).
Proof. exact (fun_ext (fun n : nat => @lem5451542 m n)). Qed.
Lemma lem5451548 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451549 (m : nat) : (term49 m) = (term50 m).
Proof. exact (MK_COMB (@lem5451548) (@lem5451547 m)). Qed.
Lemma lem5451554 : term51 = term52.
Proof. exact (fun_ext (fun m : nat => @lem5451549 m)). Qed.
Lemma lem5451555 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451556 : term53 = term54.
Proof. exact (MK_COMB (@lem5451555) (@lem5451554)). Qed.
Lemma lem5451561 : term54 = term53.
Proof. exact (SYM (@lem5451556)). Qed.
Lemma lem5451611 (m : nat) (x : nat) (n : nat) (p : nat) : ((term23 m x n p) = (term36 m x n p)) = ((term23 m x n p) = (term36 m x n p)).
Proof. exact (eq_refl ((term23 m x n p) = (term36 m x n p))). Qed.
Lemma lem5451612 (m : nat) (n : nat) (p : nat) : (term38 m n p) = (term38 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5451611 m x n p)). Qed.
Lemma lem5451613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451614 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term39 m n p).
Proof. exact (MK_COMB (@lem5451613) (@lem5451612 m n p)). Qed.
Lemma lem5451617 (m : nat) (n : nat) : (term40 m n) = (term40 m n).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem5451618 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term42 m n p).
Proof. exact (MK_COMB (@lem5451617 m n) (@lem5451614 m n p)). Qed.
Lemma lem5451619 (m : nat) (n : nat) : (term44 m n) = (term44 m n).
Proof. exact (fun_ext (fun p : nat => @lem5451618 m n p)). Qed.
Lemma lem5451620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451621 (m : nat) (n : nat) : (term46 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem5451620) (@lem5451619 m n)). Qed.
Lemma lem5451622 (m : nat) : (term48 m) = (term48 m).
Proof. exact (fun_ext (fun n : nat => @lem5451621 m n)). Qed.
Lemma lem5451623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451624 (m : nat) : (term50 m) = (term50 m).
Proof. exact (MK_COMB (@lem5451623) (@lem5451622 m)). Qed.
Lemma lem5451625 : term52 = term52.
Proof. exact (fun_ext (fun m : nat => @lem5451624 m)). Qed.
Lemma lem5451626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451628 : term54 = term54.
Proof. exact (MK_COMB (@lem5451626) (@lem5451625)). Qed.
Lemma lem5451638 (m : nat) (x : nat) (n : nat) (p : nat) : (term55 m x n p) = (term56 m x n p).
Proof. exact (@lem17045 (Peano.le m x) (term57 x n p)). Qed.
Lemma lem5451650 (m : nat) (x : nat) (n : nat) : (term58 m x n) = (term59 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5451662 (x : nat) (n : nat) (p : nat) : (term60 x n p) = (term61 x n p).
Proof. exact (@lem17045 (term62 n x) (term57 x n p)). Qed.
Lemma lem5451666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5451667 (m : nat) (x : nat) (n : nat) : (term63 m x n) = (term64 m x n).
Proof. exact (MK_COMB (@lem5451666) (@lem5451650 m x n)). Qed.
Lemma lem5451668 (m : nat) (x : nat) (n : nat) (p : nat) : (term65 m x n p) = (term66 m x n p).
Proof. exact (MK_COMB (@lem5451667 m x n) (@lem5451662 x n p)). Qed.
Lemma lem5451669 (m : nat) (x : nat) (n : nat) (p : nat) : (term67 m x n p) = (term65 m x n p).
Proof. exact (@lem17160 (term6 m x n) (term34 x n p)). Qed.
Lemma lem5451670 (m : nat) (x : nat) (n : nat) (p : nat) : (term67 m x n p) = (term66 m x n p).
Proof. exact (TRANS (@lem5451669 m x n p) (@lem5451668 m x n p)). Qed.
Lemma lem5451673 (m : nat) (x : nat) (n : nat) (p : nat) : (term36 m x n p) = (term36 m x n p).
Proof. exact (eq_refl (term36 m x n p)). Qed.
Lemma lem5451674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5451675 (m : nat) (x : nat) (n : nat) (p : nat) : (term68 m x n p) = (term69 m x n p).
Proof. exact (MK_COMB (@lem5451674) (@lem5451638 m x n p)). Qed.
Lemma lem5451676 (m : nat) (x : nat) (n : nat) (p : nat) : (term70 m x n p) = (term71 m x n p).
Proof. exact (MK_COMB (@lem5451675 m x n p) (@lem5451673 m x n p)). Qed.
Lemma lem5451678 (m : nat) (x : nat) (n : nat) (p : nat) : (term72 m x n p) = (term72 m x n p).
Proof. exact (eq_refl (term72 m x n p)). Qed.
Lemma lem5451679 (m : nat) (x : nat) (n : nat) (p : nat) : (term73 m x n p) = (term74 m x n p).
Proof. exact (MK_COMB (@lem5451678 m x n p) (@lem5451670 m x n p)). Qed.
Lemma lem5451680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5451681 (m : nat) (x : nat) (n : nat) (p : nat) : (term75 m x n p) = (term76 m x n p).
Proof. exact (MK_COMB (@lem5451680) (@lem5451679 m x n p)). Qed.
Lemma lem5451682 (m : nat) (x : nat) (n : nat) (p : nat) : (term77 m x n p) = (term78 m x n p).
Proof. exact (MK_COMB (@lem5451681 m x n p) (@lem5451676 m x n p)). Qed.
Lemma lem5451683 (m : nat) (x : nat) (n : nat) (p : nat) : ((term23 m x n p) = (term36 m x n p)) = (term77 m x n p).
Proof. exact (@lem17784 (term23 m x n p) (term36 m x n p)). Qed.
Lemma lem5451684 (m : nat) (x : nat) (n : nat) (p : nat) : ((term23 m x n p) = (term36 m x n p)) = (term78 m x n p).
Proof. exact (TRANS (@lem5451683 m x n p) (@lem5451682 m x n p)). Qed.
Lemma lem5451685 (m : nat) (n : nat) (p : nat) : (term38 m n p) = (term79 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5451684 m x n p)). Qed.
Lemma lem5451686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451687 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term80 m n p).
Proof. exact (MK_COMB (@lem5451686) (@lem5451685 m n p)). Qed.
Lemma lem5451689 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem5451690 (m : nat) (n : nat) (p : nat) : (term82 m n p) = (term83 m n p).
Proof. exact (MK_COMB (@lem5451689 m n) (@lem5451687 m n p)). Qed.
Lemma lem5451691 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term82 m n p).
Proof. exact (@lem17265 (term84 m n) (term39 m n p)). Qed.
Lemma lem5451692 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term83 m n p).
Proof. exact (TRANS (@lem5451691 m n p) (@lem5451690 m n p)). Qed.
Lemma lem5451693 (m : nat) (n : nat) : (term44 m n) = (term85 m n).
Proof. exact (fun_ext (fun p : nat => @lem5451692 m n p)). Qed.
Lemma lem5451694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451695 (m : nat) (n : nat) : (term46 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem5451694) (@lem5451693 m n)). Qed.
Lemma lem5451696 (m : nat) : (term48 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem5451695 m n)). Qed.
Lemma lem5451697 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451698 (m : nat) : (term50 m) = (term88 m).
Proof. exact (MK_COMB (@lem5451697) (@lem5451696 m)). Qed.
Lemma lem5451699 : term52 = term89.
Proof. exact (fun_ext (fun m : nat => @lem5451698 m)). Qed.
Lemma lem5451700 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451701 : term54 = term90.
Proof. exact (MK_COMB (@lem5451700) (@lem5451699)). Qed.
Lemma lem5451702 : term54 = term90.
Proof. exact (TRANS (@lem5451628) (@lem5451701)). Qed.
Lemma lem5451703 (m : nat) (x : nat) (n : nat) (p : nat) : (term78 m x n p) = (term78 m x n p).
Proof. exact (eq_refl (term78 m x n p)). Qed.
Lemma lem5451704 (m : nat) (n : nat) (p : nat) : (term79 m n p) = (term79 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5451703 m x n p)). Qed.
Lemma lem5451705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451706 (m : nat) (n : nat) (p : nat) : (term80 m n p) = (term80 m n p).
Proof. exact (MK_COMB (@lem5451705) (@lem5451704 m n p)). Qed.
Lemma lem5451709 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem5451710 (m : nat) (n : nat) (p : nat) : (term83 m n p) = (term83 m n p).
Proof. exact (MK_COMB (@lem5451709 m n) (@lem5451706 m n p)). Qed.
Lemma lem5451711 (m : nat) (n : nat) : (term85 m n) = (term85 m n).
Proof. exact (fun_ext (fun p : nat => @lem5451710 m n p)). Qed.
Lemma lem5451712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451713 (m : nat) (n : nat) : (term86 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem5451712) (@lem5451711 m n)). Qed.
Lemma lem5451714 (m : nat) : (term87 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem5451713 m n)). Qed.
Lemma lem5451715 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451716 (m : nat) : (term88 m) = (term88 m).
Proof. exact (MK_COMB (@lem5451715) (@lem5451714 m)). Qed.
Lemma lem5451717 : term89 = term89.
Proof. exact (fun_ext (fun m : nat => @lem5451716 m)). Qed.
Lemma lem5451718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451719 : term90 = term90.
Proof. exact (MK_COMB (@lem5451718) (@lem5451717)). Qed.
Lemma lem5451766 : term54 = term90.
Proof. exact (TRANS (@lem5451702) (@lem5451719)). Qed.
Lemma lem5451907 (m : nat) (x : nat) (n : nat) (p : nat) : (term78 m x n p) = (term78 m x n p).
Proof. exact (eq_refl (term78 m x n p)). Qed.
Lemma lem5451908 (m : nat) (n : nat) (p : nat) : (term79 m n p) = (term79 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5451907 m x n p)). Qed.
Lemma lem5451909 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451910 (m : nat) (n : nat) (p : nat) : (term80 m n p) = (term80 m n p).
Proof. exact (MK_COMB (@lem5451909) (@lem5451908 m n p)). Qed.
Lemma lem5451925 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem5451926 (m : nat) (n : nat) (p : nat) : (term83 m n p) = (term83 m n p).
Proof. exact (MK_COMB (@lem5451925 m n) (@lem5451910 m n p)). Qed.
Lemma lem5451927 (m : nat) (n : nat) : (term85 m n) = (term85 m n).
Proof. exact (fun_ext (fun p : nat => @lem5451926 m n p)). Qed.
Lemma lem5451928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451929 (m : nat) (n : nat) : (term86 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem5451928) (@lem5451927 m n)). Qed.
Lemma lem5451930 (m : nat) : (term87 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem5451929 m n)). Qed.
Lemma lem5451931 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451932 (m : nat) : (term88 m) = (term88 m).
Proof. exact (MK_COMB (@lem5451931) (@lem5451930 m)). Qed.
Lemma lem5451933 : term89 = term89.
Proof. exact (fun_ext (fun m : nat => @lem5451932 m)). Qed.
Lemma lem5451934 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451935 : term90 = term90.
Proof. exact (MK_COMB (@lem5451934) (@lem5451933)). Qed.
Lemma lem5451936 : term54 = term90.
Proof. exact (TRANS (@lem5451766) (@lem5451935)). Qed.
Lemma lem5451938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5451939 (P : Prop) (Q : nat -> Prop) : (term93 P Q) = (term94 P Q).
Proof. exact (@lem5451938 nat P Q). Qed.
Lemma lem5451940 (m : nat) (n : nat) (p : nat) : (term95 m n p) = (term96 m n p).
Proof. exact (@lem5451939 (term97 m n) (term79 m n p)). Qed.
Lemma lem5451941 (m : nat) (x : nat) (n : nat) (p : nat) : (term98 m n p x) = (term78 m x n p).
Proof. exact (eq_refl (term98 m n p x)). Qed.
Lemma lem5451942 (m : nat) (n : nat) (p : nat) : (term99 m n p) = (term79 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5451941 m x n p)). Qed.
Lemma lem5451943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451944 (m : nat) (n : nat) (p : nat) : (term100 m n p) = (term80 m n p).
Proof. exact (MK_COMB (@lem5451943) (@lem5451942 m n p)). Qed.
Lemma lem5451945 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem5451946 (m : nat) (n : nat) (p : nat) : (term95 m n p) = (term83 m n p).
Proof. exact (MK_COMB (@lem5451945 m n) (@lem5451944 m n p)). Qed.
Lemma lem5451947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5451948 (m : nat) (n : nat) (p : nat) : (term101 m n p) = (term102 m n p).
Proof. exact (MK_COMB (@lem5451947) (@lem5451946 m n p)). Qed.
Lemma lem5451949 (m : nat) (x : nat) (n : nat) (p : nat) : (term98 m n p x) = (term78 m x n p).
Proof. exact (eq_refl (term98 m n p x)). Qed.
Lemma lem5451950 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem5451951 (m : nat) (x : nat) (n : nat) (p : nat) : (term103 m n p x) = (term104 m x n p).
Proof. exact (MK_COMB (@lem5451950 m n) (@lem5451949 m x n p)). Qed.
Lemma lem5451952 (m : nat) (n : nat) (p : nat) : (term105 m n p) = (term106 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5451951 m x n p)). Qed.
Lemma lem5451953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451954 (m : nat) (n : nat) (p : nat) : (term96 m n p) = (term107 m n p).
Proof. exact (MK_COMB (@lem5451953) (@lem5451952 m n p)). Qed.
Lemma lem5451955 (m : nat) (n : nat) (p : nat) : ((term95 m n p) = (term96 m n p)) = ((term83 m n p) = (term107 m n p)).
Proof. exact (MK_COMB (@lem5451948 m n p) (@lem5451954 m n p)). Qed.
Lemma lem5451956 (m : nat) (n : nat) (p : nat) : (term83 m n p) = (term107 m n p).
Proof. exact (EQ_MP (@lem5451955 m n p) (@lem5451940 m n p)). Qed.
Lemma lem5451957 (m : nat) (n : nat) : (term85 m n) = (term108 m n).
Proof. exact (fun_ext (fun p : nat => @lem5451956 m n p)). Qed.
Lemma lem5451958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451959 (m : nat) (n : nat) : (term86 m n) = (term109 m n).
Proof. exact (MK_COMB (@lem5451958) (@lem5451957 m n)). Qed.
Lemma lem5451960 (m : nat) : (term87 m) = (term110 m).
Proof. exact (fun_ext (fun n : nat => @lem5451959 m n)). Qed.
Lemma lem5451961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451962 (m : nat) : (term88 m) = (term111 m).
Proof. exact (MK_COMB (@lem5451961) (@lem5451960 m)). Qed.
Lemma lem5451963 : term89 = term112.
Proof. exact (fun_ext (fun m : nat => @lem5451962 m)). Qed.
Lemma lem5451964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5451965 : term90 = term113.
Proof. exact (MK_COMB (@lem5451964) (@lem5451963)). Qed.
Lemma lem5451966 : term54 = term113.
Proof. exact (TRANS (@lem5451936) (@lem5451965)). Qed.
Lemma lem5451968 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5451969 (m : nat) (n : nat) : (term84 m n) = (term115 m n).
Proof. exact (@lem5451968 m (term35 n)). Qed.
Lemma lem5451971 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5451972 (n : nat) : (term118 n) = (term119 n).
Proof. exact (@lem5451971 n term120). Qed.
Lemma lem5451973 (m : nat) : (term121 m) = (term121 m).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem5451974 (m : nat) (n : nat) : (term115 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem5451973 m) (@lem5451972 n)). Qed.
Lemma lem5451975 (m : nat) (n : nat) : (term84 m n) = (term122 m n).
Proof. exact (TRANS (@lem5451969 m n) (@lem5451974 m n)). Qed.
Lemma lem5451976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5451977 (m : nat) (n : nat) : (term97 m n) = (term123 m n).
Proof. exact (MK_COMB (@lem5451976) (@lem5451975 m n)). Qed.
Lemma lem5451978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5451979 (m : nat) (n : nat) : (term81 m n) = (term124 m n).
Proof. exact (MK_COMB (@lem5451978) (@lem5451977 m n)). Qed.
Lemma lem5451981 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5451982 (m : nat) (x : nat) : (Peano.le m x) = (term114 m x).
Proof. exact (@lem5451981 m x). Qed.
Lemma lem5451983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5451984 (m : nat) (x : nat) : (term125 m x) = (term126 m x).
Proof. exact (MK_COMB (@lem5451983) (@lem5451982 m x)). Qed.
Lemma lem5451986 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5451987 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term127 x n p).
Proof. exact (@lem5451986 x (Nat.add n p)). Qed.
Lemma lem5451989 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5451990 (n : nat) (p : nat) : (term116 n p) = (term117 n p).
Proof. exact (@lem5451989 n p). Qed.
Lemma lem5451991 (x : nat) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem5451992 (x : nat) (n : nat) (p : nat) : (term127 x n p) = (term128 x n p).
Proof. exact (MK_COMB (@lem5451991 x) (@lem5451990 n p)). Qed.
Lemma lem5451993 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term128 x n p).
Proof. exact (TRANS (@lem5451987 x n p) (@lem5451992 x n p)). Qed.
Lemma lem5451994 (m : nat) (x : nat) (n : nat) (p : nat) : (term23 m x n p) = (term129 m x n p).
Proof. exact (MK_COMB (@lem5451984 m x) (@lem5451993 x n p)). Qed.
Lemma lem5451995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5451996 (m : nat) (x : nat) (n : nat) (p : nat) : (term72 m x n p) = (term130 m x n p).
Proof. exact (MK_COMB (@lem5451995) (@lem5451994 m x n p)). Qed.
Lemma lem5451998 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5451999 (m : nat) (x : nat) : (Peano.le m x) = (term114 m x).
Proof. exact (@lem5451998 m x). Qed.
Lemma lem5452000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5452001 (m : nat) (x : nat) : (term131 m x) = (term132 m x).
Proof. exact (MK_COMB (@lem5452000) (@lem5451999 m x)). Qed.
Lemma lem5452002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452003 (m : nat) (x : nat) : (term133 m x) = (term134 m x).
Proof. exact (MK_COMB (@lem5452002) (@lem5452001 m x)). Qed.
Lemma lem5452005 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452006 (x : nat) (n : nat) : (Peano.le x n) = (term114 x n).
Proof. exact (@lem5452005 x n). Qed.
Lemma lem5452007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5452008 (x : nat) (n : nat) : (term131 x n) = (term132 x n).
Proof. exact (MK_COMB (@lem5452007) (@lem5452006 x n)). Qed.
Lemma lem5452009 (m : nat) (x : nat) (n : nat) : (term59 m x n) = (term135 m x n).
Proof. exact (MK_COMB (@lem5452003 m x) (@lem5452008 x n)). Qed.
Lemma lem5452010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452011 (m : nat) (x : nat) (n : nat) : (term64 m x n) = (term136 m x n).
Proof. exact (MK_COMB (@lem5452010) (@lem5452009 m x n)). Qed.
Lemma lem5452013 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452014 (n : nat) (x : nat) : (term62 n x) = (term137 n x).
Proof. exact (@lem5452013 (term35 n) x). Qed.
Lemma lem5452016 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5452017 (n : nat) : (term118 n) = (term119 n).
Proof. exact (@lem5452016 n term120). Qed.
Lemma lem5452018 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5452019 (n : nat) : (term138 n) = (term139 n).
Proof. exact (MK_COMB (@lem5452018) (@lem5452017 n)). Qed.
Lemma lem5452020 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5452021 (n : nat) (x : nat) : (term137 n x) = (term140 n x).
Proof. exact (MK_COMB (@lem5452019 n) (@lem5452020 x)). Qed.
Lemma lem5452022 (n : nat) (x : nat) : (term62 n x) = (term140 n x).
Proof. exact (TRANS (@lem5452014 n x) (@lem5452021 n x)). Qed.
Lemma lem5452023 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5452024 (n : nat) (x : nat) : (term141 n x) = (term142 n x).
Proof. exact (MK_COMB (@lem5452023) (@lem5452022 n x)). Qed.
Lemma lem5452025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452026 (n : nat) (x : nat) : (term143 n x) = (term144 n x).
Proof. exact (MK_COMB (@lem5452025) (@lem5452024 n x)). Qed.
Lemma lem5452028 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452029 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term127 x n p).
Proof. exact (@lem5452028 x (Nat.add n p)). Qed.
Lemma lem5452031 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5452032 (n : nat) (p : nat) : (term116 n p) = (term117 n p).
Proof. exact (@lem5452031 n p). Qed.
Lemma lem5452033 (x : nat) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem5452034 (x : nat) (n : nat) (p : nat) : (term127 x n p) = (term128 x n p).
Proof. exact (MK_COMB (@lem5452033 x) (@lem5452032 n p)). Qed.
Lemma lem5452035 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term128 x n p).
Proof. exact (TRANS (@lem5452029 x n p) (@lem5452034 x n p)). Qed.
Lemma lem5452036 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5452037 (x : nat) (n : nat) (p : nat) : (term145 x n p) = (term146 x n p).
Proof. exact (MK_COMB (@lem5452036) (@lem5452035 x n p)). Qed.
Lemma lem5452038 (x : nat) (n : nat) (p : nat) : (term61 x n p) = (term147 x n p).
Proof. exact (MK_COMB (@lem5452026 n x) (@lem5452037 x n p)). Qed.
Lemma lem5452039 (m : nat) (x : nat) (n : nat) (p : nat) : (term66 m x n p) = (term148 m x n p).
Proof. exact (MK_COMB (@lem5452011 m x n) (@lem5452038 x n p)). Qed.
Lemma lem5452040 (m : nat) (x : nat) (n : nat) (p : nat) : (term74 m x n p) = (term149 m x n p).
Proof. exact (MK_COMB (@lem5451996 m x n p) (@lem5452039 m x n p)). Qed.
Lemma lem5452041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452042 (m : nat) (x : nat) (n : nat) (p : nat) : (term76 m x n p) = (term150 m x n p).
Proof. exact (MK_COMB (@lem5452041) (@lem5452040 m x n p)). Qed.
Lemma lem5452044 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452045 (m : nat) (x : nat) : (Peano.le m x) = (term114 m x).
Proof. exact (@lem5452044 m x). Qed.
Lemma lem5452046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5452047 (m : nat) (x : nat) : (term131 m x) = (term132 m x).
Proof. exact (MK_COMB (@lem5452046) (@lem5452045 m x)). Qed.
Lemma lem5452048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452049 (m : nat) (x : nat) : (term133 m x) = (term134 m x).
Proof. exact (MK_COMB (@lem5452048) (@lem5452047 m x)). Qed.
Lemma lem5452051 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452052 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term127 x n p).
Proof. exact (@lem5452051 x (Nat.add n p)). Qed.
Lemma lem5452054 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5452055 (n : nat) (p : nat) : (term116 n p) = (term117 n p).
Proof. exact (@lem5452054 n p). Qed.
Lemma lem5452056 (x : nat) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem5452057 (x : nat) (n : nat) (p : nat) : (term127 x n p) = (term128 x n p).
Proof. exact (MK_COMB (@lem5452056 x) (@lem5452055 n p)). Qed.
Lemma lem5452058 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term128 x n p).
Proof. exact (TRANS (@lem5452052 x n p) (@lem5452057 x n p)). Qed.
Lemma lem5452059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5452060 (x : nat) (n : nat) (p : nat) : (term145 x n p) = (term146 x n p).
Proof. exact (MK_COMB (@lem5452059) (@lem5452058 x n p)). Qed.
Lemma lem5452061 (m : nat) (x : nat) (n : nat) (p : nat) : (term56 m x n p) = (term151 m x n p).
Proof. exact (MK_COMB (@lem5452049 m x) (@lem5452060 x n p)). Qed.
Lemma lem5452062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452063 (m : nat) (x : nat) (n : nat) (p : nat) : (term69 m x n p) = (term152 m x n p).
Proof. exact (MK_COMB (@lem5452062) (@lem5452061 m x n p)). Qed.
Lemma lem5452065 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452066 (m : nat) (x : nat) : (Peano.le m x) = (term114 m x).
Proof. exact (@lem5452065 m x). Qed.
Lemma lem5452067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452068 (m : nat) (x : nat) : (term125 m x) = (term126 m x).
Proof. exact (MK_COMB (@lem5452067) (@lem5452066 m x)). Qed.
Lemma lem5452070 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452071 (x : nat) (n : nat) : (Peano.le x n) = (term114 x n).
Proof. exact (@lem5452070 x n). Qed.
Lemma lem5452072 (m : nat) (x : nat) (n : nat) : (term6 m x n) = (term153 m x n).
Proof. exact (MK_COMB (@lem5452068 m x) (@lem5452071 x n)). Qed.
Lemma lem5452073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452074 (m : nat) (x : nat) (n : nat) : (term32 m x n) = (term154 m x n).
Proof. exact (MK_COMB (@lem5452073) (@lem5452072 m x n)). Qed.
Lemma lem5452076 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452077 (n : nat) (x : nat) : (term62 n x) = (term137 n x).
Proof. exact (@lem5452076 (term35 n) x). Qed.
Lemma lem5452079 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5452080 (n : nat) : (term118 n) = (term119 n).
Proof. exact (@lem5452079 n term120). Qed.
Lemma lem5452081 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5452082 (n : nat) : (term138 n) = (term139 n).
Proof. exact (MK_COMB (@lem5452081) (@lem5452080 n)). Qed.
Lemma lem5452083 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem5452084 (n : nat) (x : nat) : (term137 n x) = (term140 n x).
Proof. exact (MK_COMB (@lem5452082 n) (@lem5452083 x)). Qed.
Lemma lem5452085 (n : nat) (x : nat) : (term62 n x) = (term140 n x).
Proof. exact (TRANS (@lem5452077 n x) (@lem5452084 n x)). Qed.
Lemma lem5452086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452087 (n : nat) (x : nat) : (term155 n x) = (term156 n x).
Proof. exact (MK_COMB (@lem5452086) (@lem5452085 n x)). Qed.
Lemma lem5452089 (m : nat) (n : nat) : (Peano.le m n) = (term114 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5452090 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term127 x n p).
Proof. exact (@lem5452089 x (Nat.add n p)). Qed.
Lemma lem5452092 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5452093 (n : nat) (p : nat) : (term116 n p) = (term117 n p).
Proof. exact (@lem5452092 n p). Qed.
Lemma lem5452094 (x : nat) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem5452095 (x : nat) (n : nat) (p : nat) : (term127 x n p) = (term128 x n p).
Proof. exact (MK_COMB (@lem5452094 x) (@lem5452093 n p)). Qed.
Lemma lem5452096 (x : nat) (n : nat) (p : nat) : (term57 x n p) = (term128 x n p).
Proof. exact (TRANS (@lem5452090 x n p) (@lem5452095 x n p)). Qed.
Lemma lem5452097 (x : nat) (n : nat) (p : nat) : (term34 x n p) = (term157 x n p).
Proof. exact (MK_COMB (@lem5452087 n x) (@lem5452096 x n p)). Qed.
Lemma lem5452098 (m : nat) (x : nat) (n : nat) (p : nat) : (term36 m x n p) = (term158 m x n p).
Proof. exact (MK_COMB (@lem5452074 m x n) (@lem5452097 x n p)). Qed.
Lemma lem5452099 (m : nat) (x : nat) (n : nat) (p : nat) : (term71 m x n p) = (term159 m x n p).
Proof. exact (MK_COMB (@lem5452063 m x n p) (@lem5452098 m x n p)). Qed.
Lemma lem5452100 (m : nat) (x : nat) (n : nat) (p : nat) : (term78 m x n p) = (term160 m x n p).
Proof. exact (MK_COMB (@lem5452042 m x n p) (@lem5452099 m x n p)). Qed.
Lemma lem5452101 (m : nat) (x : nat) (n : nat) (p : nat) : (term104 m x n p) = (term161 m x n p).
Proof. exact (MK_COMB (@lem5451979 m n) (@lem5452100 m x n p)). Qed.
Lemma lem5452102 (m : nat) (n : nat) (p : nat) : (term106 m n p) = (term162 m n p).
Proof. exact (fun_ext (fun x : nat => @lem5452101 m x n p)). Qed.
Lemma lem5452103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5452104 (m : nat) (n : nat) (p : nat) : (term107 m n p) = (term163 m n p).
Proof. exact (MK_COMB (@lem5452103) (@lem5452102 m n p)). Qed.
Lemma lem5452105 (m : nat) (n : nat) : (term108 m n) = (term164 m n).
Proof. exact (fun_ext (fun p : nat => @lem5452104 m n p)). Qed.
Lemma lem5452106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5452107 (m : nat) (n : nat) : (term109 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem5452106) (@lem5452105 m n)). Qed.
Lemma lem5452108 (m : nat) : (term110 m) = (term166 m).
Proof. exact (fun_ext (fun n : nat => @lem5452107 m n)). Qed.
Lemma lem5452109 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5452110 (m : nat) : (term111 m) = (term167 m).
Proof. exact (MK_COMB (@lem5452109) (@lem5452108 m)). Qed.
Lemma lem5452111 : term112 = term168.
Proof. exact (fun_ext (fun m : nat => @lem5452110 m)). Qed.
Lemma lem5452112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5452113 : term113 = term169.
Proof. exact (MK_COMB (@lem5452112) (@lem5452111)). Qed.
Lemma lem5452114 : term54 = term169.
Proof. exact (TRANS (@lem5451966) (@lem5452113)). Qed.
Lemma lem5452115 (m : nat) : term170 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5452116 (m : nat) : (term170 m) = (term171 m).
Proof. exact (eq_refl (term170 m)). Qed.
Lemma lem5452117 (m : nat) : term171 m.
Proof. exact (EQ_MP (@lem5452116 m) (@lem5452115 m)). Qed.
Lemma lem5452118 (n : nat) : term170 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5452119 (n : nat) : (term170 n) = (term171 n).
Proof. exact (eq_refl (term170 n)). Qed.
Lemma lem5452120 (n : nat) : term171 n.
Proof. exact (EQ_MP (@lem5452119 n) (@lem5452118 n)). Qed.
Lemma lem5452121 (p : nat) : term170 p.
Proof. exact (@lem2307535 p). Qed.
Lemma lem5452122 (p : nat) : (term170 p) = (term171 p).
Proof. exact (eq_refl (term170 p)). Qed.
Lemma lem5452123 (p : nat) : term171 p.
Proof. exact (EQ_MP (@lem5452122 p) (@lem5452121 p)). Qed.
Lemma lem5452124 (x : nat) : term170 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5452125 (x : nat) : (term170 x) = (term171 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem5452126 (x : nat) : term171 x.
Proof. exact (EQ_MP (@lem5452125 x) (@lem5452124 x)). Qed.
Lemma lem5452127 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term172 _70532 _70535 _70533 _70534) = (term173 _70532 _70535 _70533 _70534).
Proof. exact (@lem2318604 (term173 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452171 (_70532 : int) (_70533 : int) : (term174 _70532 _70533) = (term175 _70532 _70533).
Proof. exact (@lem16933 (term175 _70532 _70533)). Qed.
Lemma lem5452178 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term176 _70532 _70535 _70533 _70534) = (term177 _70532 _70535 _70533 _70534).
Proof. exact (@lem17045 (int_le _70532 _70535) (term178 _70535 _70533 _70534)). Qed.
Lemma lem5452181 (_70532 : int) (_70535 : int) : (term179 _70532 _70535) = (int_le _70532 _70535).
Proof. exact (@lem16933 (int_le _70532 _70535)). Qed.
Lemma lem5452184 (_70535 : int) (_70533 : int) : (term179 _70535 _70533) = (int_le _70535 _70533).
Proof. exact (@lem16933 (int_le _70535 _70533)). Qed.
Lemma lem5452185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452186 (_70532 : int) (_70535 : int) : (term180 _70532 _70535) = (term181 _70532 _70535).
Proof. exact (MK_COMB (@lem5452185) (@lem5452181 _70532 _70535)). Qed.
Lemma lem5452187 (_70532 : int) (_70535 : int) (_70533 : int) : (term182 _70532 _70535 _70533) = (term183 _70532 _70535 _70533).
Proof. exact (MK_COMB (@lem5452186 _70532 _70535) (@lem5452184 _70535 _70533)). Qed.
Lemma lem5452188 (_70532 : int) (_70535 : int) (_70533 : int) : (term184 _70532 _70535 _70533) = (term182 _70532 _70535 _70533).
Proof. exact (@lem17160 (term185 _70532 _70535) (term185 _70535 _70533)). Qed.
Lemma lem5452189 (_70532 : int) (_70535 : int) (_70533 : int) : (term184 _70532 _70535 _70533) = (term183 _70532 _70535 _70533).
Proof. exact (TRANS (@lem5452188 _70532 _70535 _70533) (@lem5452187 _70532 _70535 _70533)). Qed.
Lemma lem5452192 (_70533 : int) (_70535 : int) : (term186 _70533 _70535) = (term187 _70533 _70535).
Proof. exact (@lem16933 (term187 _70533 _70535)). Qed.
Lemma lem5452195 (_70535 : int) (_70533 : int) (_70534 : int) : (term188 _70535 _70533 _70534) = (term178 _70535 _70533 _70534).
Proof. exact (@lem16933 (term178 _70535 _70533 _70534)). Qed.
Lemma lem5452196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452197 (_70533 : int) (_70535 : int) : (term189 _70533 _70535) = (term190 _70533 _70535).
Proof. exact (MK_COMB (@lem5452196) (@lem5452192 _70533 _70535)). Qed.
Lemma lem5452198 (_70535 : int) (_70533 : int) (_70534 : int) : (term191 _70535 _70533 _70534) = (term192 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452197 _70533 _70535) (@lem5452195 _70535 _70533 _70534)). Qed.
Lemma lem5452199 (_70535 : int) (_70533 : int) (_70534 : int) : (term193 _70535 _70533 _70534) = (term191 _70535 _70533 _70534).
Proof. exact (@lem17160 (term194 _70533 _70535) (term195 _70535 _70533 _70534)). Qed.
Lemma lem5452200 (_70535 : int) (_70533 : int) (_70534 : int) : (term193 _70535 _70533 _70534) = (term192 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452199 _70535 _70533 _70534) (@lem5452198 _70535 _70533 _70534)). Qed.
Lemma lem5452201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452202 (_70532 : int) (_70535 : int) (_70533 : int) : (term196 _70532 _70535 _70533) = (term197 _70532 _70535 _70533).
Proof. exact (MK_COMB (@lem5452201) (@lem5452189 _70532 _70535 _70533)). Qed.
Lemma lem5452203 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term198 _70532 _70535 _70533 _70534) = (term199 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452202 _70532 _70535 _70533) (@lem5452200 _70535 _70533 _70534)). Qed.
Lemma lem5452204 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term200 _70532 _70535 _70533 _70534) = (term198 _70532 _70535 _70533 _70534).
Proof. exact (@lem17045 (term201 _70532 _70535 _70533) (term202 _70535 _70533 _70534)). Qed.
Lemma lem5452205 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term200 _70532 _70535 _70533 _70534) = (term199 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452204 _70532 _70535 _70533 _70534) (@lem5452203 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452207 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term203 _70532 _70535 _70533 _70534) = (term204 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452206) (@lem5452178 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452208 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term205 _70532 _70535 _70533 _70534) = (term206 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452207 _70532 _70535 _70533 _70534) (@lem5452205 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452209 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term207 _70532 _70535 _70533 _70534) = (term205 _70532 _70535 _70533 _70534).
Proof. exact (@lem17160 (term208 _70532 _70535 _70533 _70534) (term209 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452210 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term207 _70532 _70535 _70533 _70534) = (term206 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452209 _70532 _70535 _70533 _70534) (@lem5452208 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452213 (_70532 : int) (_70535 : int) : (term179 _70532 _70535) = (int_le _70532 _70535).
Proof. exact (@lem16933 (int_le _70532 _70535)). Qed.
Lemma lem5452216 (_70535 : int) (_70533 : int) (_70534 : int) : (term188 _70535 _70533 _70534) = (term178 _70535 _70533 _70534).
Proof. exact (@lem16933 (term178 _70535 _70533 _70534)). Qed.
Lemma lem5452217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452218 (_70532 : int) (_70535 : int) : (term180 _70532 _70535) = (term181 _70532 _70535).
Proof. exact (MK_COMB (@lem5452217) (@lem5452213 _70532 _70535)). Qed.
Lemma lem5452219 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term210 _70532 _70535 _70533 _70534) = (term208 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452218 _70532 _70535) (@lem5452216 _70535 _70533 _70534)). Qed.
Lemma lem5452220 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term211 _70532 _70535 _70533 _70534) = (term210 _70532 _70535 _70533 _70534).
Proof. exact (@lem17160 (term185 _70532 _70535) (term195 _70535 _70533 _70534)). Qed.
Lemma lem5452221 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term211 _70532 _70535 _70533 _70534) = (term208 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452220 _70532 _70535 _70533 _70534) (@lem5452219 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452228 (_70532 : int) (_70535 : int) (_70533 : int) : (term212 _70532 _70535 _70533) = (term201 _70532 _70535 _70533).
Proof. exact (@lem17045 (int_le _70532 _70535) (int_le _70535 _70533)). Qed.
Lemma lem5452235 (_70535 : int) (_70533 : int) (_70534 : int) : (term213 _70535 _70533 _70534) = (term202 _70535 _70533 _70534).
Proof. exact (@lem17045 (term187 _70533 _70535) (term178 _70535 _70533 _70534)). Qed.
Lemma lem5452236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452237 (_70532 : int) (_70535 : int) (_70533 : int) : (term214 _70532 _70535 _70533) = (term215 _70532 _70535 _70533).
Proof. exact (MK_COMB (@lem5452236) (@lem5452228 _70532 _70535 _70533)). Qed.
Lemma lem5452238 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term216 _70532 _70535 _70533 _70534) = (term209 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452237 _70532 _70535 _70533) (@lem5452235 _70535 _70533 _70534)). Qed.
Lemma lem5452239 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term217 _70532 _70535 _70533 _70534) = (term216 _70532 _70535 _70533 _70534).
Proof. exact (@lem17160 (term183 _70532 _70535 _70533) (term192 _70535 _70533 _70534)). Qed.
Lemma lem5452240 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term217 _70532 _70535 _70533 _70534) = (term209 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452239 _70532 _70535 _70533 _70534) (@lem5452238 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452242 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term218 _70532 _70535 _70533 _70534) = (term219 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452241) (@lem5452221 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452243 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term220 _70532 _70535 _70533 _70534) = (term221 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452242 _70532 _70535 _70533 _70534) (@lem5452240 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452244 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term222 _70532 _70535 _70533 _70534) = (term220 _70532 _70535 _70533 _70534).
Proof. exact (@lem17160 (term177 _70532 _70535 _70533 _70534) (term199 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452245 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term222 _70532 _70535 _70533 _70534) = (term221 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452244 _70532 _70535 _70533 _70534) (@lem5452243 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452247 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term223 _70532 _70535 _70533 _70534) = (term224 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452246) (@lem5452210 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452248 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term225 _70532 _70535 _70533 _70534) = (term226 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452247 _70532 _70535 _70533 _70534) (@lem5452245 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452249 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term227 _70532 _70535 _70533 _70534) = (term225 _70532 _70535 _70533 _70534).
Proof. exact (@lem17045 (term228 _70532 _70535 _70533 _70534) (term229 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452250 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term227 _70532 _70535 _70533 _70534) = (term226 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452249 _70532 _70535 _70533 _70534) (@lem5452248 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452252 (_70532 : int) (_70533 : int) : (term230 _70532 _70533) = (term231 _70532 _70533).
Proof. exact (MK_COMB (@lem5452251) (@lem5452171 _70532 _70533)). Qed.
Lemma lem5452253 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term232 _70532 _70535 _70533 _70534) = (term233 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452252 _70532 _70533) (@lem5452250 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452254 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term234 _70532 _70535 _70533 _70534) = (term232 _70532 _70535 _70533 _70534).
Proof. exact (@lem17160 (term235 _70532 _70533) (term236 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452255 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term234 _70532 _70535 _70533 _70534) = (term233 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452254 _70532 _70535 _70533 _70534) (@lem5452253 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452257 (_70535 : int) : (term237 _70535) = (term237 _70535).
Proof. exact (eq_refl (term237 _70535)). Qed.
Lemma lem5452258 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term238 _70532 _70535 _70533 _70534) = (term239 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452257 _70535) (@lem5452255 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452259 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term240 _70532 _70535 _70533 _70534) = (term238 _70532 _70535 _70533 _70534).
Proof. exact (@lem17362 (term241 _70535) (term242 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452260 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term240 _70532 _70535 _70533 _70534) = (term239 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452259 _70532 _70535 _70533 _70534) (@lem5452258 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452262 (_70534 : int) : (term237 _70534) = (term237 _70534).
Proof. exact (eq_refl (term237 _70534)). Qed.
Lemma lem5452263 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term243 _70532 _70535 _70533 _70534) = (term244 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452262 _70534) (@lem5452260 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452264 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term245 _70532 _70535 _70533 _70534) = (term243 _70532 _70535 _70533 _70534).
Proof. exact (@lem17362 (term241 _70534) (term246 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452265 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term245 _70532 _70535 _70533 _70534) = (term244 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452264 _70532 _70535 _70533 _70534) (@lem5452263 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452267 (_70533 : int) : (term237 _70533) = (term237 _70533).
Proof. exact (eq_refl (term237 _70533)). Qed.
Lemma lem5452268 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term247 _70532 _70535 _70533 _70534) = (term248 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452267 _70533) (@lem5452265 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452269 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term249 _70532 _70535 _70533 _70534) = (term247 _70532 _70535 _70533 _70534).
Proof. exact (@lem17362 (term241 _70533) (term250 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452270 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term249 _70532 _70535 _70533 _70534) = (term248 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452269 _70532 _70535 _70533 _70534) (@lem5452268 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452272 (_70532 : int) : (term237 _70532) = (term237 _70532).
Proof. exact (eq_refl (term237 _70532)). Qed.
Lemma lem5452273 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term251 _70532 _70535 _70533 _70534) = (term252 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452272 _70532) (@lem5452270 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452274 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term253 _70532 _70535 _70533 _70534) = (term251 _70532 _70535 _70533 _70534).
Proof. exact (@lem17362 (term241 _70532) (term254 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452354 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term253 _70532 _70535 _70533 _70534) = (term252 _70532 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452274 _70532 _70535 _70533 _70534) (@lem5452273 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452357 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452358 (_70532 : int) : (term241 _70532) = (term256 _70532).
Proof. exact (@lem5452357 term257 _70532). Qed.
Lemma lem5452360 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452361 : term259 = term260.
Proof. exact (@lem5452360 (NUMERAL 0)). Qed.
Lemma lem5452362 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452363 : term261 = term262.
Proof. exact (MK_COMB (@lem5452362) (@lem5452361)). Qed.
Lemma lem5452364 (_70532 : int) : (real_of_int _70532) = (real_of_int _70532).
Proof. exact (eq_refl (real_of_int _70532)). Qed.
Lemma lem5452365 (_70532 : int) : (term256 _70532) = (term263 _70532).
Proof. exact (MK_COMB (@lem5452363) (@lem5452364 _70532)). Qed.
Lemma lem5452367 (_70532 : int) : (term241 _70532) = (term263 _70532).
Proof. exact (TRANS (@lem5452358 _70532) (@lem5452365 _70532)). Qed.
Lemma lem5452370 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452371 (_70533 : int) : (term241 _70533) = (term256 _70533).
Proof. exact (@lem5452370 term257 _70533). Qed.
Lemma lem5452373 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452374 : term259 = term260.
Proof. exact (@lem5452373 (NUMERAL 0)). Qed.
Lemma lem5452375 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452376 : term261 = term262.
Proof. exact (MK_COMB (@lem5452375) (@lem5452374)). Qed.
Lemma lem5452377 (_70533 : int) : (real_of_int _70533) = (real_of_int _70533).
Proof. exact (eq_refl (real_of_int _70533)). Qed.
Lemma lem5452378 (_70533 : int) : (term256 _70533) = (term263 _70533).
Proof. exact (MK_COMB (@lem5452376) (@lem5452377 _70533)). Qed.
Lemma lem5452380 (_70533 : int) : (term241 _70533) = (term263 _70533).
Proof. exact (TRANS (@lem5452371 _70533) (@lem5452378 _70533)). Qed.
Lemma lem5452383 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452384 (_70534 : int) : (term241 _70534) = (term256 _70534).
Proof. exact (@lem5452383 term257 _70534). Qed.
Lemma lem5452386 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452387 : term259 = term260.
Proof. exact (@lem5452386 (NUMERAL 0)). Qed.
Lemma lem5452388 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452389 : term261 = term262.
Proof. exact (MK_COMB (@lem5452388) (@lem5452387)). Qed.
Lemma lem5452390 (_70534 : int) : (real_of_int _70534) = (real_of_int _70534).
Proof. exact (eq_refl (real_of_int _70534)). Qed.
Lemma lem5452391 (_70534 : int) : (term256 _70534) = (term263 _70534).
Proof. exact (MK_COMB (@lem5452389) (@lem5452390 _70534)). Qed.
Lemma lem5452393 (_70534 : int) : (term241 _70534) = (term263 _70534).
Proof. exact (TRANS (@lem5452384 _70534) (@lem5452391 _70534)). Qed.
Lemma lem5452396 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452397 (_70535 : int) : (term241 _70535) = (term256 _70535).
Proof. exact (@lem5452396 term257 _70535). Qed.
Lemma lem5452399 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452400 : term259 = term260.
Proof. exact (@lem5452399 (NUMERAL 0)). Qed.
Lemma lem5452401 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452402 : term261 = term262.
Proof. exact (MK_COMB (@lem5452401) (@lem5452400)). Qed.
Lemma lem5452403 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5452404 (_70535 : int) : (term256 _70535) = (term263 _70535).
Proof. exact (MK_COMB (@lem5452402) (@lem5452403 _70535)). Qed.
Lemma lem5452406 (_70535 : int) : (term241 _70535) = (term263 _70535).
Proof. exact (TRANS (@lem5452397 _70535) (@lem5452404 _70535)). Qed.
Lemma lem5452409 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452410 (_70532 : int) (_70533 : int) : (term175 _70532 _70533) = (term264 _70532 _70533).
Proof. exact (@lem5452409 _70532 (term265 _70533)). Qed.
Lemma lem5452412 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452413 (_70533 : int) : (term268 _70533) = (term269 _70533).
Proof. exact (@lem5452412 _70533 term270). Qed.
Lemma lem5452415 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452416 : term271 = term272.
Proof. exact (@lem5452415 term120). Qed.
Lemma lem5452417 (_70533 : int) : (term273 _70533) = (term273 _70533).
Proof. exact (eq_refl (term273 _70533)). Qed.
Lemma lem5452418 (_70533 : int) : (term269 _70533) = (term274 _70533).
Proof. exact (MK_COMB (@lem5452417 _70533) (@lem5452416)). Qed.
Lemma lem5452419 (_70533 : int) : (term268 _70533) = (term274 _70533).
Proof. exact (TRANS (@lem5452413 _70533) (@lem5452418 _70533)). Qed.
Lemma lem5452420 (_70532 : int) : (term275 _70532) = (term275 _70532).
Proof. exact (eq_refl (term275 _70532)). Qed.
Lemma lem5452421 (_70532 : int) (_70533 : int) : (term264 _70532 _70533) = (term276 _70532 _70533).
Proof. exact (MK_COMB (@lem5452420 _70532) (@lem5452419 _70533)). Qed.
Lemma lem5452423 (_70532 : int) (_70533 : int) : (term175 _70532 _70533) = (term276 _70532 _70533).
Proof. exact (TRANS (@lem5452410 _70532 _70533) (@lem5452421 _70532 _70533)). Qed.
Lemma lem5452425 (y : int) (x : int) : (term185 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5452426 (_70535 : int) (_70532 : int) : (term185 _70532 _70535) = (term187 _70535 _70532).
Proof. exact (@lem5452425 _70535 _70532). Qed.
Lemma lem5452428 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452429 (_70535 : int) (_70532 : int) : (term187 _70535 _70532) = (term277 _70535 _70532).
Proof. exact (@lem5452428 (term265 _70535) _70532). Qed.
Lemma lem5452431 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452432 (_70535 : int) : (term268 _70535) = (term269 _70535).
Proof. exact (@lem5452431 _70535 term270). Qed.
Lemma lem5452434 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452435 : term271 = term272.
Proof. exact (@lem5452434 term120). Qed.
Lemma lem5452436 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5452437 (_70535 : int) : (term269 _70535) = (term274 _70535).
Proof. exact (MK_COMB (@lem5452436 _70535) (@lem5452435)). Qed.
Lemma lem5452438 (_70535 : int) : (term268 _70535) = (term274 _70535).
Proof. exact (TRANS (@lem5452432 _70535) (@lem5452437 _70535)). Qed.
Lemma lem5452439 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452440 (_70535 : int) : (term278 _70535) = (term279 _70535).
Proof. exact (MK_COMB (@lem5452439) (@lem5452438 _70535)). Qed.
Lemma lem5452441 (_70532 : int) : (real_of_int _70532) = (real_of_int _70532).
Proof. exact (eq_refl (real_of_int _70532)). Qed.
Lemma lem5452442 (_70535 : int) (_70532 : int) : (term277 _70535 _70532) = (term280 _70535 _70532).
Proof. exact (MK_COMB (@lem5452440 _70535) (@lem5452441 _70532)). Qed.
Lemma lem5452443 (_70535 : int) (_70532 : int) : (term187 _70535 _70532) = (term280 _70535 _70532).
Proof. exact (TRANS (@lem5452429 _70535 _70532) (@lem5452442 _70535 _70532)). Qed.
Lemma lem5452444 (_70535 : int) (_70532 : int) : (term185 _70532 _70535) = (term280 _70535 _70532).
Proof. exact (TRANS (@lem5452426 _70535 _70532) (@lem5452443 _70535 _70532)). Qed.
Lemma lem5452446 (y : int) (x : int) : (term185 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5452447 (_70533 : int) (_70534 : int) (_70535 : int) : (term195 _70535 _70533 _70534) = (term281 _70533 _70534 _70535).
Proof. exact (@lem5452446 (int_add _70533 _70534) _70535). Qed.
Lemma lem5452449 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452450 (_70533 : int) (_70534 : int) (_70535 : int) : (term281 _70533 _70534 _70535) = (term282 _70533 _70534 _70535).
Proof. exact (@lem5452449 (term283 _70533 _70534) _70535). Qed.
Lemma lem5452452 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452453 (_70533 : int) (_70534 : int) : (term284 _70533 _70534) = (term285 _70533 _70534).
Proof. exact (@lem5452452 (int_add _70533 _70534) term270). Qed.
Lemma lem5452455 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452456 (_70533 : int) (_70534 : int) : (term266 _70533 _70534) = (term267 _70533 _70534).
Proof. exact (@lem5452455 _70533 _70534). Qed.
Lemma lem5452457 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5452458 (_70533 : int) (_70534 : int) : (term286 _70533 _70534) = (term287 _70533 _70534).
Proof. exact (MK_COMB (@lem5452457) (@lem5452456 _70533 _70534)). Qed.
Lemma lem5452460 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452461 : term271 = term272.
Proof. exact (@lem5452460 term120). Qed.
Lemma lem5452462 (_70533 : int) (_70534 : int) : (term285 _70533 _70534) = (term288 _70533 _70534).
Proof. exact (MK_COMB (@lem5452458 _70533 _70534) (@lem5452461)). Qed.
Lemma lem5452463 (_70533 : int) (_70534 : int) : (term284 _70533 _70534) = (term288 _70533 _70534).
Proof. exact (TRANS (@lem5452453 _70533 _70534) (@lem5452462 _70533 _70534)). Qed.
Lemma lem5452464 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452465 (_70533 : int) (_70534 : int) : (term289 _70533 _70534) = (term290 _70533 _70534).
Proof. exact (MK_COMB (@lem5452464) (@lem5452463 _70533 _70534)). Qed.
Lemma lem5452466 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5452467 (_70533 : int) (_70534 : int) (_70535 : int) : (term282 _70533 _70534 _70535) = (term291 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452465 _70533 _70534) (@lem5452466 _70535)). Qed.
Lemma lem5452468 (_70533 : int) (_70534 : int) (_70535 : int) : (term281 _70533 _70534 _70535) = (term291 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5452450 _70533 _70534 _70535) (@lem5452467 _70533 _70534 _70535)). Qed.
Lemma lem5452469 (_70533 : int) (_70534 : int) (_70535 : int) : (term195 _70535 _70533 _70534) = (term291 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5452447 _70533 _70534 _70535) (@lem5452468 _70533 _70534 _70535)). Qed.
Lemma lem5452470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452471 (_70535 : int) (_70532 : int) : (term292 _70532 _70535) = (term293 _70535 _70532).
Proof. exact (MK_COMB (@lem5452470) (@lem5452444 _70535 _70532)). Qed.
Lemma lem5452472 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term177 _70532 _70535 _70533 _70534) = (term294 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452471 _70535 _70532) (@lem5452469 _70533 _70534 _70535)). Qed.
Lemma lem5452475 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452477 (_70532 : int) (_70535 : int) : (int_le _70532 _70535) = (term255 _70532 _70535).
Proof. exact (@lem5452475 _70532 _70535). Qed.
Lemma lem5452480 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452482 (_70535 : int) (_70533 : int) : (int_le _70535 _70533) = (term255 _70535 _70533).
Proof. exact (@lem5452480 _70535 _70533). Qed.
Lemma lem5452483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452484 (_70532 : int) (_70535 : int) : (term181 _70532 _70535) = (term295 _70532 _70535).
Proof. exact (MK_COMB (@lem5452483) (@lem5452477 _70532 _70535)). Qed.
Lemma lem5452485 (_70532 : int) (_70535 : int) (_70533 : int) : (term183 _70532 _70535 _70533) = (term296 _70532 _70535 _70533).
Proof. exact (MK_COMB (@lem5452484 _70532 _70535) (@lem5452482 _70535 _70533)). Qed.
Lemma lem5452488 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452489 (_70533 : int) (_70535 : int) : (term187 _70533 _70535) = (term277 _70533 _70535).
Proof. exact (@lem5452488 (term265 _70533) _70535). Qed.
Lemma lem5452491 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452492 (_70533 : int) : (term268 _70533) = (term269 _70533).
Proof. exact (@lem5452491 _70533 term270). Qed.
Lemma lem5452494 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452495 : term271 = term272.
Proof. exact (@lem5452494 term120). Qed.
Lemma lem5452496 (_70533 : int) : (term273 _70533) = (term273 _70533).
Proof. exact (eq_refl (term273 _70533)). Qed.
Lemma lem5452497 (_70533 : int) : (term269 _70533) = (term274 _70533).
Proof. exact (MK_COMB (@lem5452496 _70533) (@lem5452495)). Qed.
Lemma lem5452498 (_70533 : int) : (term268 _70533) = (term274 _70533).
Proof. exact (TRANS (@lem5452492 _70533) (@lem5452497 _70533)). Qed.
Lemma lem5452499 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452500 (_70533 : int) : (term278 _70533) = (term279 _70533).
Proof. exact (MK_COMB (@lem5452499) (@lem5452498 _70533)). Qed.
Lemma lem5452501 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5452502 (_70533 : int) (_70535 : int) : (term277 _70533 _70535) = (term280 _70533 _70535).
Proof. exact (MK_COMB (@lem5452500 _70533) (@lem5452501 _70535)). Qed.
Lemma lem5452504 (_70533 : int) (_70535 : int) : (term187 _70533 _70535) = (term280 _70533 _70535).
Proof. exact (TRANS (@lem5452489 _70533 _70535) (@lem5452502 _70533 _70535)). Qed.
Lemma lem5452507 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452508 (_70535 : int) (_70533 : int) (_70534 : int) : (term178 _70535 _70533 _70534) = (term297 _70535 _70533 _70534).
Proof. exact (@lem5452507 _70535 (int_add _70533 _70534)). Qed.
Lemma lem5452510 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452511 (_70533 : int) (_70534 : int) : (term266 _70533 _70534) = (term267 _70533 _70534).
Proof. exact (@lem5452510 _70533 _70534). Qed.
Lemma lem5452512 (_70535 : int) : (term275 _70535) = (term275 _70535).
Proof. exact (eq_refl (term275 _70535)). Qed.
Lemma lem5452513 (_70535 : int) (_70533 : int) (_70534 : int) : (term297 _70535 _70533 _70534) = (term298 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452512 _70535) (@lem5452511 _70533 _70534)). Qed.
Lemma lem5452515 (_70535 : int) (_70533 : int) (_70534 : int) : (term178 _70535 _70533 _70534) = (term298 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452508 _70535 _70533 _70534) (@lem5452513 _70535 _70533 _70534)). Qed.
Lemma lem5452516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452517 (_70533 : int) (_70535 : int) : (term190 _70533 _70535) = (term299 _70533 _70535).
Proof. exact (MK_COMB (@lem5452516) (@lem5452504 _70533 _70535)). Qed.
Lemma lem5452518 (_70535 : int) (_70533 : int) (_70534 : int) : (term192 _70535 _70533 _70534) = (term300 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452517 _70533 _70535) (@lem5452515 _70535 _70533 _70534)). Qed.
Lemma lem5452519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452520 (_70532 : int) (_70535 : int) (_70533 : int) : (term197 _70532 _70535 _70533) = (term301 _70532 _70535 _70533).
Proof. exact (MK_COMB (@lem5452519) (@lem5452485 _70532 _70535 _70533)). Qed.
Lemma lem5452521 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term199 _70532 _70535 _70533 _70534) = (term302 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452520 _70532 _70535 _70533) (@lem5452518 _70535 _70533 _70534)). Qed.
Lemma lem5452522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452523 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term204 _70532 _70535 _70533 _70534) = (term303 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452522) (@lem5452472 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452524 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term206 _70532 _70535 _70533 _70534) = (term304 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452523 _70532 _70533 _70534 _70535) (@lem5452521 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452527 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452529 (_70532 : int) (_70535 : int) : (int_le _70532 _70535) = (term255 _70532 _70535).
Proof. exact (@lem5452527 _70532 _70535). Qed.
Lemma lem5452532 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452533 (_70535 : int) (_70533 : int) (_70534 : int) : (term178 _70535 _70533 _70534) = (term297 _70535 _70533 _70534).
Proof. exact (@lem5452532 _70535 (int_add _70533 _70534)). Qed.
Lemma lem5452535 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452536 (_70533 : int) (_70534 : int) : (term266 _70533 _70534) = (term267 _70533 _70534).
Proof. exact (@lem5452535 _70533 _70534). Qed.
Lemma lem5452537 (_70535 : int) : (term275 _70535) = (term275 _70535).
Proof. exact (eq_refl (term275 _70535)). Qed.
Lemma lem5452538 (_70535 : int) (_70533 : int) (_70534 : int) : (term297 _70535 _70533 _70534) = (term298 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452537 _70535) (@lem5452536 _70533 _70534)). Qed.
Lemma lem5452540 (_70535 : int) (_70533 : int) (_70534 : int) : (term178 _70535 _70533 _70534) = (term298 _70535 _70533 _70534).
Proof. exact (TRANS (@lem5452533 _70535 _70533 _70534) (@lem5452538 _70535 _70533 _70534)). Qed.
Lemma lem5452541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452542 (_70532 : int) (_70535 : int) : (term181 _70532 _70535) = (term295 _70532 _70535).
Proof. exact (MK_COMB (@lem5452541) (@lem5452529 _70532 _70535)). Qed.
Lemma lem5452543 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term208 _70532 _70535 _70533 _70534) = (term305 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452542 _70532 _70535) (@lem5452540 _70535 _70533 _70534)). Qed.
Lemma lem5452545 (y : int) (x : int) : (term185 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5452546 (_70535 : int) (_70532 : int) : (term185 _70532 _70535) = (term187 _70535 _70532).
Proof. exact (@lem5452545 _70535 _70532). Qed.
Lemma lem5452548 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452549 (_70535 : int) (_70532 : int) : (term187 _70535 _70532) = (term277 _70535 _70532).
Proof. exact (@lem5452548 (term265 _70535) _70532). Qed.
Lemma lem5452551 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452552 (_70535 : int) : (term268 _70535) = (term269 _70535).
Proof. exact (@lem5452551 _70535 term270). Qed.
Lemma lem5452554 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452555 : term271 = term272.
Proof. exact (@lem5452554 term120). Qed.
Lemma lem5452556 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5452557 (_70535 : int) : (term269 _70535) = (term274 _70535).
Proof. exact (MK_COMB (@lem5452556 _70535) (@lem5452555)). Qed.
Lemma lem5452558 (_70535 : int) : (term268 _70535) = (term274 _70535).
Proof. exact (TRANS (@lem5452552 _70535) (@lem5452557 _70535)). Qed.
Lemma lem5452559 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452560 (_70535 : int) : (term278 _70535) = (term279 _70535).
Proof. exact (MK_COMB (@lem5452559) (@lem5452558 _70535)). Qed.
Lemma lem5452561 (_70532 : int) : (real_of_int _70532) = (real_of_int _70532).
Proof. exact (eq_refl (real_of_int _70532)). Qed.
Lemma lem5452562 (_70535 : int) (_70532 : int) : (term277 _70535 _70532) = (term280 _70535 _70532).
Proof. exact (MK_COMB (@lem5452560 _70535) (@lem5452561 _70532)). Qed.
Lemma lem5452563 (_70535 : int) (_70532 : int) : (term187 _70535 _70532) = (term280 _70535 _70532).
Proof. exact (TRANS (@lem5452549 _70535 _70532) (@lem5452562 _70535 _70532)). Qed.
Lemma lem5452564 (_70535 : int) (_70532 : int) : (term185 _70532 _70535) = (term280 _70535 _70532).
Proof. exact (TRANS (@lem5452546 _70535 _70532) (@lem5452563 _70535 _70532)). Qed.
Lemma lem5452566 (y : int) (x : int) : (term185 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5452567 (_70533 : int) (_70535 : int) : (term185 _70535 _70533) = (term187 _70533 _70535).
Proof. exact (@lem5452566 _70533 _70535). Qed.
Lemma lem5452569 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452570 (_70533 : int) (_70535 : int) : (term187 _70533 _70535) = (term277 _70533 _70535).
Proof. exact (@lem5452569 (term265 _70533) _70535). Qed.
Lemma lem5452572 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452573 (_70533 : int) : (term268 _70533) = (term269 _70533).
Proof. exact (@lem5452572 _70533 term270). Qed.
Lemma lem5452575 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452576 : term271 = term272.
Proof. exact (@lem5452575 term120). Qed.
Lemma lem5452577 (_70533 : int) : (term273 _70533) = (term273 _70533).
Proof. exact (eq_refl (term273 _70533)). Qed.
Lemma lem5452578 (_70533 : int) : (term269 _70533) = (term274 _70533).
Proof. exact (MK_COMB (@lem5452577 _70533) (@lem5452576)). Qed.
Lemma lem5452579 (_70533 : int) : (term268 _70533) = (term274 _70533).
Proof. exact (TRANS (@lem5452573 _70533) (@lem5452578 _70533)). Qed.
Lemma lem5452580 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452581 (_70533 : int) : (term278 _70533) = (term279 _70533).
Proof. exact (MK_COMB (@lem5452580) (@lem5452579 _70533)). Qed.
Lemma lem5452582 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5452583 (_70533 : int) (_70535 : int) : (term277 _70533 _70535) = (term280 _70533 _70535).
Proof. exact (MK_COMB (@lem5452581 _70533) (@lem5452582 _70535)). Qed.
Lemma lem5452584 (_70533 : int) (_70535 : int) : (term187 _70533 _70535) = (term280 _70533 _70535).
Proof. exact (TRANS (@lem5452570 _70533 _70535) (@lem5452583 _70533 _70535)). Qed.
Lemma lem5452585 (_70533 : int) (_70535 : int) : (term185 _70535 _70533) = (term280 _70533 _70535).
Proof. exact (TRANS (@lem5452567 _70533 _70535) (@lem5452584 _70533 _70535)). Qed.
Lemma lem5452586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452587 (_70535 : int) (_70532 : int) : (term292 _70532 _70535) = (term293 _70535 _70532).
Proof. exact (MK_COMB (@lem5452586) (@lem5452564 _70535 _70532)). Qed.
Lemma lem5452588 (_70532 : int) (_70533 : int) (_70535 : int) : (term201 _70532 _70535 _70533) = (term306 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5452587 _70535 _70532) (@lem5452585 _70533 _70535)). Qed.
Lemma lem5452590 (y : int) (x : int) : (term185 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5452591 (_70535 : int) (_70533 : int) : (term194 _70533 _70535) = (term307 _70535 _70533).
Proof. exact (@lem5452590 _70535 (term265 _70533)). Qed.
Lemma lem5452593 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452594 (_70535 : int) (_70533 : int) : (term307 _70535 _70533) = (term308 _70535 _70533).
Proof. exact (@lem5452593 (term265 _70535) (term265 _70533)). Qed.
Lemma lem5452596 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452597 (_70535 : int) : (term268 _70535) = (term269 _70535).
Proof. exact (@lem5452596 _70535 term270). Qed.
Lemma lem5452599 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452600 : term271 = term272.
Proof. exact (@lem5452599 term120). Qed.
Lemma lem5452601 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5452602 (_70535 : int) : (term269 _70535) = (term274 _70535).
Proof. exact (MK_COMB (@lem5452601 _70535) (@lem5452600)). Qed.
Lemma lem5452603 (_70535 : int) : (term268 _70535) = (term274 _70535).
Proof. exact (TRANS (@lem5452597 _70535) (@lem5452602 _70535)). Qed.
Lemma lem5452604 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452605 (_70535 : int) : (term278 _70535) = (term279 _70535).
Proof. exact (MK_COMB (@lem5452604) (@lem5452603 _70535)). Qed.
Lemma lem5452607 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452608 (_70533 : int) : (term268 _70533) = (term269 _70533).
Proof. exact (@lem5452607 _70533 term270). Qed.
Lemma lem5452610 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452611 : term271 = term272.
Proof. exact (@lem5452610 term120). Qed.
Lemma lem5452612 (_70533 : int) : (term273 _70533) = (term273 _70533).
Proof. exact (eq_refl (term273 _70533)). Qed.
Lemma lem5452613 (_70533 : int) : (term269 _70533) = (term274 _70533).
Proof. exact (MK_COMB (@lem5452612 _70533) (@lem5452611)). Qed.
Lemma lem5452614 (_70533 : int) : (term268 _70533) = (term274 _70533).
Proof. exact (TRANS (@lem5452608 _70533) (@lem5452613 _70533)). Qed.
Lemma lem5452615 (_70535 : int) (_70533 : int) : (term308 _70535 _70533) = (term309 _70535 _70533).
Proof. exact (MK_COMB (@lem5452605 _70535) (@lem5452614 _70533)). Qed.
Lemma lem5452616 (_70535 : int) (_70533 : int) : (term307 _70535 _70533) = (term309 _70535 _70533).
Proof. exact (TRANS (@lem5452594 _70535 _70533) (@lem5452615 _70535 _70533)). Qed.
Lemma lem5452617 (_70535 : int) (_70533 : int) : (term194 _70533 _70535) = (term309 _70535 _70533).
Proof. exact (TRANS (@lem5452591 _70535 _70533) (@lem5452616 _70535 _70533)). Qed.
Lemma lem5452619 (y : int) (x : int) : (term185 x y) = (term187 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5452620 (_70533 : int) (_70534 : int) (_70535 : int) : (term195 _70535 _70533 _70534) = (term281 _70533 _70534 _70535).
Proof. exact (@lem5452619 (int_add _70533 _70534) _70535). Qed.
Lemma lem5452622 (x : int) (y : int) : (int_le x y) = (term255 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5452623 (_70533 : int) (_70534 : int) (_70535 : int) : (term281 _70533 _70534 _70535) = (term282 _70533 _70534 _70535).
Proof. exact (@lem5452622 (term283 _70533 _70534) _70535). Qed.
Lemma lem5452625 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452626 (_70533 : int) (_70534 : int) : (term284 _70533 _70534) = (term285 _70533 _70534).
Proof. exact (@lem5452625 (int_add _70533 _70534) term270). Qed.
Lemma lem5452628 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5452629 (_70533 : int) (_70534 : int) : (term266 _70533 _70534) = (term267 _70533 _70534).
Proof. exact (@lem5452628 _70533 _70534). Qed.
Lemma lem5452630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5452631 (_70533 : int) (_70534 : int) : (term286 _70533 _70534) = (term287 _70533 _70534).
Proof. exact (MK_COMB (@lem5452630) (@lem5452629 _70533 _70534)). Qed.
Lemma lem5452633 (n : nat) : (term258 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5452634 : term271 = term272.
Proof. exact (@lem5452633 term120). Qed.
Lemma lem5452635 (_70533 : int) (_70534 : int) : (term285 _70533 _70534) = (term288 _70533 _70534).
Proof. exact (MK_COMB (@lem5452631 _70533 _70534) (@lem5452634)). Qed.
Lemma lem5452636 (_70533 : int) (_70534 : int) : (term284 _70533 _70534) = (term288 _70533 _70534).
Proof. exact (TRANS (@lem5452626 _70533 _70534) (@lem5452635 _70533 _70534)). Qed.
Lemma lem5452637 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5452638 (_70533 : int) (_70534 : int) : (term289 _70533 _70534) = (term290 _70533 _70534).
Proof. exact (MK_COMB (@lem5452637) (@lem5452636 _70533 _70534)). Qed.
Lemma lem5452639 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5452640 (_70533 : int) (_70534 : int) (_70535 : int) : (term282 _70533 _70534 _70535) = (term291 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452638 _70533 _70534) (@lem5452639 _70535)). Qed.
Lemma lem5452641 (_70533 : int) (_70534 : int) (_70535 : int) : (term281 _70533 _70534 _70535) = (term291 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5452623 _70533 _70534 _70535) (@lem5452640 _70533 _70534 _70535)). Qed.
Lemma lem5452642 (_70533 : int) (_70534 : int) (_70535 : int) : (term195 _70535 _70533 _70534) = (term291 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5452620 _70533 _70534 _70535) (@lem5452641 _70533 _70534 _70535)). Qed.
Lemma lem5452643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452644 (_70535 : int) (_70533 : int) : (term310 _70533 _70535) = (term311 _70535 _70533).
Proof. exact (MK_COMB (@lem5452643) (@lem5452617 _70535 _70533)). Qed.
Lemma lem5452645 (_70533 : int) (_70534 : int) (_70535 : int) : (term202 _70535 _70533 _70534) = (term312 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452644 _70535 _70533) (@lem5452642 _70533 _70534 _70535)). Qed.
Lemma lem5452646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452647 (_70532 : int) (_70533 : int) (_70535 : int) : (term215 _70532 _70535 _70533) = (term313 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5452646) (@lem5452588 _70532 _70533 _70535)). Qed.
Lemma lem5452648 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term209 _70532 _70535 _70533 _70534) = (term314 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452647 _70532 _70533 _70535) (@lem5452645 _70533 _70534 _70535)). Qed.
Lemma lem5452649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452650 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term219 _70532 _70535 _70533 _70534) = (term315 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452649) (@lem5452543 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452651 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term221 _70532 _70535 _70533 _70534) = (term316 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452650 _70532 _70535 _70533 _70534) (@lem5452648 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5452653 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term224 _70532 _70535 _70533 _70534) = (term317 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5452652) (@lem5452524 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5452654 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term226 _70532 _70535 _70533 _70534) = (term318 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452653 _70532 _70535 _70533 _70534) (@lem5452651 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452656 (_70532 : int) (_70533 : int) : (term231 _70532 _70533) = (term319 _70532 _70533).
Proof. exact (MK_COMB (@lem5452655) (@lem5452423 _70532 _70533)). Qed.
Lemma lem5452657 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term233 _70532 _70535 _70533 _70534) = (term320 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452656 _70532 _70533) (@lem5452654 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452659 (_70535 : int) : (term237 _70535) = (term321 _70535).
Proof. exact (MK_COMB (@lem5452658) (@lem5452406 _70535)). Qed.
Lemma lem5452660 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term239 _70532 _70535 _70533 _70534) = (term322 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452659 _70535) (@lem5452657 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452662 (_70534 : int) : (term237 _70534) = (term321 _70534).
Proof. exact (MK_COMB (@lem5452661) (@lem5452393 _70534)). Qed.
Lemma lem5452663 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term244 _70532 _70535 _70533 _70534) = (term323 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452662 _70534) (@lem5452660 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452665 (_70533 : int) : (term237 _70533) = (term321 _70533).
Proof. exact (MK_COMB (@lem5452664) (@lem5452380 _70533)). Qed.
Lemma lem5452666 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term248 _70532 _70535 _70533 _70534) = (term324 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452665 _70533) (@lem5452663 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5452668 (_70532 : int) : (term237 _70532) = (term321 _70532).
Proof. exact (MK_COMB (@lem5452667) (@lem5452367 _70532)). Qed.
Lemma lem5452669 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term252 _70532 _70535 _70533 _70534) = (term325 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5452668 _70532) (@lem5452666 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452670 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term253 _70532 _70535 _70533 _70534) = (term325 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5452354 _70532 _70535 _70533 _70534) (@lem5452669 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452674 (t : Prop) : (term326 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5452840 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term327 _70532 _70533 _70534 _70535) = (term325 _70532 _70533 _70534 _70535).
Proof. exact (@lem5452674 (term325 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5452841 (_70532 : int) : (term263 _70532) = (term328 _70532).
Proof. exact (@lem1988287 (real_of_int _70532) term260). Qed.
Lemma lem5452847 (_70532 : int) : (term329 _70532) = (term330 _70532).
Proof. exact (@lem1982792 (real_of_int _70532) term260). Qed.
Lemma lem5452849 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5452850 : term260 = term332.
Proof. exact (@lem5452849 (NUMERAL 0)). Qed.
Lemma lem5452852 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5452853 : term335 = term336.
Proof. exact (@lem5452852 term120). Qed.
Lemma lem5452854 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5452855 : term337 = term338.
Proof. exact (MK_COMB (@lem5452854) (@lem5452853)). Qed.
Lemma lem5452856 : term339 = term340.
Proof. exact (MK_COMB (@lem5452855) (@lem5452850)). Qed.
Lemma lem5452857 : term340 = term341.
Proof. exact (@lem1981613 term335 term260 term272 term272). Qed.
Lemma lem5452859 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5452860 : term344 = term345.
Proof. exact (@lem5452859 term120 term120). Qed.
Lemma lem5452861 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5452862 : term347 = term120.
Proof. exact (EQ_MP (@lem5452861) (@lem940073)). Qed.
Lemma lem5452863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5452864 : term345 = term272.
Proof. exact (MK_COMB (@lem5452863) (@lem5452862)). Qed.
Lemma lem5452865 : term344 = term272.
Proof. exact (TRANS (@lem5452860) (@lem5452864)). Qed.
Lemma lem5452867 (x : nat) : (term348 x) = term260.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5452868 : term339 = term260.
Proof. exact (@lem5452867 term120). Qed.
Lemma lem5452869 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5452870 : term349 = term350.
Proof. exact (MK_COMB (@lem5452869) (@lem5452868)). Qed.
Lemma lem5452871 : term341 = term332.
Proof. exact (MK_COMB (@lem5452870) (@lem5452865)). Qed.
Lemma lem5452872 : term340 = term332.
Proof. exact (TRANS (@lem5452857) (@lem5452871)). Qed.
Lemma lem5452873 : term339 = term332.
Proof. exact (TRANS (@lem5452856) (@lem5452872)). Qed.
Lemma lem5452875 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5452876 : term332 = term260.
Proof. exact (@lem5452875 term260). Qed.
Lemma lem5452877 : term339 = term260.
Proof. exact (TRANS (@lem5452873) (@lem5452876)). Qed.
Lemma lem5452878 (_70532 : int) : (term273 _70532) = (term273 _70532).
Proof. exact (eq_refl (term273 _70532)). Qed.
Lemma lem5452879 (_70532 : int) : (term330 _70532) = (term352 _70532).
Proof. exact (MK_COMB (@lem5452878 _70532) (@lem5452877)). Qed.
Lemma lem5452880 (_70532 : int) : (term352 _70532) = (real_of_int _70532).
Proof. exact (@lem1982723 (real_of_int _70532)). Qed.
Lemma lem5452881 (_70532 : int) : (term330 _70532) = (real_of_int _70532).
Proof. exact (TRANS (@lem5452879 _70532) (@lem5452880 _70532)). Qed.
Lemma lem5452883 (_70532 : int) : (term329 _70532) = (real_of_int _70532).
Proof. exact (TRANS (@lem5452847 _70532) (@lem5452881 _70532)). Qed.
Lemma lem5452884 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5452885 (_70532 : int) : (term353 _70532) = (term354 _70532).
Proof. exact (MK_COMB (@lem5452884) (@lem5452883 _70532)). Qed.
Lemma lem5452886 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5452887 (_70532 : int) : (term328 _70532) = (term355 _70532).
Proof. exact (MK_COMB (@lem5452885 _70532) (@lem5452886)). Qed.
Lemma lem5452888 (_70532 : int) : (term263 _70532) = (term355 _70532).
Proof. exact (TRANS (@lem5452841 _70532) (@lem5452887 _70532)). Qed.
Lemma lem5452889 (_70533 : int) : (term263 _70533) = (term328 _70533).
Proof. exact (@lem1988287 (real_of_int _70533) term260). Qed.
Lemma lem5452895 (_70533 : int) : (term329 _70533) = (term330 _70533).
Proof. exact (@lem1982792 (real_of_int _70533) term260). Qed.
Lemma lem5452897 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5452898 : term260 = term332.
Proof. exact (@lem5452897 (NUMERAL 0)). Qed.
Lemma lem5452900 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5452901 : term335 = term336.
Proof. exact (@lem5452900 term120). Qed.
Lemma lem5452902 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5452903 : term337 = term338.
Proof. exact (MK_COMB (@lem5452902) (@lem5452901)). Qed.
Lemma lem5452904 : term339 = term340.
Proof. exact (MK_COMB (@lem5452903) (@lem5452898)). Qed.
Lemma lem5452905 : term340 = term341.
Proof. exact (@lem1981613 term335 term260 term272 term272). Qed.
Lemma lem5452907 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5452908 : term344 = term345.
Proof. exact (@lem5452907 term120 term120). Qed.
Lemma lem5452909 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5452910 : term347 = term120.
Proof. exact (EQ_MP (@lem5452909) (@lem940073)). Qed.
Lemma lem5452911 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5452912 : term345 = term272.
Proof. exact (MK_COMB (@lem5452911) (@lem5452910)). Qed.
Lemma lem5452913 : term344 = term272.
Proof. exact (TRANS (@lem5452908) (@lem5452912)). Qed.
Lemma lem5452915 (x : nat) : (term348 x) = term260.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5452916 : term339 = term260.
Proof. exact (@lem5452915 term120). Qed.
Lemma lem5452917 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5452918 : term349 = term350.
Proof. exact (MK_COMB (@lem5452917) (@lem5452916)). Qed.
Lemma lem5452919 : term341 = term332.
Proof. exact (MK_COMB (@lem5452918) (@lem5452913)). Qed.
Lemma lem5452920 : term340 = term332.
Proof. exact (TRANS (@lem5452905) (@lem5452919)). Qed.
Lemma lem5452921 : term339 = term332.
Proof. exact (TRANS (@lem5452904) (@lem5452920)). Qed.
Lemma lem5452923 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5452924 : term332 = term260.
Proof. exact (@lem5452923 term260). Qed.
Lemma lem5452925 : term339 = term260.
Proof. exact (TRANS (@lem5452921) (@lem5452924)). Qed.
Lemma lem5452926 (_70533 : int) : (term273 _70533) = (term273 _70533).
Proof. exact (eq_refl (term273 _70533)). Qed.
Lemma lem5452927 (_70533 : int) : (term330 _70533) = (term352 _70533).
Proof. exact (MK_COMB (@lem5452926 _70533) (@lem5452925)). Qed.
Lemma lem5452928 (_70533 : int) : (term352 _70533) = (real_of_int _70533).
Proof. exact (@lem1982723 (real_of_int _70533)). Qed.
Lemma lem5452929 (_70533 : int) : (term330 _70533) = (real_of_int _70533).
Proof. exact (TRANS (@lem5452927 _70533) (@lem5452928 _70533)). Qed.
Lemma lem5452931 (_70533 : int) : (term329 _70533) = (real_of_int _70533).
Proof. exact (TRANS (@lem5452895 _70533) (@lem5452929 _70533)). Qed.
Lemma lem5452932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5452933 (_70533 : int) : (term353 _70533) = (term354 _70533).
Proof. exact (MK_COMB (@lem5452932) (@lem5452931 _70533)). Qed.
Lemma lem5452934 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5452935 (_70533 : int) : (term328 _70533) = (term355 _70533).
Proof. exact (MK_COMB (@lem5452933 _70533) (@lem5452934)). Qed.
Lemma lem5452936 (_70533 : int) : (term263 _70533) = (term355 _70533).
Proof. exact (TRANS (@lem5452889 _70533) (@lem5452935 _70533)). Qed.
Lemma lem5452937 (_70534 : int) : (term263 _70534) = (term328 _70534).
Proof. exact (@lem1988287 (real_of_int _70534) term260). Qed.
Lemma lem5452943 (_70534 : int) : (term329 _70534) = (term330 _70534).
Proof. exact (@lem1982792 (real_of_int _70534) term260). Qed.
Lemma lem5452945 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5452946 : term260 = term332.
Proof. exact (@lem5452945 (NUMERAL 0)). Qed.
Lemma lem5452948 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5452949 : term335 = term336.
Proof. exact (@lem5452948 term120). Qed.
Lemma lem5452950 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5452951 : term337 = term338.
Proof. exact (MK_COMB (@lem5452950) (@lem5452949)). Qed.
Lemma lem5452952 : term339 = term340.
Proof. exact (MK_COMB (@lem5452951) (@lem5452946)). Qed.
Lemma lem5452953 : term340 = term341.
Proof. exact (@lem1981613 term335 term260 term272 term272). Qed.
Lemma lem5452955 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5452956 : term344 = term345.
Proof. exact (@lem5452955 term120 term120). Qed.
Lemma lem5452957 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5452958 : term347 = term120.
Proof. exact (EQ_MP (@lem5452957) (@lem940073)). Qed.
Lemma lem5452959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5452960 : term345 = term272.
Proof. exact (MK_COMB (@lem5452959) (@lem5452958)). Qed.
Lemma lem5452961 : term344 = term272.
Proof. exact (TRANS (@lem5452956) (@lem5452960)). Qed.
Lemma lem5452963 (x : nat) : (term348 x) = term260.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5452964 : term339 = term260.
Proof. exact (@lem5452963 term120). Qed.
Lemma lem5452965 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5452966 : term349 = term350.
Proof. exact (MK_COMB (@lem5452965) (@lem5452964)). Qed.
Lemma lem5452967 : term341 = term332.
Proof. exact (MK_COMB (@lem5452966) (@lem5452961)). Qed.
Lemma lem5452968 : term340 = term332.
Proof. exact (TRANS (@lem5452953) (@lem5452967)). Qed.
Lemma lem5452969 : term339 = term332.
Proof. exact (TRANS (@lem5452952) (@lem5452968)). Qed.
Lemma lem5452971 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5452972 : term332 = term260.
Proof. exact (@lem5452971 term260). Qed.
Lemma lem5452973 : term339 = term260.
Proof. exact (TRANS (@lem5452969) (@lem5452972)). Qed.
Lemma lem5452974 (_70534 : int) : (term273 _70534) = (term273 _70534).
Proof. exact (eq_refl (term273 _70534)). Qed.
Lemma lem5452975 (_70534 : int) : (term330 _70534) = (term352 _70534).
Proof. exact (MK_COMB (@lem5452974 _70534) (@lem5452973)). Qed.
Lemma lem5452976 (_70534 : int) : (term352 _70534) = (real_of_int _70534).
Proof. exact (@lem1982723 (real_of_int _70534)). Qed.
Lemma lem5452977 (_70534 : int) : (term330 _70534) = (real_of_int _70534).
Proof. exact (TRANS (@lem5452975 _70534) (@lem5452976 _70534)). Qed.
Lemma lem5452979 (_70534 : int) : (term329 _70534) = (real_of_int _70534).
Proof. exact (TRANS (@lem5452943 _70534) (@lem5452977 _70534)). Qed.
Lemma lem5452980 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5452981 (_70534 : int) : (term353 _70534) = (term354 _70534).
Proof. exact (MK_COMB (@lem5452980) (@lem5452979 _70534)). Qed.
Lemma lem5452982 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5452983 (_70534 : int) : (term328 _70534) = (term355 _70534).
Proof. exact (MK_COMB (@lem5452981 _70534) (@lem5452982)). Qed.
Lemma lem5452984 (_70534 : int) : (term263 _70534) = (term355 _70534).
Proof. exact (TRANS (@lem5452937 _70534) (@lem5452983 _70534)). Qed.
Lemma lem5452985 (_70535 : int) : (term263 _70535) = (term328 _70535).
Proof. exact (@lem1988287 (real_of_int _70535) term260). Qed.
Lemma lem5452991 (_70535 : int) : (term329 _70535) = (term330 _70535).
Proof. exact (@lem1982792 (real_of_int _70535) term260). Qed.
Lemma lem5452993 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5452994 : term260 = term332.
Proof. exact (@lem5452993 (NUMERAL 0)). Qed.
Lemma lem5452996 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5452997 : term335 = term336.
Proof. exact (@lem5452996 term120). Qed.
Lemma lem5452998 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5452999 : term337 = term338.
Proof. exact (MK_COMB (@lem5452998) (@lem5452997)). Qed.
Lemma lem5453000 : term339 = term340.
Proof. exact (MK_COMB (@lem5452999) (@lem5452994)). Qed.
Lemma lem5453001 : term340 = term341.
Proof. exact (@lem1981613 term335 term260 term272 term272). Qed.
Lemma lem5453003 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453004 : term344 = term345.
Proof. exact (@lem5453003 term120 term120). Qed.
Lemma lem5453005 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453006 : term347 = term120.
Proof. exact (EQ_MP (@lem5453005) (@lem940073)). Qed.
Lemma lem5453007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453008 : term345 = term272.
Proof. exact (MK_COMB (@lem5453007) (@lem5453006)). Qed.
Lemma lem5453009 : term344 = term272.
Proof. exact (TRANS (@lem5453004) (@lem5453008)). Qed.
Lemma lem5453011 (x : nat) : (term348 x) = term260.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5453012 : term339 = term260.
Proof. exact (@lem5453011 term120). Qed.
Lemma lem5453013 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453014 : term349 = term350.
Proof. exact (MK_COMB (@lem5453013) (@lem5453012)). Qed.
Lemma lem5453015 : term341 = term332.
Proof. exact (MK_COMB (@lem5453014) (@lem5453009)). Qed.
Lemma lem5453016 : term340 = term332.
Proof. exact (TRANS (@lem5453001) (@lem5453015)). Qed.
Lemma lem5453017 : term339 = term332.
Proof. exact (TRANS (@lem5453000) (@lem5453016)). Qed.
Lemma lem5453019 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453020 : term332 = term260.
Proof. exact (@lem5453019 term260). Qed.
Lemma lem5453021 : term339 = term260.
Proof. exact (TRANS (@lem5453017) (@lem5453020)). Qed.
Lemma lem5453022 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5453023 (_70535 : int) : (term330 _70535) = (term352 _70535).
Proof. exact (MK_COMB (@lem5453022 _70535) (@lem5453021)). Qed.
Lemma lem5453024 (_70535 : int) : (term352 _70535) = (real_of_int _70535).
Proof. exact (@lem1982723 (real_of_int _70535)). Qed.
Lemma lem5453025 (_70535 : int) : (term330 _70535) = (real_of_int _70535).
Proof. exact (TRANS (@lem5453023 _70535) (@lem5453024 _70535)). Qed.
Lemma lem5453027 (_70535 : int) : (term329 _70535) = (real_of_int _70535).
Proof. exact (TRANS (@lem5452991 _70535) (@lem5453025 _70535)). Qed.
Lemma lem5453028 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453029 (_70535 : int) : (term353 _70535) = (term354 _70535).
Proof. exact (MK_COMB (@lem5453028) (@lem5453027 _70535)). Qed.
Lemma lem5453030 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453031 (_70535 : int) : (term328 _70535) = (term355 _70535).
Proof. exact (MK_COMB (@lem5453029 _70535) (@lem5453030)). Qed.
Lemma lem5453032 (_70535 : int) : (term263 _70535) = (term355 _70535).
Proof. exact (TRANS (@lem5452985 _70535) (@lem5453031 _70535)). Qed.
Lemma lem5453033 (_70533 : int) (_70532 : int) : (term276 _70532 _70533) = (term356 _70533 _70532).
Proof. exact (@lem1988287 (term274 _70533) (real_of_int _70532)). Qed.
Lemma lem5453045 (_70533 : int) (_70532 : int) : (term357 _70533 _70532) = (term358 _70533 _70532).
Proof. exact (@lem1982792 (term274 _70533) (real_of_int _70532)). Qed.
Lemma lem5453050 (_70532 : int) (_70533 : int) : (term358 _70533 _70532) = (term359 _70532 _70533).
Proof. exact (@lem1982761 (term360 _70532) (term274 _70533)). Qed.
Lemma lem5453052 (_70532 : int) (_70533 : int) : (term357 _70533 _70532) = (term359 _70532 _70533).
Proof. exact (TRANS (@lem5453045 _70533 _70532) (@lem5453050 _70532 _70533)). Qed.
Lemma lem5453053 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453054 (_70532 : int) (_70533 : int) : (term361 _70533 _70532) = (term362 _70532 _70533).
Proof. exact (MK_COMB (@lem5453053) (@lem5453052 _70532 _70533)). Qed.
Lemma lem5453055 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453056 (_70532 : int) (_70533 : int) : (term356 _70533 _70532) = (term363 _70532 _70533).
Proof. exact (MK_COMB (@lem5453054 _70532 _70533) (@lem5453055)). Qed.
Lemma lem5453057 (_70532 : int) (_70533 : int) : (term276 _70532 _70533) = (term363 _70532 _70533).
Proof. exact (TRANS (@lem5453033 _70533 _70532) (@lem5453056 _70532 _70533)). Qed.
Lemma lem5453058 (_70532 : int) (_70535 : int) : (term280 _70535 _70532) = (term364 _70532 _70535).
Proof. exact (@lem1988287 (real_of_int _70532) (term274 _70535)). Qed.
Lemma lem5453070 (_70532 : int) (_70535 : int) : (term365 _70532 _70535) = (term366 _70532 _70535).
Proof. exact (@lem1982792 (real_of_int _70532) (term274 _70535)). Qed.
Lemma lem5453071 (_70535 : int) : (term367 _70535) = (term368 _70535).
Proof. exact (@lem1982781 (real_of_int _70535) term335 term272). Qed.
Lemma lem5453073 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453074 : term272 = term369.
Proof. exact (@lem5453073 term120). Qed.
Lemma lem5453076 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453077 : term335 = term336.
Proof. exact (@lem5453076 term120). Qed.
Lemma lem5453078 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453079 : term337 = term338.
Proof. exact (MK_COMB (@lem5453078) (@lem5453077)). Qed.
Lemma lem5453080 : term370 = term371.
Proof. exact (MK_COMB (@lem5453079) (@lem5453074)). Qed.
Lemma lem5453081 : term371 = term372.
Proof. exact (@lem1981613 term335 term272 term272 term272). Qed.
Lemma lem5453083 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453084 : term344 = term345.
Proof. exact (@lem5453083 term120 term120). Qed.
Lemma lem5453085 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453086 : term347 = term120.
Proof. exact (EQ_MP (@lem5453085) (@lem940073)). Qed.
Lemma lem5453087 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453088 : term345 = term272.
Proof. exact (MK_COMB (@lem5453087) (@lem5453086)). Qed.
Lemma lem5453089 : term344 = term272.
Proof. exact (TRANS (@lem5453084) (@lem5453088)). Qed.
Lemma lem5453091 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453092 : term370 = term375.
Proof. exact (@lem5453091 term120 term120). Qed.
Lemma lem5453093 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453094 : term347 = term120.
Proof. exact (EQ_MP (@lem5453093) (@lem940073)). Qed.
Lemma lem5453095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453096 : term345 = term272.
Proof. exact (MK_COMB (@lem5453095) (@lem5453094)). Qed.
Lemma lem5453097 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453098 : term375 = term335.
Proof. exact (MK_COMB (@lem5453097) (@lem5453096)). Qed.
Lemma lem5453099 : term370 = term335.
Proof. exact (TRANS (@lem5453092) (@lem5453098)). Qed.
Lemma lem5453100 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453101 : term376 = term377.
Proof. exact (MK_COMB (@lem5453100) (@lem5453099)). Qed.
Lemma lem5453102 : term372 = term336.
Proof. exact (MK_COMB (@lem5453101) (@lem5453089)). Qed.
Lemma lem5453103 : term371 = term336.
Proof. exact (TRANS (@lem5453081) (@lem5453102)). Qed.
Lemma lem5453104 : term370 = term336.
Proof. exact (TRANS (@lem5453080) (@lem5453103)). Qed.
Lemma lem5453106 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453107 : term336 = term335.
Proof. exact (@lem5453106 term335). Qed.
Lemma lem5453108 : term370 = term335.
Proof. exact (TRANS (@lem5453104) (@lem5453107)). Qed.
Lemma lem5453111 (_70535 : int) : (term378 _70535) = (term378 _70535).
Proof. exact (eq_refl (term378 _70535)). Qed.
Lemma lem5453112 (_70535 : int) : (term368 _70535) = (term379 _70535).
Proof. exact (MK_COMB (@lem5453111 _70535) (@lem5453108)). Qed.
Lemma lem5453113 (_70535 : int) : (term367 _70535) = (term379 _70535).
Proof. exact (TRANS (@lem5453071 _70535) (@lem5453112 _70535)). Qed.
Lemma lem5453114 (_70532 : int) : (term273 _70532) = (term273 _70532).
Proof. exact (eq_refl (term273 _70532)). Qed.
Lemma lem5453117 (_70532 : int) (_70535 : int) : (term366 _70532 _70535) = (term380 _70532 _70535).
Proof. exact (MK_COMB (@lem5453114 _70532) (@lem5453113 _70535)). Qed.
Lemma lem5453119 (_70532 : int) (_70535 : int) : (term365 _70532 _70535) = (term380 _70532 _70535).
Proof. exact (TRANS (@lem5453070 _70532 _70535) (@lem5453117 _70532 _70535)). Qed.
Lemma lem5453120 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453121 (_70532 : int) (_70535 : int) : (term381 _70532 _70535) = (term382 _70532 _70535).
Proof. exact (MK_COMB (@lem5453120) (@lem5453119 _70532 _70535)). Qed.
Lemma lem5453122 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453123 (_70532 : int) (_70535 : int) : (term364 _70532 _70535) = (term383 _70532 _70535).
Proof. exact (MK_COMB (@lem5453121 _70532 _70535) (@lem5453122)). Qed.
Lemma lem5453124 (_70532 : int) (_70535 : int) : (term280 _70535 _70532) = (term383 _70532 _70535).
Proof. exact (TRANS (@lem5453058 _70532 _70535) (@lem5453123 _70532 _70535)). Qed.
Lemma lem5453125 (_70535 : int) (_70533 : int) (_70534 : int) : (term291 _70533 _70534 _70535) = (term384 _70535 _70533 _70534).
Proof. exact (@lem1988287 (real_of_int _70535) (term288 _70533 _70534)). Qed.
Lemma lem5453142 (_70533 : int) (_70534 : int) : (term288 _70533 _70534) = (term385 _70533 _70534).
Proof. exact (@lem1982755 (real_of_int _70533) (real_of_int _70534) term272). Qed.
Lemma lem5453145 (_70535 : int) : (term386 _70535) = (term386 _70535).
Proof. exact (eq_refl (term386 _70535)). Qed.
Lemma lem5453146 (_70535 : int) (_70533 : int) (_70534 : int) : (term387 _70535 _70533 _70534) = (term388 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5453145 _70535) (@lem5453142 _70533 _70534)). Qed.
Lemma lem5453147 (_70535 : int) (_70533 : int) (_70534 : int) : (term388 _70535 _70533 _70534) = (term389 _70535 _70533 _70534).
Proof. exact (@lem1982792 (real_of_int _70535) (term385 _70533 _70534)). Qed.
Lemma lem5453148 (_70533 : int) (_70534 : int) : (term390 _70533 _70534) = (term391 _70533 _70534).
Proof. exact (@lem1982781 (real_of_int _70533) term335 (term274 _70534)). Qed.
Lemma lem5453149 (_70534 : int) : (term367 _70534) = (term368 _70534).
Proof. exact (@lem1982781 (real_of_int _70534) term335 term272). Qed.
Lemma lem5453151 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453152 : term272 = term369.
Proof. exact (@lem5453151 term120). Qed.
Lemma lem5453154 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453155 : term335 = term336.
Proof. exact (@lem5453154 term120). Qed.
Lemma lem5453156 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453157 : term337 = term338.
Proof. exact (MK_COMB (@lem5453156) (@lem5453155)). Qed.
Lemma lem5453158 : term370 = term371.
Proof. exact (MK_COMB (@lem5453157) (@lem5453152)). Qed.
Lemma lem5453159 : term371 = term372.
Proof. exact (@lem1981613 term335 term272 term272 term272). Qed.
Lemma lem5453161 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453162 : term344 = term345.
Proof. exact (@lem5453161 term120 term120). Qed.
Lemma lem5453163 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453164 : term347 = term120.
Proof. exact (EQ_MP (@lem5453163) (@lem940073)). Qed.
Lemma lem5453165 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453166 : term345 = term272.
Proof. exact (MK_COMB (@lem5453165) (@lem5453164)). Qed.
Lemma lem5453167 : term344 = term272.
Proof. exact (TRANS (@lem5453162) (@lem5453166)). Qed.
Lemma lem5453169 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453170 : term370 = term375.
Proof. exact (@lem5453169 term120 term120). Qed.
Lemma lem5453171 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453172 : term347 = term120.
Proof. exact (EQ_MP (@lem5453171) (@lem940073)). Qed.
Lemma lem5453173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453174 : term345 = term272.
Proof. exact (MK_COMB (@lem5453173) (@lem5453172)). Qed.
Lemma lem5453175 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453176 : term375 = term335.
Proof. exact (MK_COMB (@lem5453175) (@lem5453174)). Qed.
Lemma lem5453177 : term370 = term335.
Proof. exact (TRANS (@lem5453170) (@lem5453176)). Qed.
Lemma lem5453178 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453179 : term376 = term377.
Proof. exact (MK_COMB (@lem5453178) (@lem5453177)). Qed.
Lemma lem5453180 : term372 = term336.
Proof. exact (MK_COMB (@lem5453179) (@lem5453167)). Qed.
Lemma lem5453181 : term371 = term336.
Proof. exact (TRANS (@lem5453159) (@lem5453180)). Qed.
Lemma lem5453182 : term370 = term336.
Proof. exact (TRANS (@lem5453158) (@lem5453181)). Qed.
Lemma lem5453184 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453185 : term336 = term335.
Proof. exact (@lem5453184 term335). Qed.
Lemma lem5453186 : term370 = term335.
Proof. exact (TRANS (@lem5453182) (@lem5453185)). Qed.
Lemma lem5453189 (_70534 : int) : (term378 _70534) = (term378 _70534).
Proof. exact (eq_refl (term378 _70534)). Qed.
Lemma lem5453190 (_70534 : int) : (term368 _70534) = (term379 _70534).
Proof. exact (MK_COMB (@lem5453189 _70534) (@lem5453186)). Qed.
Lemma lem5453191 (_70534 : int) : (term367 _70534) = (term379 _70534).
Proof. exact (TRANS (@lem5453149 _70534) (@lem5453190 _70534)). Qed.
Lemma lem5453194 (_70533 : int) : (term378 _70533) = (term378 _70533).
Proof. exact (eq_refl (term378 _70533)). Qed.
Lemma lem5453195 (_70533 : int) (_70534 : int) : (term391 _70533 _70534) = (term392 _70533 _70534).
Proof. exact (MK_COMB (@lem5453194 _70533) (@lem5453191 _70534)). Qed.
Lemma lem5453196 (_70533 : int) (_70534 : int) : (term390 _70533 _70534) = (term392 _70533 _70534).
Proof. exact (TRANS (@lem5453148 _70533 _70534) (@lem5453195 _70533 _70534)). Qed.
Lemma lem5453197 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5453198 (_70535 : int) (_70533 : int) (_70534 : int) : (term389 _70535 _70533 _70534) = (term393 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5453197 _70535) (@lem5453196 _70533 _70534)). Qed.
Lemma lem5453199 (_70533 : int) (_70535 : int) (_70534 : int) : (term393 _70535 _70533 _70534) = (term394 _70533 _70535 _70534).
Proof. exact (@lem1982757 (term360 _70533) (real_of_int _70535) (term379 _70534)). Qed.
Lemma lem5453204 (_70534 : int) (_70535 : int) : (term380 _70535 _70534) = (term395 _70534 _70535).
Proof. exact (@lem1982757 (term360 _70534) (real_of_int _70535) term335). Qed.
Lemma lem5453205 (_70533 : int) : (term378 _70533) = (term378 _70533).
Proof. exact (eq_refl (term378 _70533)). Qed.
Lemma lem5453206 (_70533 : int) (_70534 : int) (_70535 : int) : (term394 _70533 _70535 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453205 _70533) (@lem5453204 _70534 _70535)). Qed.
Lemma lem5453207 (_70533 : int) (_70534 : int) (_70535 : int) : (term393 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453199 _70533 _70535 _70534) (@lem5453206 _70533 _70534 _70535)). Qed.
Lemma lem5453208 (_70533 : int) (_70534 : int) (_70535 : int) : (term389 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453198 _70535 _70533 _70534) (@lem5453207 _70533 _70534 _70535)). Qed.
Lemma lem5453209 (_70533 : int) (_70534 : int) (_70535 : int) : (term388 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453147 _70535 _70533 _70534) (@lem5453208 _70533 _70534 _70535)). Qed.
Lemma lem5453210 (_70533 : int) (_70534 : int) (_70535 : int) : (term387 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453146 _70535 _70533 _70534) (@lem5453209 _70533 _70534 _70535)). Qed.
Lemma lem5453211 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453212 (_70533 : int) (_70534 : int) (_70535 : int) : (term397 _70535 _70533 _70534) = (term398 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453211) (@lem5453210 _70533 _70534 _70535)). Qed.
Lemma lem5453213 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453214 (_70533 : int) (_70534 : int) (_70535 : int) : (term384 _70535 _70533 _70534) = (term399 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453212 _70533 _70534 _70535) (@lem5453213)). Qed.
Lemma lem5453215 (_70533 : int) (_70534 : int) (_70535 : int) : (term291 _70533 _70534 _70535) = (term399 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453125 _70535 _70533 _70534) (@lem5453214 _70533 _70534 _70535)). Qed.
Lemma lem5453216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453217 (_70532 : int) (_70535 : int) : (term293 _70535 _70532) = (term400 _70532 _70535).
Proof. exact (MK_COMB (@lem5453216) (@lem5453124 _70532 _70535)). Qed.
Lemma lem5453218 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term294 _70532 _70533 _70534 _70535) = (term401 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453217 _70532 _70535) (@lem5453215 _70533 _70534 _70535)). Qed.
Lemma lem5453219 (_70535 : int) (_70532 : int) : (term255 _70532 _70535) = (term402 _70535 _70532).
Proof. exact (@lem1988287 (real_of_int _70535) (real_of_int _70532)). Qed.
Lemma lem5453225 (_70535 : int) (_70532 : int) : (term403 _70535 _70532) = (term404 _70535 _70532).
Proof. exact (@lem1982792 (real_of_int _70535) (real_of_int _70532)). Qed.
Lemma lem5453230 (_70532 : int) (_70535 : int) : (term404 _70535 _70532) = (term405 _70532 _70535).
Proof. exact (@lem1982761 (term360 _70532) (real_of_int _70535)). Qed.
Lemma lem5453232 (_70532 : int) (_70535 : int) : (term403 _70535 _70532) = (term405 _70532 _70535).
Proof. exact (TRANS (@lem5453225 _70535 _70532) (@lem5453230 _70532 _70535)). Qed.
Lemma lem5453233 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453234 (_70532 : int) (_70535 : int) : (term406 _70535 _70532) = (term407 _70532 _70535).
Proof. exact (MK_COMB (@lem5453233) (@lem5453232 _70532 _70535)). Qed.
Lemma lem5453235 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453236 (_70532 : int) (_70535 : int) : (term402 _70535 _70532) = (term408 _70532 _70535).
Proof. exact (MK_COMB (@lem5453234 _70532 _70535) (@lem5453235)). Qed.
Lemma lem5453237 (_70532 : int) (_70535 : int) : (term255 _70532 _70535) = (term408 _70532 _70535).
Proof. exact (TRANS (@lem5453219 _70535 _70532) (@lem5453236 _70532 _70535)). Qed.
Lemma lem5453238 (_70533 : int) (_70535 : int) : (term255 _70535 _70533) = (term402 _70533 _70535).
Proof. exact (@lem1988287 (real_of_int _70533) (real_of_int _70535)). Qed.
Lemma lem5453251 (_70533 : int) (_70535 : int) : (term403 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (@lem1982792 (real_of_int _70533) (real_of_int _70535)). Qed.
Lemma lem5453252 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453253 (_70533 : int) (_70535 : int) : (term406 _70533 _70535) = (term409 _70533 _70535).
Proof. exact (MK_COMB (@lem5453252) (@lem5453251 _70533 _70535)). Qed.
Lemma lem5453254 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453255 (_70533 : int) (_70535 : int) : (term402 _70533 _70535) = (term410 _70533 _70535).
Proof. exact (MK_COMB (@lem5453253 _70533 _70535) (@lem5453254)). Qed.
Lemma lem5453256 (_70533 : int) (_70535 : int) : (term255 _70535 _70533) = (term410 _70533 _70535).
Proof. exact (TRANS (@lem5453238 _70533 _70535) (@lem5453255 _70533 _70535)). Qed.
Lemma lem5453257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453258 (_70532 : int) (_70535 : int) : (term295 _70532 _70535) = (term411 _70532 _70535).
Proof. exact (MK_COMB (@lem5453257) (@lem5453237 _70532 _70535)). Qed.
Lemma lem5453259 (_70532 : int) (_70533 : int) (_70535 : int) : (term296 _70532 _70535 _70533) = (term412 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5453258 _70532 _70535) (@lem5453256 _70533 _70535)). Qed.
Lemma lem5453260 (_70535 : int) (_70533 : int) : (term280 _70533 _70535) = (term364 _70535 _70533).
Proof. exact (@lem1988287 (real_of_int _70535) (term274 _70533)). Qed.
Lemma lem5453272 (_70535 : int) (_70533 : int) : (term365 _70535 _70533) = (term366 _70535 _70533).
Proof. exact (@lem1982792 (real_of_int _70535) (term274 _70533)). Qed.
Lemma lem5453273 (_70533 : int) : (term367 _70533) = (term368 _70533).
Proof. exact (@lem1982781 (real_of_int _70533) term335 term272). Qed.
Lemma lem5453275 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453276 : term272 = term369.
Proof. exact (@lem5453275 term120). Qed.
Lemma lem5453278 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453279 : term335 = term336.
Proof. exact (@lem5453278 term120). Qed.
Lemma lem5453280 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453281 : term337 = term338.
Proof. exact (MK_COMB (@lem5453280) (@lem5453279)). Qed.
Lemma lem5453282 : term370 = term371.
Proof. exact (MK_COMB (@lem5453281) (@lem5453276)). Qed.
Lemma lem5453283 : term371 = term372.
Proof. exact (@lem1981613 term335 term272 term272 term272). Qed.
Lemma lem5453285 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453286 : term344 = term345.
Proof. exact (@lem5453285 term120 term120). Qed.
Lemma lem5453287 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453288 : term347 = term120.
Proof. exact (EQ_MP (@lem5453287) (@lem940073)). Qed.
Lemma lem5453289 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453290 : term345 = term272.
Proof. exact (MK_COMB (@lem5453289) (@lem5453288)). Qed.
Lemma lem5453291 : term344 = term272.
Proof. exact (TRANS (@lem5453286) (@lem5453290)). Qed.
Lemma lem5453293 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453294 : term370 = term375.
Proof. exact (@lem5453293 term120 term120). Qed.
Lemma lem5453295 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453296 : term347 = term120.
Proof. exact (EQ_MP (@lem5453295) (@lem940073)). Qed.
Lemma lem5453297 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453298 : term345 = term272.
Proof. exact (MK_COMB (@lem5453297) (@lem5453296)). Qed.
Lemma lem5453299 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453300 : term375 = term335.
Proof. exact (MK_COMB (@lem5453299) (@lem5453298)). Qed.
Lemma lem5453301 : term370 = term335.
Proof. exact (TRANS (@lem5453294) (@lem5453300)). Qed.
Lemma lem5453302 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453303 : term376 = term377.
Proof. exact (MK_COMB (@lem5453302) (@lem5453301)). Qed.
Lemma lem5453304 : term372 = term336.
Proof. exact (MK_COMB (@lem5453303) (@lem5453291)). Qed.
Lemma lem5453305 : term371 = term336.
Proof. exact (TRANS (@lem5453283) (@lem5453304)). Qed.
Lemma lem5453306 : term370 = term336.
Proof. exact (TRANS (@lem5453282) (@lem5453305)). Qed.
Lemma lem5453308 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453309 : term336 = term335.
Proof. exact (@lem5453308 term335). Qed.
Lemma lem5453310 : term370 = term335.
Proof. exact (TRANS (@lem5453306) (@lem5453309)). Qed.
Lemma lem5453313 (_70533 : int) : (term378 _70533) = (term378 _70533).
Proof. exact (eq_refl (term378 _70533)). Qed.
Lemma lem5453314 (_70533 : int) : (term368 _70533) = (term379 _70533).
Proof. exact (MK_COMB (@lem5453313 _70533) (@lem5453310)). Qed.
Lemma lem5453315 (_70533 : int) : (term367 _70533) = (term379 _70533).
Proof. exact (TRANS (@lem5453273 _70533) (@lem5453314 _70533)). Qed.
Lemma lem5453316 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5453317 (_70535 : int) (_70533 : int) : (term366 _70535 _70533) = (term380 _70535 _70533).
Proof. exact (MK_COMB (@lem5453316 _70535) (@lem5453315 _70533)). Qed.
Lemma lem5453322 (_70533 : int) (_70535 : int) : (term380 _70535 _70533) = (term395 _70533 _70535).
Proof. exact (@lem1982757 (term360 _70533) (real_of_int _70535) term335). Qed.
Lemma lem5453323 (_70533 : int) (_70535 : int) : (term366 _70535 _70533) = (term395 _70533 _70535).
Proof. exact (TRANS (@lem5453317 _70535 _70533) (@lem5453322 _70533 _70535)). Qed.
Lemma lem5453325 (_70533 : int) (_70535 : int) : (term365 _70535 _70533) = (term395 _70533 _70535).
Proof. exact (TRANS (@lem5453272 _70535 _70533) (@lem5453323 _70533 _70535)). Qed.
Lemma lem5453326 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453327 (_70533 : int) (_70535 : int) : (term381 _70535 _70533) = (term413 _70533 _70535).
Proof. exact (MK_COMB (@lem5453326) (@lem5453325 _70533 _70535)). Qed.
Lemma lem5453328 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453329 (_70533 : int) (_70535 : int) : (term364 _70535 _70533) = (term414 _70533 _70535).
Proof. exact (MK_COMB (@lem5453327 _70533 _70535) (@lem5453328)). Qed.
Lemma lem5453330 (_70533 : int) (_70535 : int) : (term280 _70533 _70535) = (term414 _70533 _70535).
Proof. exact (TRANS (@lem5453260 _70535 _70533) (@lem5453329 _70533 _70535)). Qed.
Lemma lem5453331 (_70533 : int) (_70534 : int) (_70535 : int) : (term298 _70535 _70533 _70534) = (term415 _70533 _70534 _70535).
Proof. exact (@lem1988287 (term267 _70533 _70534) (real_of_int _70535)). Qed.
Lemma lem5453343 (_70533 : int) (_70534 : int) (_70535 : int) : (term416 _70533 _70534 _70535) = (term417 _70533 _70534 _70535).
Proof. exact (@lem1982792 (term267 _70533 _70534) (real_of_int _70535)). Qed.
Lemma lem5453352 (_70533 : int) (_70534 : int) (_70535 : int) : (term417 _70533 _70534 _70535) = (term418 _70533 _70534 _70535).
Proof. exact (@lem1982755 (real_of_int _70533) (real_of_int _70534) (term360 _70535)). Qed.
Lemma lem5453354 (_70533 : int) (_70534 : int) (_70535 : int) : (term416 _70533 _70534 _70535) = (term418 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453343 _70533 _70534 _70535) (@lem5453352 _70533 _70534 _70535)). Qed.
Lemma lem5453355 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453356 (_70533 : int) (_70534 : int) (_70535 : int) : (term419 _70533 _70534 _70535) = (term420 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453355) (@lem5453354 _70533 _70534 _70535)). Qed.
Lemma lem5453357 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453358 (_70533 : int) (_70534 : int) (_70535 : int) : (term415 _70533 _70534 _70535) = (term421 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453356 _70533 _70534 _70535) (@lem5453357)). Qed.
Lemma lem5453359 (_70533 : int) (_70534 : int) (_70535 : int) : (term298 _70535 _70533 _70534) = (term421 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453331 _70533 _70534 _70535) (@lem5453358 _70533 _70534 _70535)). Qed.
Lemma lem5453360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453361 (_70533 : int) (_70535 : int) : (term299 _70533 _70535) = (term422 _70533 _70535).
Proof. exact (MK_COMB (@lem5453360) (@lem5453330 _70533 _70535)). Qed.
Lemma lem5453362 (_70533 : int) (_70534 : int) (_70535 : int) : (term300 _70535 _70533 _70534) = (term423 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453361 _70533 _70535) (@lem5453359 _70533 _70534 _70535)). Qed.
Lemma lem5453363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453364 (_70532 : int) (_70533 : int) (_70535 : int) : (term301 _70532 _70535 _70533) = (term424 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5453363) (@lem5453259 _70532 _70533 _70535)). Qed.
Lemma lem5453365 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term302 _70532 _70535 _70533 _70534) = (term425 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453364 _70532 _70533 _70535) (@lem5453362 _70533 _70534 _70535)). Qed.
Lemma lem5453366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453367 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term303 _70532 _70533 _70534 _70535) = (term426 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453366) (@lem5453218 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453368 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term304 _70532 _70535 _70533 _70534) = (term427 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453367 _70532 _70533 _70534 _70535) (@lem5453365 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453369 (_70535 : int) (_70532 : int) : (term255 _70532 _70535) = (term402 _70535 _70532).
Proof. exact (@lem1988287 (real_of_int _70535) (real_of_int _70532)). Qed.
Lemma lem5453375 (_70535 : int) (_70532 : int) : (term403 _70535 _70532) = (term404 _70535 _70532).
Proof. exact (@lem1982792 (real_of_int _70535) (real_of_int _70532)). Qed.
Lemma lem5453380 (_70532 : int) (_70535 : int) : (term404 _70535 _70532) = (term405 _70532 _70535).
Proof. exact (@lem1982761 (term360 _70532) (real_of_int _70535)). Qed.
Lemma lem5453382 (_70532 : int) (_70535 : int) : (term403 _70535 _70532) = (term405 _70532 _70535).
Proof. exact (TRANS (@lem5453375 _70535 _70532) (@lem5453380 _70532 _70535)). Qed.
Lemma lem5453383 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453384 (_70532 : int) (_70535 : int) : (term406 _70535 _70532) = (term407 _70532 _70535).
Proof. exact (MK_COMB (@lem5453383) (@lem5453382 _70532 _70535)). Qed.
Lemma lem5453385 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453386 (_70532 : int) (_70535 : int) : (term402 _70535 _70532) = (term408 _70532 _70535).
Proof. exact (MK_COMB (@lem5453384 _70532 _70535) (@lem5453385)). Qed.
Lemma lem5453387 (_70532 : int) (_70535 : int) : (term255 _70532 _70535) = (term408 _70532 _70535).
Proof. exact (TRANS (@lem5453369 _70535 _70532) (@lem5453386 _70532 _70535)). Qed.
Lemma lem5453388 (_70533 : int) (_70534 : int) (_70535 : int) : (term298 _70535 _70533 _70534) = (term415 _70533 _70534 _70535).
Proof. exact (@lem1988287 (term267 _70533 _70534) (real_of_int _70535)). Qed.
Lemma lem5453400 (_70533 : int) (_70534 : int) (_70535 : int) : (term416 _70533 _70534 _70535) = (term417 _70533 _70534 _70535).
Proof. exact (@lem1982792 (term267 _70533 _70534) (real_of_int _70535)). Qed.
Lemma lem5453409 (_70533 : int) (_70534 : int) (_70535 : int) : (term417 _70533 _70534 _70535) = (term418 _70533 _70534 _70535).
Proof. exact (@lem1982755 (real_of_int _70533) (real_of_int _70534) (term360 _70535)). Qed.
Lemma lem5453411 (_70533 : int) (_70534 : int) (_70535 : int) : (term416 _70533 _70534 _70535) = (term418 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453400 _70533 _70534 _70535) (@lem5453409 _70533 _70534 _70535)). Qed.
Lemma lem5453412 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453413 (_70533 : int) (_70534 : int) (_70535 : int) : (term419 _70533 _70534 _70535) = (term420 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453412) (@lem5453411 _70533 _70534 _70535)). Qed.
Lemma lem5453414 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453415 (_70533 : int) (_70534 : int) (_70535 : int) : (term415 _70533 _70534 _70535) = (term421 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453413 _70533 _70534 _70535) (@lem5453414)). Qed.
Lemma lem5453416 (_70533 : int) (_70534 : int) (_70535 : int) : (term298 _70535 _70533 _70534) = (term421 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453388 _70533 _70534 _70535) (@lem5453415 _70533 _70534 _70535)). Qed.
Lemma lem5453417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453418 (_70532 : int) (_70535 : int) : (term295 _70532 _70535) = (term411 _70532 _70535).
Proof. exact (MK_COMB (@lem5453417) (@lem5453387 _70532 _70535)). Qed.
Lemma lem5453419 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term305 _70532 _70535 _70533 _70534) = (term428 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453418 _70532 _70535) (@lem5453416 _70533 _70534 _70535)). Qed.
Lemma lem5453420 (_70532 : int) (_70535 : int) : (term280 _70535 _70532) = (term364 _70532 _70535).
Proof. exact (@lem1988287 (real_of_int _70532) (term274 _70535)). Qed.
Lemma lem5453432 (_70532 : int) (_70535 : int) : (term365 _70532 _70535) = (term366 _70532 _70535).
Proof. exact (@lem1982792 (real_of_int _70532) (term274 _70535)). Qed.
Lemma lem5453433 (_70535 : int) : (term367 _70535) = (term368 _70535).
Proof. exact (@lem1982781 (real_of_int _70535) term335 term272). Qed.
Lemma lem5453435 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453436 : term272 = term369.
Proof. exact (@lem5453435 term120). Qed.
Lemma lem5453438 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453439 : term335 = term336.
Proof. exact (@lem5453438 term120). Qed.
Lemma lem5453440 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453441 : term337 = term338.
Proof. exact (MK_COMB (@lem5453440) (@lem5453439)). Qed.
Lemma lem5453442 : term370 = term371.
Proof. exact (MK_COMB (@lem5453441) (@lem5453436)). Qed.
Lemma lem5453443 : term371 = term372.
Proof. exact (@lem1981613 term335 term272 term272 term272). Qed.
Lemma lem5453445 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453446 : term344 = term345.
Proof. exact (@lem5453445 term120 term120). Qed.
Lemma lem5453447 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453448 : term347 = term120.
Proof. exact (EQ_MP (@lem5453447) (@lem940073)). Qed.
Lemma lem5453449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453450 : term345 = term272.
Proof. exact (MK_COMB (@lem5453449) (@lem5453448)). Qed.
Lemma lem5453451 : term344 = term272.
Proof. exact (TRANS (@lem5453446) (@lem5453450)). Qed.
Lemma lem5453453 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453454 : term370 = term375.
Proof. exact (@lem5453453 term120 term120). Qed.
Lemma lem5453455 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453456 : term347 = term120.
Proof. exact (EQ_MP (@lem5453455) (@lem940073)). Qed.
Lemma lem5453457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453458 : term345 = term272.
Proof. exact (MK_COMB (@lem5453457) (@lem5453456)). Qed.
Lemma lem5453459 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453460 : term375 = term335.
Proof. exact (MK_COMB (@lem5453459) (@lem5453458)). Qed.
Lemma lem5453461 : term370 = term335.
Proof. exact (TRANS (@lem5453454) (@lem5453460)). Qed.
Lemma lem5453462 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453463 : term376 = term377.
Proof. exact (MK_COMB (@lem5453462) (@lem5453461)). Qed.
Lemma lem5453464 : term372 = term336.
Proof. exact (MK_COMB (@lem5453463) (@lem5453451)). Qed.
Lemma lem5453465 : term371 = term336.
Proof. exact (TRANS (@lem5453443) (@lem5453464)). Qed.
Lemma lem5453466 : term370 = term336.
Proof. exact (TRANS (@lem5453442) (@lem5453465)). Qed.
Lemma lem5453468 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453469 : term336 = term335.
Proof. exact (@lem5453468 term335). Qed.
Lemma lem5453470 : term370 = term335.
Proof. exact (TRANS (@lem5453466) (@lem5453469)). Qed.
Lemma lem5453473 (_70535 : int) : (term378 _70535) = (term378 _70535).
Proof. exact (eq_refl (term378 _70535)). Qed.
Lemma lem5453474 (_70535 : int) : (term368 _70535) = (term379 _70535).
Proof. exact (MK_COMB (@lem5453473 _70535) (@lem5453470)). Qed.
Lemma lem5453475 (_70535 : int) : (term367 _70535) = (term379 _70535).
Proof. exact (TRANS (@lem5453433 _70535) (@lem5453474 _70535)). Qed.
Lemma lem5453476 (_70532 : int) : (term273 _70532) = (term273 _70532).
Proof. exact (eq_refl (term273 _70532)). Qed.
Lemma lem5453479 (_70532 : int) (_70535 : int) : (term366 _70532 _70535) = (term380 _70532 _70535).
Proof. exact (MK_COMB (@lem5453476 _70532) (@lem5453475 _70535)). Qed.
Lemma lem5453481 (_70532 : int) (_70535 : int) : (term365 _70532 _70535) = (term380 _70532 _70535).
Proof. exact (TRANS (@lem5453432 _70532 _70535) (@lem5453479 _70532 _70535)). Qed.
Lemma lem5453482 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453483 (_70532 : int) (_70535 : int) : (term381 _70532 _70535) = (term382 _70532 _70535).
Proof. exact (MK_COMB (@lem5453482) (@lem5453481 _70532 _70535)). Qed.
Lemma lem5453484 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453485 (_70532 : int) (_70535 : int) : (term364 _70532 _70535) = (term383 _70532 _70535).
Proof. exact (MK_COMB (@lem5453483 _70532 _70535) (@lem5453484)). Qed.
Lemma lem5453486 (_70532 : int) (_70535 : int) : (term280 _70535 _70532) = (term383 _70532 _70535).
Proof. exact (TRANS (@lem5453420 _70532 _70535) (@lem5453485 _70532 _70535)). Qed.
Lemma lem5453487 (_70535 : int) (_70533 : int) : (term280 _70533 _70535) = (term364 _70535 _70533).
Proof. exact (@lem1988287 (real_of_int _70535) (term274 _70533)). Qed.
Lemma lem5453499 (_70535 : int) (_70533 : int) : (term365 _70535 _70533) = (term366 _70535 _70533).
Proof. exact (@lem1982792 (real_of_int _70535) (term274 _70533)). Qed.
Lemma lem5453500 (_70533 : int) : (term367 _70533) = (term368 _70533).
Proof. exact (@lem1982781 (real_of_int _70533) term335 term272). Qed.
Lemma lem5453502 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453503 : term272 = term369.
Proof. exact (@lem5453502 term120). Qed.
Lemma lem5453505 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453506 : term335 = term336.
Proof. exact (@lem5453505 term120). Qed.
Lemma lem5453507 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453508 : term337 = term338.
Proof. exact (MK_COMB (@lem5453507) (@lem5453506)). Qed.
Lemma lem5453509 : term370 = term371.
Proof. exact (MK_COMB (@lem5453508) (@lem5453503)). Qed.
Lemma lem5453510 : term371 = term372.
Proof. exact (@lem1981613 term335 term272 term272 term272). Qed.
Lemma lem5453512 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453513 : term344 = term345.
Proof. exact (@lem5453512 term120 term120). Qed.
Lemma lem5453514 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453515 : term347 = term120.
Proof. exact (EQ_MP (@lem5453514) (@lem940073)). Qed.
Lemma lem5453516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453517 : term345 = term272.
Proof. exact (MK_COMB (@lem5453516) (@lem5453515)). Qed.
Lemma lem5453518 : term344 = term272.
Proof. exact (TRANS (@lem5453513) (@lem5453517)). Qed.
Lemma lem5453520 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453521 : term370 = term375.
Proof. exact (@lem5453520 term120 term120). Qed.
Lemma lem5453522 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453523 : term347 = term120.
Proof. exact (EQ_MP (@lem5453522) (@lem940073)). Qed.
Lemma lem5453524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453525 : term345 = term272.
Proof. exact (MK_COMB (@lem5453524) (@lem5453523)). Qed.
Lemma lem5453526 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453527 : term375 = term335.
Proof. exact (MK_COMB (@lem5453526) (@lem5453525)). Qed.
Lemma lem5453528 : term370 = term335.
Proof. exact (TRANS (@lem5453521) (@lem5453527)). Qed.
Lemma lem5453529 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453530 : term376 = term377.
Proof. exact (MK_COMB (@lem5453529) (@lem5453528)). Qed.
Lemma lem5453531 : term372 = term336.
Proof. exact (MK_COMB (@lem5453530) (@lem5453518)). Qed.
Lemma lem5453532 : term371 = term336.
Proof. exact (TRANS (@lem5453510) (@lem5453531)). Qed.
Lemma lem5453533 : term370 = term336.
Proof. exact (TRANS (@lem5453509) (@lem5453532)). Qed.
Lemma lem5453535 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453536 : term336 = term335.
Proof. exact (@lem5453535 term335). Qed.
Lemma lem5453537 : term370 = term335.
Proof. exact (TRANS (@lem5453533) (@lem5453536)). Qed.
Lemma lem5453540 (_70533 : int) : (term378 _70533) = (term378 _70533).
Proof. exact (eq_refl (term378 _70533)). Qed.
Lemma lem5453541 (_70533 : int) : (term368 _70533) = (term379 _70533).
Proof. exact (MK_COMB (@lem5453540 _70533) (@lem5453537)). Qed.
Lemma lem5453542 (_70533 : int) : (term367 _70533) = (term379 _70533).
Proof. exact (TRANS (@lem5453500 _70533) (@lem5453541 _70533)). Qed.
Lemma lem5453543 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5453544 (_70535 : int) (_70533 : int) : (term366 _70535 _70533) = (term380 _70535 _70533).
Proof. exact (MK_COMB (@lem5453543 _70535) (@lem5453542 _70533)). Qed.
Lemma lem5453549 (_70533 : int) (_70535 : int) : (term380 _70535 _70533) = (term395 _70533 _70535).
Proof. exact (@lem1982757 (term360 _70533) (real_of_int _70535) term335). Qed.
Lemma lem5453550 (_70533 : int) (_70535 : int) : (term366 _70535 _70533) = (term395 _70533 _70535).
Proof. exact (TRANS (@lem5453544 _70535 _70533) (@lem5453549 _70533 _70535)). Qed.
Lemma lem5453552 (_70533 : int) (_70535 : int) : (term365 _70535 _70533) = (term395 _70533 _70535).
Proof. exact (TRANS (@lem5453499 _70535 _70533) (@lem5453550 _70533 _70535)). Qed.
Lemma lem5453553 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453554 (_70533 : int) (_70535 : int) : (term381 _70535 _70533) = (term413 _70533 _70535).
Proof. exact (MK_COMB (@lem5453553) (@lem5453552 _70533 _70535)). Qed.
Lemma lem5453555 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453556 (_70533 : int) (_70535 : int) : (term364 _70535 _70533) = (term414 _70533 _70535).
Proof. exact (MK_COMB (@lem5453554 _70533 _70535) (@lem5453555)). Qed.
Lemma lem5453557 (_70533 : int) (_70535 : int) : (term280 _70533 _70535) = (term414 _70533 _70535).
Proof. exact (TRANS (@lem5453487 _70535 _70533) (@lem5453556 _70533 _70535)). Qed.
Lemma lem5453558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453559 (_70532 : int) (_70535 : int) : (term293 _70535 _70532) = (term400 _70532 _70535).
Proof. exact (MK_COMB (@lem5453558) (@lem5453486 _70532 _70535)). Qed.
Lemma lem5453560 (_70532 : int) (_70533 : int) (_70535 : int) : (term306 _70532 _70533 _70535) = (term429 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5453559 _70532 _70535) (@lem5453557 _70533 _70535)). Qed.
Lemma lem5453561 (_70533 : int) (_70535 : int) : (term309 _70535 _70533) = (term430 _70533 _70535).
Proof. exact (@lem1988287 (term274 _70533) (term274 _70535)). Qed.
Lemma lem5453579 (_70533 : int) (_70535 : int) : (term431 _70533 _70535) = (term432 _70533 _70535).
Proof. exact (@lem1982792 (term274 _70533) (term274 _70535)). Qed.
Lemma lem5453580 (_70535 : int) : (term367 _70535) = (term368 _70535).
Proof. exact (@lem1982781 (real_of_int _70535) term335 term272). Qed.
Lemma lem5453582 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453583 : term272 = term369.
Proof. exact (@lem5453582 term120). Qed.
Lemma lem5453585 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453586 : term335 = term336.
Proof. exact (@lem5453585 term120). Qed.
Lemma lem5453587 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453588 : term337 = term338.
Proof. exact (MK_COMB (@lem5453587) (@lem5453586)). Qed.
Lemma lem5453589 : term370 = term371.
Proof. exact (MK_COMB (@lem5453588) (@lem5453583)). Qed.
Lemma lem5453590 : term371 = term372.
Proof. exact (@lem1981613 term335 term272 term272 term272). Qed.
Lemma lem5453592 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453593 : term344 = term345.
Proof. exact (@lem5453592 term120 term120). Qed.
Lemma lem5453594 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453595 : term347 = term120.
Proof. exact (EQ_MP (@lem5453594) (@lem940073)). Qed.
Lemma lem5453596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453597 : term345 = term272.
Proof. exact (MK_COMB (@lem5453596) (@lem5453595)). Qed.
Lemma lem5453598 : term344 = term272.
Proof. exact (TRANS (@lem5453593) (@lem5453597)). Qed.
Lemma lem5453600 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453601 : term370 = term375.
Proof. exact (@lem5453600 term120 term120). Qed.
Lemma lem5453602 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453603 : term347 = term120.
Proof. exact (EQ_MP (@lem5453602) (@lem940073)). Qed.
Lemma lem5453604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453605 : term345 = term272.
Proof. exact (MK_COMB (@lem5453604) (@lem5453603)). Qed.
Lemma lem5453606 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453607 : term375 = term335.
Proof. exact (MK_COMB (@lem5453606) (@lem5453605)). Qed.
Lemma lem5453608 : term370 = term335.
Proof. exact (TRANS (@lem5453601) (@lem5453607)). Qed.
Lemma lem5453609 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453610 : term376 = term377.
Proof. exact (MK_COMB (@lem5453609) (@lem5453608)). Qed.
Lemma lem5453611 : term372 = term336.
Proof. exact (MK_COMB (@lem5453610) (@lem5453598)). Qed.
Lemma lem5453612 : term371 = term336.
Proof. exact (TRANS (@lem5453590) (@lem5453611)). Qed.
Lemma lem5453613 : term370 = term336.
Proof. exact (TRANS (@lem5453589) (@lem5453612)). Qed.
Lemma lem5453615 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453616 : term336 = term335.
Proof. exact (@lem5453615 term335). Qed.
Lemma lem5453617 : term370 = term335.
Proof. exact (TRANS (@lem5453613) (@lem5453616)). Qed.
Lemma lem5453620 (_70535 : int) : (term378 _70535) = (term378 _70535).
Proof. exact (eq_refl (term378 _70535)). Qed.
Lemma lem5453621 (_70535 : int) : (term368 _70535) = (term379 _70535).
Proof. exact (MK_COMB (@lem5453620 _70535) (@lem5453617)). Qed.
Lemma lem5453622 (_70535 : int) : (term367 _70535) = (term379 _70535).
Proof. exact (TRANS (@lem5453580 _70535) (@lem5453621 _70535)). Qed.
Lemma lem5453623 (_70533 : int) : (term433 _70533) = (term433 _70533).
Proof. exact (eq_refl (term433 _70533)). Qed.
Lemma lem5453624 (_70533 : int) (_70535 : int) : (term432 _70533 _70535) = (term434 _70533 _70535).
Proof. exact (MK_COMB (@lem5453623 _70533) (@lem5453622 _70535)). Qed.
Lemma lem5453625 (_70533 : int) (_70535 : int) : (term434 _70533 _70535) = (term435 _70533 _70535).
Proof. exact (@lem1982755 (real_of_int _70533) term272 (term379 _70535)). Qed.
Lemma lem5453626 (_70535 : int) : (term436 _70535) = (term437 _70535).
Proof. exact (@lem1982757 (term360 _70535) term272 term335). Qed.
Lemma lem5453628 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453629 : term335 = term336.
Proof. exact (@lem5453628 term120). Qed.
Lemma lem5453631 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453632 : term272 = term369.
Proof. exact (@lem5453631 term120). Qed.
Lemma lem5453633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5453634 : term438 = term439.
Proof. exact (MK_COMB (@lem5453633) (@lem5453632)). Qed.
Lemma lem5453635 : term440 = term441.
Proof. exact (MK_COMB (@lem5453634) (@lem5453629)). Qed.
Lemma lem5453636 : term442.
Proof. exact (@lem1981473 term272 term272 term335 term272 term260 term272). Qed.
Lemma lem5453638 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5453639 : term444 = term445.
Proof. exact (@lem5453638 (NUMERAL 0) term120). Qed.
Lemma lem5453640 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5453641 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5453642 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5453641 h1) (fun h1 : term445 = True => @lem5453640)). Qed.
Lemma lem5453643 : term445 = True.
Proof. exact (EQ_MP (@lem5453642) (@lem5453640)). Qed.
Lemma lem5453644 : term444 = True.
Proof. exact (TRANS (@lem5453639) (@lem5453643)). Qed.
Lemma lem5453645 : True = term444.
Proof. exact (SYM (@lem5453644)). Qed.
Lemma lem5453646 : term444.
Proof. exact (EQ_MP (@lem5453645) (@lem0)). Qed.
Lemma lem5453647 : term447.
Proof. exact (@lem5453636 (@lem5453646)). Qed.
Lemma lem5453649 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5453650 : term444 = term445.
Proof. exact (@lem5453649 (NUMERAL 0) term120). Qed.
Lemma lem5453651 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5453652 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5453653 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5453652 h1) (fun h1 : term445 = True => @lem5453651)). Qed.
Lemma lem5453654 : term445 = True.
Proof. exact (EQ_MP (@lem5453653) (@lem5453651)). Qed.
Lemma lem5453655 : term444 = True.
Proof. exact (TRANS (@lem5453650) (@lem5453654)). Qed.
Lemma lem5453656 : True = term444.
Proof. exact (SYM (@lem5453655)). Qed.
Lemma lem5453657 : term444.
Proof. exact (EQ_MP (@lem5453656) (@lem0)). Qed.
Lemma lem5453658 : term448.
Proof. exact (@lem5453647 (@lem5453657)). Qed.
Lemma lem5453660 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5453661 : term444 = term445.
Proof. exact (@lem5453660 (NUMERAL 0) term120). Qed.
Lemma lem5453662 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5453663 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5453664 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5453663 h1) (fun h1 : term445 = True => @lem5453662)). Qed.
Lemma lem5453665 : term445 = True.
Proof. exact (EQ_MP (@lem5453664) (@lem5453662)). Qed.
Lemma lem5453666 : term444 = True.
Proof. exact (TRANS (@lem5453661) (@lem5453665)). Qed.
Lemma lem5453667 : True = term444.
Proof. exact (SYM (@lem5453666)). Qed.
Lemma lem5453668 : term444.
Proof. exact (EQ_MP (@lem5453667) (@lem0)). Qed.
Lemma lem5453669 : term449.
Proof. exact (@lem5453658 (@lem5453668)). Qed.
Lemma lem5453671 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453672 : term370 = term375.
Proof. exact (@lem5453671 term120 term120). Qed.
Lemma lem5453673 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453674 : term347 = term120.
Proof. exact (EQ_MP (@lem5453673) (@lem940073)). Qed.
Lemma lem5453675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453676 : term345 = term272.
Proof. exact (MK_COMB (@lem5453675) (@lem5453674)). Qed.
Lemma lem5453677 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453678 : term375 = term335.
Proof. exact (MK_COMB (@lem5453677) (@lem5453676)). Qed.
Lemma lem5453679 : term370 = term335.
Proof. exact (TRANS (@lem5453672) (@lem5453678)). Qed.
Lemma lem5453681 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453682 : term344 = term345.
Proof. exact (@lem5453681 term120 term120). Qed.
Lemma lem5453683 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453684 : term347 = term120.
Proof. exact (EQ_MP (@lem5453683) (@lem940073)). Qed.
Lemma lem5453685 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453686 : term345 = term272.
Proof. exact (MK_COMB (@lem5453685) (@lem5453684)). Qed.
Lemma lem5453687 : term344 = term272.
Proof. exact (TRANS (@lem5453682) (@lem5453686)). Qed.
Lemma lem5453688 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5453689 : term450 = term438.
Proof. exact (MK_COMB (@lem5453688) (@lem5453687)). Qed.
Lemma lem5453690 : term451 = term440.
Proof. exact (MK_COMB (@lem5453689) (@lem5453679)). Qed.
Lemma lem5453692 (m : nat) : (term452 m) = term260.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5453693 : term440 = term260.
Proof. exact (@lem5453692 term120). Qed.
Lemma lem5453694 : term451 = term260.
Proof. exact (TRANS (@lem5453690) (@lem5453693)). Qed.
Lemma lem5453695 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453696 : term453 = term454.
Proof. exact (MK_COMB (@lem5453695) (@lem5453694)). Qed.
Lemma lem5453697 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5453698 : term455 = term456.
Proof. exact (MK_COMB (@lem5453696) (@lem5453697)). Qed.
Lemma lem5453700 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5453701 : term456 = term260.
Proof. exact (@lem5453700 term120). Qed.
Lemma lem5453702 : term455 = term260.
Proof. exact (TRANS (@lem5453698) (@lem5453701)). Qed.
Lemma lem5453704 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453705 : term344 = term345.
Proof. exact (@lem5453704 term120 term120). Qed.
Lemma lem5453706 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453707 : term347 = term120.
Proof. exact (EQ_MP (@lem5453706) (@lem940073)). Qed.
Lemma lem5453708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453709 : term345 = term272.
Proof. exact (MK_COMB (@lem5453708) (@lem5453707)). Qed.
Lemma lem5453710 : term344 = term272.
Proof. exact (TRANS (@lem5453705) (@lem5453709)). Qed.
Lemma lem5453711 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5453712 : term458 = term456.
Proof. exact (MK_COMB (@lem5453711) (@lem5453710)). Qed.
Lemma lem5453714 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5453715 : term456 = term260.
Proof. exact (@lem5453714 term120). Qed.
Lemma lem5453716 : term458 = term260.
Proof. exact (TRANS (@lem5453712) (@lem5453715)). Qed.
Lemma lem5453717 : term260 = term458.
Proof. exact (SYM (@lem5453716)). Qed.
Lemma lem5453718 : term455 = term458.
Proof. exact (TRANS (@lem5453702) (@lem5453717)). Qed.
Lemma lem5453719 : term441 = term332.
Proof. exact (@lem5453669 (@lem5453718)). Qed.
Lemma lem5453720 : term440 = term332.
Proof. exact (TRANS (@lem5453635) (@lem5453719)). Qed.
Lemma lem5453722 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5453723 : term332 = term260.
Proof. exact (@lem5453722 term260). Qed.
Lemma lem5453724 : term440 = term260.
Proof. exact (TRANS (@lem5453720) (@lem5453723)). Qed.
Lemma lem5453725 (_70535 : int) : (term378 _70535) = (term378 _70535).
Proof. exact (eq_refl (term378 _70535)). Qed.
Lemma lem5453726 (_70535 : int) : (term437 _70535) = (term459 _70535).
Proof. exact (MK_COMB (@lem5453725 _70535) (@lem5453724)). Qed.
Lemma lem5453727 (_70535 : int) : (term436 _70535) = (term459 _70535).
Proof. exact (TRANS (@lem5453626 _70535) (@lem5453726 _70535)). Qed.
Lemma lem5453728 (_70535 : int) : (term459 _70535) = (term360 _70535).
Proof. exact (@lem1982723 (term360 _70535)). Qed.
Lemma lem5453729 (_70535 : int) : (term436 _70535) = (term360 _70535).
Proof. exact (TRANS (@lem5453727 _70535) (@lem5453728 _70535)). Qed.
Lemma lem5453730 (_70533 : int) : (term273 _70533) = (term273 _70533).
Proof. exact (eq_refl (term273 _70533)). Qed.
Lemma lem5453731 (_70533 : int) (_70535 : int) : (term435 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (MK_COMB (@lem5453730 _70533) (@lem5453729 _70535)). Qed.
Lemma lem5453732 (_70533 : int) (_70535 : int) : (term434 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (TRANS (@lem5453625 _70533 _70535) (@lem5453731 _70533 _70535)). Qed.
Lemma lem5453733 (_70533 : int) (_70535 : int) : (term432 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (TRANS (@lem5453624 _70533 _70535) (@lem5453732 _70533 _70535)). Qed.
Lemma lem5453735 (_70533 : int) (_70535 : int) : (term431 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (TRANS (@lem5453579 _70533 _70535) (@lem5453733 _70533 _70535)). Qed.
Lemma lem5453736 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453737 (_70533 : int) (_70535 : int) : (term460 _70533 _70535) = (term409 _70533 _70535).
Proof. exact (MK_COMB (@lem5453736) (@lem5453735 _70533 _70535)). Qed.
Lemma lem5453738 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453739 (_70533 : int) (_70535 : int) : (term430 _70533 _70535) = (term410 _70533 _70535).
Proof. exact (MK_COMB (@lem5453737 _70533 _70535) (@lem5453738)). Qed.
Lemma lem5453740 (_70533 : int) (_70535 : int) : (term309 _70535 _70533) = (term410 _70533 _70535).
Proof. exact (TRANS (@lem5453561 _70533 _70535) (@lem5453739 _70533 _70535)). Qed.
Lemma lem5453741 (_70535 : int) (_70533 : int) (_70534 : int) : (term291 _70533 _70534 _70535) = (term384 _70535 _70533 _70534).
Proof. exact (@lem1988287 (real_of_int _70535) (term288 _70533 _70534)). Qed.
Lemma lem5453758 (_70533 : int) (_70534 : int) : (term288 _70533 _70534) = (term385 _70533 _70534).
Proof. exact (@lem1982755 (real_of_int _70533) (real_of_int _70534) term272). Qed.
Lemma lem5453761 (_70535 : int) : (term386 _70535) = (term386 _70535).
Proof. exact (eq_refl (term386 _70535)). Qed.
Lemma lem5453762 (_70535 : int) (_70533 : int) (_70534 : int) : (term387 _70535 _70533 _70534) = (term388 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5453761 _70535) (@lem5453758 _70533 _70534)). Qed.
Lemma lem5453763 (_70535 : int) (_70533 : int) (_70534 : int) : (term388 _70535 _70533 _70534) = (term389 _70535 _70533 _70534).
Proof. exact (@lem1982792 (real_of_int _70535) (term385 _70533 _70534)). Qed.
Lemma lem5453764 (_70533 : int) (_70534 : int) : (term390 _70533 _70534) = (term391 _70533 _70534).
Proof. exact (@lem1982781 (real_of_int _70533) term335 (term274 _70534)). Qed.
Lemma lem5453765 (_70534 : int) : (term367 _70534) = (term368 _70534).
Proof. exact (@lem1982781 (real_of_int _70534) term335 term272). Qed.
Lemma lem5453767 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5453768 : term272 = term369.
Proof. exact (@lem5453767 term120). Qed.
Lemma lem5453770 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5453771 : term335 = term336.
Proof. exact (@lem5453770 term120). Qed.
Lemma lem5453772 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5453773 : term337 = term338.
Proof. exact (MK_COMB (@lem5453772) (@lem5453771)). Qed.
Lemma lem5453774 : term370 = term371.
Proof. exact (MK_COMB (@lem5453773) (@lem5453768)). Qed.
Lemma lem5453775 : term371 = term372.
Proof. exact (@lem1981613 term335 term272 term272 term272). Qed.
Lemma lem5453777 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5453778 : term344 = term345.
Proof. exact (@lem5453777 term120 term120). Qed.
Lemma lem5453779 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453780 : term347 = term120.
Proof. exact (EQ_MP (@lem5453779) (@lem940073)). Qed.
Lemma lem5453781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453782 : term345 = term272.
Proof. exact (MK_COMB (@lem5453781) (@lem5453780)). Qed.
Lemma lem5453783 : term344 = term272.
Proof. exact (TRANS (@lem5453778) (@lem5453782)). Qed.
Lemma lem5453785 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5453786 : term370 = term375.
Proof. exact (@lem5453785 term120 term120). Qed.
Lemma lem5453787 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5453788 : term347 = term120.
Proof. exact (EQ_MP (@lem5453787) (@lem940073)). Qed.
Lemma lem5453789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5453790 : term345 = term272.
Proof. exact (MK_COMB (@lem5453789) (@lem5453788)). Qed.
Lemma lem5453791 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5453792 : term375 = term335.
Proof. exact (MK_COMB (@lem5453791) (@lem5453790)). Qed.
Lemma lem5453793 : term370 = term335.
Proof. exact (TRANS (@lem5453786) (@lem5453792)). Qed.
Lemma lem5453794 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5453795 : term376 = term377.
Proof. exact (MK_COMB (@lem5453794) (@lem5453793)). Qed.
Lemma lem5453796 : term372 = term336.
Proof. exact (MK_COMB (@lem5453795) (@lem5453783)). Qed.
Lemma lem5453797 : term371 = term336.
Proof. exact (TRANS (@lem5453775) (@lem5453796)). Qed.
Lemma lem5453798 : term370 = term336.
Proof. exact (TRANS (@lem5453774) (@lem5453797)). Qed.
Lemma lem5453800 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5453801 : term336 = term335.
Proof. exact (@lem5453800 term335). Qed.
Lemma lem5453802 : term370 = term335.
Proof. exact (TRANS (@lem5453798) (@lem5453801)). Qed.
Lemma lem5453805 (_70534 : int) : (term378 _70534) = (term378 _70534).
Proof. exact (eq_refl (term378 _70534)). Qed.
Lemma lem5453806 (_70534 : int) : (term368 _70534) = (term379 _70534).
Proof. exact (MK_COMB (@lem5453805 _70534) (@lem5453802)). Qed.
Lemma lem5453807 (_70534 : int) : (term367 _70534) = (term379 _70534).
Proof. exact (TRANS (@lem5453765 _70534) (@lem5453806 _70534)). Qed.
Lemma lem5453810 (_70533 : int) : (term378 _70533) = (term378 _70533).
Proof. exact (eq_refl (term378 _70533)). Qed.
Lemma lem5453811 (_70533 : int) (_70534 : int) : (term391 _70533 _70534) = (term392 _70533 _70534).
Proof. exact (MK_COMB (@lem5453810 _70533) (@lem5453807 _70534)). Qed.
Lemma lem5453812 (_70533 : int) (_70534 : int) : (term390 _70533 _70534) = (term392 _70533 _70534).
Proof. exact (TRANS (@lem5453764 _70533 _70534) (@lem5453811 _70533 _70534)). Qed.
Lemma lem5453813 (_70535 : int) : (term273 _70535) = (term273 _70535).
Proof. exact (eq_refl (term273 _70535)). Qed.
Lemma lem5453814 (_70535 : int) (_70533 : int) (_70534 : int) : (term389 _70535 _70533 _70534) = (term393 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5453813 _70535) (@lem5453812 _70533 _70534)). Qed.
Lemma lem5453815 (_70533 : int) (_70535 : int) (_70534 : int) : (term393 _70535 _70533 _70534) = (term394 _70533 _70535 _70534).
Proof. exact (@lem1982757 (term360 _70533) (real_of_int _70535) (term379 _70534)). Qed.
Lemma lem5453820 (_70534 : int) (_70535 : int) : (term380 _70535 _70534) = (term395 _70534 _70535).
Proof. exact (@lem1982757 (term360 _70534) (real_of_int _70535) term335). Qed.
Lemma lem5453821 (_70533 : int) : (term378 _70533) = (term378 _70533).
Proof. exact (eq_refl (term378 _70533)). Qed.
Lemma lem5453822 (_70533 : int) (_70534 : int) (_70535 : int) : (term394 _70533 _70535 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453821 _70533) (@lem5453820 _70534 _70535)). Qed.
Lemma lem5453823 (_70533 : int) (_70534 : int) (_70535 : int) : (term393 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453815 _70533 _70535 _70534) (@lem5453822 _70533 _70534 _70535)). Qed.
Lemma lem5453824 (_70533 : int) (_70534 : int) (_70535 : int) : (term389 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453814 _70535 _70533 _70534) (@lem5453823 _70533 _70534 _70535)). Qed.
Lemma lem5453825 (_70533 : int) (_70534 : int) (_70535 : int) : (term388 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453763 _70535 _70533 _70534) (@lem5453824 _70533 _70534 _70535)). Qed.
Lemma lem5453826 (_70533 : int) (_70534 : int) (_70535 : int) : (term387 _70535 _70533 _70534) = (term396 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453762 _70535 _70533 _70534) (@lem5453825 _70533 _70534 _70535)). Qed.
Lemma lem5453827 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5453828 (_70533 : int) (_70534 : int) (_70535 : int) : (term397 _70535 _70533 _70534) = (term398 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453827) (@lem5453826 _70533 _70534 _70535)). Qed.
Lemma lem5453829 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5453830 (_70533 : int) (_70534 : int) (_70535 : int) : (term384 _70535 _70533 _70534) = (term399 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453828 _70533 _70534 _70535) (@lem5453829)). Qed.
Lemma lem5453831 (_70533 : int) (_70534 : int) (_70535 : int) : (term291 _70533 _70534 _70535) = (term399 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453741 _70535 _70533 _70534) (@lem5453830 _70533 _70534 _70535)). Qed.
Lemma lem5453832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453833 (_70533 : int) (_70535 : int) : (term311 _70535 _70533) = (term461 _70533 _70535).
Proof. exact (MK_COMB (@lem5453832) (@lem5453740 _70533 _70535)). Qed.
Lemma lem5453834 (_70533 : int) (_70534 : int) (_70535 : int) : (term312 _70533 _70534 _70535) = (term462 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453833 _70533 _70535) (@lem5453831 _70533 _70534 _70535)). Qed.
Lemma lem5453835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453836 (_70532 : int) (_70533 : int) (_70535 : int) : (term313 _70532 _70533 _70535) = (term463 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5453835) (@lem5453560 _70532 _70533 _70535)). Qed.
Lemma lem5453837 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term314 _70532 _70533 _70534 _70535) = (term464 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453836 _70532 _70533 _70535) (@lem5453834 _70533 _70534 _70535)). Qed.
Lemma lem5453838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453839 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term315 _70532 _70535 _70533 _70534) = (term465 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453838) (@lem5453419 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453840 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term316 _70532 _70533 _70534 _70535) = (term466 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453839 _70532 _70533 _70534 _70535) (@lem5453837 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453842 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term317 _70532 _70535 _70533 _70534) = (term467 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453841) (@lem5453368 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453843 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term318 _70532 _70533 _70534 _70535) = (term468 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453842 _70532 _70533 _70534 _70535) (@lem5453840 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453845 (_70532 : int) (_70533 : int) : (term319 _70532 _70533) = (term469 _70532 _70533).
Proof. exact (MK_COMB (@lem5453844) (@lem5453057 _70532 _70533)). Qed.
Lemma lem5453846 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term320 _70532 _70533 _70534 _70535) = (term470 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453845 _70532 _70533) (@lem5453843 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453848 (_70535 : int) : (term321 _70535) = (term471 _70535).
Proof. exact (MK_COMB (@lem5453847) (@lem5453032 _70535)). Qed.
Lemma lem5453849 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term322 _70532 _70533 _70534 _70535) = (term472 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453848 _70535) (@lem5453846 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453851 (_70534 : int) : (term321 _70534) = (term471 _70534).
Proof. exact (MK_COMB (@lem5453850) (@lem5452984 _70534)). Qed.
Lemma lem5453852 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term323 _70532 _70533 _70534 _70535) = (term473 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453851 _70534) (@lem5453849 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453854 (_70533 : int) : (term321 _70533) = (term471 _70533).
Proof. exact (MK_COMB (@lem5453853) (@lem5452936 _70533)). Qed.
Lemma lem5453855 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term324 _70532 _70533 _70534 _70535) = (term474 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453854 _70533) (@lem5453852 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5453857 (_70532 : int) : (term321 _70532) = (term471 _70532).
Proof. exact (MK_COMB (@lem5453856) (@lem5452888 _70532)). Qed.
Lemma lem5453858 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term325 _70532 _70533 _70534 _70535) = (term475 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453857 _70532) (@lem5453855 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453865 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term327 _70532 _70533 _70534 _70535) = (term475 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5452840 _70532 _70533 _70534 _70535) (@lem5453858 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453879 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term464 _70532 _70533 _70534 _70535) = (term476 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term410 _70533 _70535) (term429 _70532 _70533 _70535) (term399 _70533 _70534 _70535)). Qed.
Lemma lem5453886 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term477 _70532 _70533 _70534 _70535) = (term478 _70532 _70533 _70534 _70535).
Proof. exact (@lem19367 (term383 _70532 _70535) (term414 _70533 _70535) (term399 _70533 _70534 _70535)). Qed.
Lemma lem5453893 (_70532 : int) (_70533 : int) (_70535 : int) : (term479 _70532 _70533 _70535) = (term480 _70532 _70533 _70535).
Proof. exact (@lem19367 (term383 _70532 _70535) (term414 _70533 _70535) (term410 _70533 _70535)). Qed.
Lemma lem5453894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453895 (_70532 : int) (_70533 : int) (_70535 : int) : (term481 _70532 _70533 _70535) = (term482 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5453894) (@lem5453893 _70532 _70533 _70535)). Qed.
Lemma lem5453896 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term476 _70532 _70533 _70534 _70535) = (term483 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453895 _70532 _70533 _70535) (@lem5453886 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453898 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term464 _70532 _70533 _70534 _70535) = (term483 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453879 _70532 _70533 _70534 _70535) (@lem5453896 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453907 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term465 _70532 _70533 _70534 _70535) = (term465 _70532 _70533 _70534 _70535).
Proof. exact (eq_refl (term465 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453908 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term466 _70532 _70533 _70534 _70535) = (term484 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453907 _70532 _70533 _70534 _70535) (@lem5453898 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453909 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term484 _70532 _70533 _70534 _70535) = (term485 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term480 _70532 _70533 _70535) (term428 _70532 _70533 _70534 _70535) (term478 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453916 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term486 _70532 _70533 _70534 _70535) = (term487 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term488 _70532 _70533 _70534 _70535) (term428 _70532 _70533 _70534 _70535) (term489 _70533 _70534 _70535)). Qed.
Lemma lem5453923 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term490 _70534 _70532 _70533 _70535) = (term491 _70532 _70534 _70533 _70535).
Proof. exact (@lem19158 (term492 _70532 _70533 _70535) (term428 _70532 _70533 _70534 _70535) (term493 _70533 _70535)). Qed.
Lemma lem5453924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453925 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term494 _70534 _70532 _70533 _70535) = (term495 _70532 _70534 _70533 _70535).
Proof. exact (MK_COMB (@lem5453924) (@lem5453923 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5453926 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term485 _70532 _70533 _70534 _70535) = (term496 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453925 _70532 _70534 _70533 _70535) (@lem5453916 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453927 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term484 _70532 _70533 _70534 _70535) = (term496 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453909 _70532 _70533 _70534 _70535) (@lem5453926 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453928 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term466 _70532 _70533 _70534 _70535) = (term496 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453908 _70532 _70533 _70534 _70535) (@lem5453927 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453954 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term427 _70532 _70533 _70534 _70535) = (term497 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term412 _70532 _70533 _70535) (term401 _70532 _70533 _70534 _70535) (term423 _70533 _70534 _70535)). Qed.
Lemma lem5453961 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term498 _70532 _70533 _70534 _70535) = (term499 _70532 _70533 _70534 _70535).
Proof. exact (@lem19367 (term383 _70532 _70535) (term399 _70533 _70534 _70535) (term423 _70533 _70534 _70535)). Qed.
Lemma lem5453968 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term500 _70534 _70532 _70533 _70535) = (term501 _70534 _70532 _70533 _70535).
Proof. exact (@lem19367 (term383 _70532 _70535) (term399 _70533 _70534 _70535) (term412 _70532 _70533 _70535)). Qed.
Lemma lem5453969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453970 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term502 _70534 _70532 _70533 _70535) = (term503 _70534 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5453969) (@lem5453968 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5453971 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term497 _70532 _70533 _70534 _70535) = (term504 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453970 _70534 _70532 _70533 _70535) (@lem5453961 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453973 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term427 _70532 _70533 _70534 _70535) = (term504 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453954 _70532 _70533 _70534 _70535) (@lem5453971 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453975 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term467 _70532 _70533 _70534 _70535) = (term505 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453974) (@lem5453973 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453976 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term468 _70532 _70533 _70534 _70535) = (term506 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453975 _70532 _70533 _70534 _70535) (@lem5453928 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453979 (_70532 : int) (_70533 : int) : (term469 _70532 _70533) = (term469 _70532 _70533).
Proof. exact (eq_refl (term469 _70532 _70533)). Qed.
Lemma lem5453980 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term470 _70532 _70533 _70534 _70535) = (term507 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453979 _70532 _70533) (@lem5453976 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453981 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term507 _70532 _70533 _70534 _70535) = (term508 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term504 _70532 _70533 _70534 _70535) (term363 _70532 _70533) (term496 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453982 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term509 _70532 _70533 _70534 _70535) = (term510 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term491 _70532 _70534 _70533 _70535) (term363 _70532 _70533) (term487 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453989 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term511 _70532 _70533 _70534 _70535) = (term512 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term513 _70532 _70533 _70534 _70535) (term363 _70532 _70533) (term514 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5453996 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term515 _70532 _70534 _70533 _70535) = (term516 _70532 _70534 _70533 _70535).
Proof. exact (@lem19158 (term517 _70534 _70532 _70533 _70535) (term363 _70532 _70533) (term518 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5453997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5453998 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term519 _70532 _70534 _70533 _70535) = (term520 _70532 _70534 _70533 _70535).
Proof. exact (MK_COMB (@lem5453997) (@lem5453996 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5453999 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term510 _70532 _70533 _70534 _70535) = (term521 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5453998 _70532 _70534 _70533 _70535) (@lem5453989 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454000 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term509 _70532 _70533 _70534 _70535) = (term521 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453982 _70532 _70533 _70534 _70535) (@lem5453999 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454001 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term522 _70532 _70533 _70534 _70535) = (term523 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term501 _70534 _70532 _70533 _70535) (term363 _70532 _70533) (term499 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454008 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term524 _70532 _70533 _70534 _70535) = (term525 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term526 _70532 _70533 _70534 _70535) (term363 _70532 _70533) (term527 _70533 _70534 _70535)). Qed.
Lemma lem5454015 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term528 _70534 _70532 _70533 _70535) = (term529 _70534 _70532 _70533 _70535).
Proof. exact (@lem19158 (term530 _70532 _70533 _70535) (term363 _70532 _70533) (term531 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454017 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term532 _70534 _70532 _70533 _70535) = (term533 _70534 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5454016) (@lem5454015 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454018 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term523 _70532 _70533 _70534 _70535) = (term534 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454017 _70534 _70532 _70533 _70535) (@lem5454008 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454019 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term522 _70532 _70533 _70534 _70535) = (term534 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454001 _70532 _70533 _70534 _70535) (@lem5454018 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454021 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term535 _70532 _70533 _70534 _70535) = (term536 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454020) (@lem5454019 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454022 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term508 _70532 _70533 _70534 _70535) = (term537 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454021 _70532 _70533 _70534 _70535) (@lem5454000 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454023 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term507 _70532 _70533 _70534 _70535) = (term537 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453981 _70532 _70533 _70534 _70535) (@lem5454022 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454024 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term470 _70532 _70533 _70534 _70535) = (term537 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453980 _70532 _70533 _70534 _70535) (@lem5454023 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454027 (_70535 : int) : (term471 _70535) = (term471 _70535).
Proof. exact (eq_refl (term471 _70535)). Qed.
Lemma lem5454028 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term472 _70532 _70533 _70534 _70535) = (term538 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454027 _70535) (@lem5454024 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454029 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term538 _70532 _70533 _70534 _70535) = (term539 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term534 _70532 _70533 _70534 _70535) (term355 _70535) (term521 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454030 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term540 _70532 _70533 _70534 _70535) = (term541 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term516 _70532 _70534 _70533 _70535) (term355 _70535) (term512 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454037 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term542 _70532 _70533 _70534 _70535) = (term543 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term544 _70532 _70533 _70534 _70535) (term355 _70535) (term545 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454044 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term546 _70532 _70534 _70533 _70535) = (term547 _70532 _70534 _70533 _70535).
Proof. exact (@lem19158 (term548 _70534 _70532 _70533 _70535) (term355 _70535) (term549 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454046 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term550 _70532 _70534 _70533 _70535) = (term551 _70532 _70534 _70533 _70535).
Proof. exact (MK_COMB (@lem5454045) (@lem5454044 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454047 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term541 _70532 _70533 _70534 _70535) = (term552 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454046 _70532 _70534 _70533 _70535) (@lem5454037 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454048 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term540 _70532 _70533 _70534 _70535) = (term552 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454030 _70532 _70533 _70534 _70535) (@lem5454047 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454049 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term553 _70532 _70533 _70534 _70535) = (term554 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term529 _70534 _70532 _70533 _70535) (term355 _70535) (term525 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454056 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term555 _70532 _70533 _70534 _70535) = (term556 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term557 _70532 _70533 _70534 _70535) (term355 _70535) (term558 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454063 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term559 _70534 _70532 _70533 _70535) = (term560 _70534 _70532 _70533 _70535).
Proof. exact (@lem19158 (term561 _70532 _70533 _70535) (term355 _70535) (term562 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454065 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term563 _70534 _70532 _70533 _70535) = (term564 _70534 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5454064) (@lem5454063 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454066 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term554 _70532 _70533 _70534 _70535) = (term565 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454065 _70534 _70532 _70533 _70535) (@lem5454056 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454067 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term553 _70532 _70533 _70534 _70535) = (term565 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454049 _70532 _70533 _70534 _70535) (@lem5454066 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454069 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term566 _70532 _70533 _70534 _70535) = (term567 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454068) (@lem5454067 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454070 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term539 _70532 _70533 _70534 _70535) = (term568 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454069 _70532 _70533 _70534 _70535) (@lem5454048 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454071 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term538 _70532 _70533 _70534 _70535) = (term568 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454029 _70532 _70533 _70534 _70535) (@lem5454070 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454072 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term472 _70532 _70533 _70534 _70535) = (term568 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454028 _70532 _70533 _70534 _70535) (@lem5454071 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454075 (_70534 : int) : (term471 _70534) = (term471 _70534).
Proof. exact (eq_refl (term471 _70534)). Qed.
Lemma lem5454076 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term473 _70532 _70533 _70534 _70535) = (term569 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454075 _70534) (@lem5454072 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454077 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term569 _70532 _70533 _70534 _70535) = (term570 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term565 _70532 _70533 _70534 _70535) (term355 _70534) (term552 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454078 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term571 _70532 _70533 _70534 _70535) = (term572 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term547 _70532 _70534 _70533 _70535) (term355 _70534) (term543 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454085 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term573 _70532 _70533 _70534 _70535) = (term574 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term575 _70532 _70533 _70534 _70535) (term355 _70534) (term576 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454092 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term577 _70532 _70534 _70533 _70535) = (term578 _70532 _70534 _70533 _70535).
Proof. exact (@lem19158 (term579 _70534 _70532 _70533 _70535) (term355 _70534) (term580 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454094 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term581 _70532 _70534 _70533 _70535) = (term582 _70532 _70534 _70533 _70535).
Proof. exact (MK_COMB (@lem5454093) (@lem5454092 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454095 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term572 _70532 _70533 _70534 _70535) = (term583 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454094 _70532 _70534 _70533 _70535) (@lem5454085 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454096 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term571 _70532 _70533 _70534 _70535) = (term583 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454078 _70532 _70533 _70534 _70535) (@lem5454095 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454097 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term584 _70532 _70533 _70534 _70535) = (term585 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term560 _70534 _70532 _70533 _70535) (term355 _70534) (term556 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454104 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term586 _70532 _70533 _70534 _70535) = (term587 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term588 _70532 _70533 _70534 _70535) (term355 _70534) (term589 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454111 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term590 _70534 _70532 _70533 _70535) = (term591 _70534 _70532 _70533 _70535).
Proof. exact (@lem19158 (term592 _70532 _70533 _70535) (term355 _70534) (term593 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454112 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454113 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term594 _70534 _70532 _70533 _70535) = (term595 _70534 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5454112) (@lem5454111 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454114 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term585 _70532 _70533 _70534 _70535) = (term596 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454113 _70534 _70532 _70533 _70535) (@lem5454104 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454115 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term584 _70532 _70533 _70534 _70535) = (term596 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454097 _70532 _70533 _70534 _70535) (@lem5454114 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454117 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term597 _70532 _70533 _70534 _70535) = (term598 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454116) (@lem5454115 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454118 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term570 _70532 _70533 _70534 _70535) = (term599 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454117 _70532 _70533 _70534 _70535) (@lem5454096 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454119 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term569 _70532 _70533 _70534 _70535) = (term599 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454077 _70532 _70533 _70534 _70535) (@lem5454118 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454120 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term473 _70532 _70533 _70534 _70535) = (term599 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454076 _70532 _70533 _70534 _70535) (@lem5454119 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454123 (_70533 : int) : (term471 _70533) = (term471 _70533).
Proof. exact (eq_refl (term471 _70533)). Qed.
Lemma lem5454124 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term474 _70532 _70533 _70534 _70535) = (term600 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454123 _70533) (@lem5454120 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454125 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term600 _70532 _70533 _70534 _70535) = (term601 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term596 _70532 _70533 _70534 _70535) (term355 _70533) (term583 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454126 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term602 _70532 _70533 _70534 _70535) = (term603 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term578 _70532 _70534 _70533 _70535) (term355 _70533) (term574 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454133 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term604 _70532 _70533 _70534 _70535) = (term605 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term606 _70532 _70533 _70534 _70535) (term355 _70533) (term607 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454140 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term608 _70532 _70534 _70533 _70535) = (term609 _70532 _70534 _70533 _70535).
Proof. exact (@lem19158 (term610 _70534 _70532 _70533 _70535) (term355 _70533) (term611 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454142 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term612 _70532 _70534 _70533 _70535) = (term613 _70532 _70534 _70533 _70535).
Proof. exact (MK_COMB (@lem5454141) (@lem5454140 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454143 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term603 _70532 _70533 _70534 _70535) = (term614 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454142 _70532 _70534 _70533 _70535) (@lem5454133 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454144 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term602 _70532 _70533 _70534 _70535) = (term614 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454126 _70532 _70533 _70534 _70535) (@lem5454143 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454145 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term615 _70532 _70533 _70534 _70535) = (term616 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term591 _70534 _70532 _70533 _70535) (term355 _70533) (term587 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454152 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term617 _70532 _70533 _70534 _70535) = (term618 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term619 _70532 _70533 _70534 _70535) (term355 _70533) (term620 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454159 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term621 _70534 _70532 _70533 _70535) = (term622 _70534 _70532 _70533 _70535).
Proof. exact (@lem19158 (term623 _70534 _70532 _70533 _70535) (term355 _70533) (term624 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454161 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term625 _70534 _70532 _70533 _70535) = (term626 _70534 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5454160) (@lem5454159 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454162 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term616 _70532 _70533 _70534 _70535) = (term627 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454161 _70534 _70532 _70533 _70535) (@lem5454152 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454163 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term615 _70532 _70533 _70534 _70535) = (term627 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454145 _70532 _70533 _70534 _70535) (@lem5454162 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454165 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term628 _70532 _70533 _70534 _70535) = (term629 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454164) (@lem5454163 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454166 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term601 _70532 _70533 _70534 _70535) = (term630 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454165 _70532 _70533 _70534 _70535) (@lem5454144 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454167 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term600 _70532 _70533 _70534 _70535) = (term630 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454125 _70532 _70533 _70534 _70535) (@lem5454166 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454168 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term474 _70532 _70533 _70534 _70535) = (term630 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454124 _70532 _70533 _70534 _70535) (@lem5454167 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454171 (_70532 : int) : (term471 _70532) = (term471 _70532).
Proof. exact (eq_refl (term471 _70532)). Qed.
Lemma lem5454172 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term475 _70532 _70533 _70534 _70535) = (term631 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454171 _70532) (@lem5454168 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454173 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term631 _70532 _70533 _70534 _70535) = (term632 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term627 _70532 _70533 _70534 _70535) (term355 _70532) (term614 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454174 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term633 _70532 _70533 _70534 _70535) = (term634 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term609 _70532 _70534 _70533 _70535) (term355 _70532) (term605 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454181 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term635 _70532 _70533 _70534 _70535) = (term636 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term637 _70532 _70533 _70534 _70535) (term355 _70532) (term638 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454188 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term639 _70532 _70534 _70533 _70535) = (term640 _70532 _70534 _70533 _70535).
Proof. exact (@lem19158 (term641 _70534 _70532 _70533 _70535) (term355 _70532) (term642 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454190 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) : (term643 _70532 _70534 _70533 _70535) = (term644 _70532 _70534 _70533 _70535).
Proof. exact (MK_COMB (@lem5454189) (@lem5454188 _70532 _70534 _70533 _70535)). Qed.
Lemma lem5454191 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term634 _70532 _70533 _70534 _70535) = (term645 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454190 _70532 _70534 _70533 _70535) (@lem5454181 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454192 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term633 _70532 _70533 _70534 _70535) = (term645 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454174 _70532 _70533 _70534 _70535) (@lem5454191 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454193 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term646 _70532 _70533 _70534 _70535) = (term647 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term622 _70534 _70532 _70533 _70535) (term355 _70532) (term618 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454200 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term648 _70532 _70533 _70534 _70535) = (term649 _70532 _70533 _70534 _70535).
Proof. exact (@lem19158 (term650 _70532 _70533 _70534 _70535) (term355 _70532) (term651 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454207 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term652 _70534 _70532 _70533 _70535) = (term653 _70534 _70532 _70533 _70535).
Proof. exact (@lem19158 (term654 _70534 _70532 _70533 _70535) (term355 _70532) (term655 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454209 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) : (term656 _70534 _70532 _70533 _70535) = (term657 _70534 _70532 _70533 _70535).
Proof. exact (MK_COMB (@lem5454208) (@lem5454207 _70534 _70532 _70533 _70535)). Qed.
Lemma lem5454210 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term647 _70532 _70533 _70534 _70535) = (term658 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454209 _70534 _70532 _70533 _70535) (@lem5454200 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454211 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term646 _70532 _70533 _70534 _70535) = (term658 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454193 _70532 _70533 _70534 _70535) (@lem5454210 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5454213 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term659 _70532 _70533 _70534 _70535) = (term660 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454212) (@lem5454211 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454214 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term632 _70532 _70533 _70534 _70535) = (term661 _70532 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454213 _70532 _70533 _70534 _70535) (@lem5454192 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454215 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term631 _70532 _70533 _70534 _70535) = (term661 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454173 _70532 _70533 _70534 _70535) (@lem5454214 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454216 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term475 _70532 _70533 _70534 _70535) = (term661 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5454172 _70532 _70533 _70534 _70535) (@lem5454215 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454217 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : (term327 _70532 _70533 _70534 _70535) = (term661 _70532 _70533 _70534 _70535).
Proof. exact (TRANS (@lem5453865 _70532 _70533 _70534 _70535) (@lem5454216 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5454263 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term661 _70532 _70533 _70534 _70535) : term661 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5454264 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term658 _70532 _70533 _70534 _70535) : term658 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5454265 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term653 _70534 _70532 _70533 _70535) : term653 _70534 _70532 _70533 _70535.
Proof. exact (h1). Qed.
Lemma lem5454266 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term662 _70534 _70532 _70533 _70535.
Proof. exact (h1). Qed.
Lemma lem5454267 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term654 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454266 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454269 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term623 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454267 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454271 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term592 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454269 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454273 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term561 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454271 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454275 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term530 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454273 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454277 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term412 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454275 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454278 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term383 _70532 _70535.
Proof. exact (proj1 (@lem5454275 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454280 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term408 _70532 _70535.
Proof. exact (proj1 (@lem5454277 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454282 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5454283 : term663 = term444.
Proof. exact (@lem5454282 term260 term272). Qed.
Lemma lem5454285 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454286 : term272 = term369.
Proof. exact (@lem5454285 term120). Qed.
Lemma lem5454288 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454289 : term260 = term332.
Proof. exact (@lem5454288 (NUMERAL 0)). Qed.
Lemma lem5454290 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454291 : term664 = term665.
Proof. exact (MK_COMB (@lem5454290) (@lem5454289)). Qed.
Lemma lem5454292 : term444 = term666.
Proof. exact (MK_COMB (@lem5454291) (@lem5454286)). Qed.
Lemma lem5454293 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5454295 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454296 : term444 = term445.
Proof. exact (@lem5454295 (NUMERAL 0) term120). Qed.
Lemma lem5454297 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454298 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454299 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454298 h1) (fun h1 : term445 = True => @lem5454297)). Qed.
Lemma lem5454300 : term445 = True.
Proof. exact (EQ_MP (@lem5454299) (@lem5454297)). Qed.
Lemma lem5454301 : term444 = True.
Proof. exact (TRANS (@lem5454296) (@lem5454300)). Qed.
Lemma lem5454302 : True = term444.
Proof. exact (SYM (@lem5454301)). Qed.
Lemma lem5454303 : term444.
Proof. exact (EQ_MP (@lem5454302) (@lem0)). Qed.
Lemma lem5454304 : term668.
Proof. exact (@lem5454293 (@lem5454303)). Qed.
Lemma lem5454306 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454307 : term444 = term445.
Proof. exact (@lem5454306 (NUMERAL 0) term120). Qed.
Lemma lem5454308 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454309 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454310 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454309 h1) (fun h1 : term445 = True => @lem5454308)). Qed.
Lemma lem5454311 : term445 = True.
Proof. exact (EQ_MP (@lem5454310) (@lem5454308)). Qed.
Lemma lem5454312 : term444 = True.
Proof. exact (TRANS (@lem5454307) (@lem5454311)). Qed.
Lemma lem5454313 : True = term444.
Proof. exact (SYM (@lem5454312)). Qed.
Lemma lem5454314 : term444.
Proof. exact (EQ_MP (@lem5454313) (@lem0)). Qed.
Lemma lem5454315 : term666 = term669.
Proof. exact (@lem5454304 (@lem5454314)). Qed.
Lemma lem5454317 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454318 : term344 = term345.
Proof. exact (@lem5454317 term120 term120). Qed.
Lemma lem5454319 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454320 : term347 = term120.
Proof. exact (EQ_MP (@lem5454319) (@lem940073)). Qed.
Lemma lem5454321 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454322 : term345 = term272.
Proof. exact (MK_COMB (@lem5454321) (@lem5454320)). Qed.
Lemma lem5454323 : term344 = term272.
Proof. exact (TRANS (@lem5454318) (@lem5454322)). Qed.
Lemma lem5454325 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454326 : term456 = term260.
Proof. exact (@lem5454325 term120). Qed.
Lemma lem5454327 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454328 : term670 = term664.
Proof. exact (MK_COMB (@lem5454327) (@lem5454326)). Qed.
Lemma lem5454329 : term669 = term444.
Proof. exact (MK_COMB (@lem5454328) (@lem5454323)). Qed.
Lemma lem5454331 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454332 : term444 = term445.
Proof. exact (@lem5454331 (NUMERAL 0) term120). Qed.
Lemma lem5454333 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454334 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454335 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454334 h1) (fun h1 : term445 = True => @lem5454333)). Qed.
Lemma lem5454336 : term445 = True.
Proof. exact (EQ_MP (@lem5454335) (@lem5454333)). Qed.
Lemma lem5454337 : term444 = True.
Proof. exact (TRANS (@lem5454332) (@lem5454336)). Qed.
Lemma lem5454338 : term669 = True.
Proof. exact (TRANS (@lem5454329) (@lem5454337)). Qed.
Lemma lem5454339 : term666 = True.
Proof. exact (TRANS (@lem5454315) (@lem5454338)). Qed.
Lemma lem5454340 : term444 = True.
Proof. exact (TRANS (@lem5454292) (@lem5454339)). Qed.
Lemma lem5454341 : term663 = True.
Proof. exact (TRANS (@lem5454283) (@lem5454340)). Qed.
Lemma lem5454342 : True = term663.
Proof. exact (SYM (@lem5454341)). Qed.
Lemma lem5454343 : term663.
Proof. exact (EQ_MP (@lem5454342) (@lem0)). Qed.
Lemma lem5454344 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term671 _70532 _70535.
Proof. exact (conj (@lem5454343) (@lem5454278 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454346 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5454347 (_70532 : int) (_70535 : int) : term673 _70532 _70535.
Proof. exact (@lem5454346 term272 (term380 _70532 _70535)). Qed.
Lemma lem5454348 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term674 _70532 _70535.
Proof. exact (@lem5454347 _70532 _70535 (@lem5454344 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454349 (_70532 : int) (_70535 : int) : (term675 _70532 _70535) = (term380 _70532 _70535).
Proof. exact (@lem1982733 (term380 _70532 _70535)). Qed.
Lemma lem5454350 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5454351 (_70532 : int) (_70535 : int) : (term676 _70532 _70535) = (term382 _70532 _70535).
Proof. exact (MK_COMB (@lem5454350) (@lem5454349 _70532 _70535)). Qed.
Lemma lem5454352 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5454353 (_70532 : int) (_70535 : int) : (term674 _70532 _70535) = (term383 _70532 _70535).
Proof. exact (MK_COMB (@lem5454351 _70532 _70535) (@lem5454352)). Qed.
Lemma lem5454354 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term383 _70532 _70535.
Proof. exact (EQ_MP (@lem5454353 _70532 _70535) (@lem5454348 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454356 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5454357 : term663 = term444.
Proof. exact (@lem5454356 term260 term272). Qed.
Lemma lem5454359 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454360 : term272 = term369.
Proof. exact (@lem5454359 term120). Qed.
Lemma lem5454362 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454363 : term260 = term332.
Proof. exact (@lem5454362 (NUMERAL 0)). Qed.
Lemma lem5454364 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454365 : term664 = term665.
Proof. exact (MK_COMB (@lem5454364) (@lem5454363)). Qed.
Lemma lem5454366 : term444 = term666.
Proof. exact (MK_COMB (@lem5454365) (@lem5454360)). Qed.
Lemma lem5454367 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5454369 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454370 : term444 = term445.
Proof. exact (@lem5454369 (NUMERAL 0) term120). Qed.
Lemma lem5454371 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454372 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454373 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454372 h1) (fun h1 : term445 = True => @lem5454371)). Qed.
Lemma lem5454374 : term445 = True.
Proof. exact (EQ_MP (@lem5454373) (@lem5454371)). Qed.
Lemma lem5454375 : term444 = True.
Proof. exact (TRANS (@lem5454370) (@lem5454374)). Qed.
Lemma lem5454376 : True = term444.
Proof. exact (SYM (@lem5454375)). Qed.
Lemma lem5454377 : term444.
Proof. exact (EQ_MP (@lem5454376) (@lem0)). Qed.
Lemma lem5454378 : term668.
Proof. exact (@lem5454367 (@lem5454377)). Qed.
Lemma lem5454380 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454381 : term444 = term445.
Proof. exact (@lem5454380 (NUMERAL 0) term120). Qed.
Lemma lem5454382 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454383 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454384 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454383 h1) (fun h1 : term445 = True => @lem5454382)). Qed.
Lemma lem5454385 : term445 = True.
Proof. exact (EQ_MP (@lem5454384) (@lem5454382)). Qed.
Lemma lem5454386 : term444 = True.
Proof. exact (TRANS (@lem5454381) (@lem5454385)). Qed.
Lemma lem5454387 : True = term444.
Proof. exact (SYM (@lem5454386)). Qed.
Lemma lem5454388 : term444.
Proof. exact (EQ_MP (@lem5454387) (@lem0)). Qed.
Lemma lem5454389 : term666 = term669.
Proof. exact (@lem5454378 (@lem5454388)). Qed.
Lemma lem5454391 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454392 : term344 = term345.
Proof. exact (@lem5454391 term120 term120). Qed.
Lemma lem5454393 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454394 : term347 = term120.
Proof. exact (EQ_MP (@lem5454393) (@lem940073)). Qed.
Lemma lem5454395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454396 : term345 = term272.
Proof. exact (MK_COMB (@lem5454395) (@lem5454394)). Qed.
Lemma lem5454397 : term344 = term272.
Proof. exact (TRANS (@lem5454392) (@lem5454396)). Qed.
Lemma lem5454399 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454400 : term456 = term260.
Proof. exact (@lem5454399 term120). Qed.
Lemma lem5454401 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454402 : term670 = term664.
Proof. exact (MK_COMB (@lem5454401) (@lem5454400)). Qed.
Lemma lem5454403 : term669 = term444.
Proof. exact (MK_COMB (@lem5454402) (@lem5454397)). Qed.
Lemma lem5454405 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454406 : term444 = term445.
Proof. exact (@lem5454405 (NUMERAL 0) term120). Qed.
Lemma lem5454407 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454408 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454409 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454408 h1) (fun h1 : term445 = True => @lem5454407)). Qed.
Lemma lem5454410 : term445 = True.
Proof. exact (EQ_MP (@lem5454409) (@lem5454407)). Qed.
Lemma lem5454411 : term444 = True.
Proof. exact (TRANS (@lem5454406) (@lem5454410)). Qed.
Lemma lem5454412 : term669 = True.
Proof. exact (TRANS (@lem5454403) (@lem5454411)). Qed.
Lemma lem5454413 : term666 = True.
Proof. exact (TRANS (@lem5454389) (@lem5454412)). Qed.
Lemma lem5454414 : term444 = True.
Proof. exact (TRANS (@lem5454366) (@lem5454413)). Qed.
Lemma lem5454415 : term663 = True.
Proof. exact (TRANS (@lem5454357) (@lem5454414)). Qed.
Lemma lem5454416 : True = term663.
Proof. exact (SYM (@lem5454415)). Qed.
Lemma lem5454417 : term663.
Proof. exact (EQ_MP (@lem5454416) (@lem0)). Qed.
Lemma lem5454418 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term677 _70532 _70535.
Proof. exact (conj (@lem5454417) (@lem5454280 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454420 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5454421 (_70532 : int) (_70535 : int) : term678 _70532 _70535.
Proof. exact (@lem5454420 term272 (term405 _70532 _70535)). Qed.
Lemma lem5454422 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term679 _70532 _70535.
Proof. exact (@lem5454421 _70532 _70535 (@lem5454418 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454423 (_70532 : int) (_70535 : int) : (term680 _70532 _70535) = (term405 _70532 _70535).
Proof. exact (@lem1982733 (term405 _70532 _70535)). Qed.
Lemma lem5454424 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5454425 (_70532 : int) (_70535 : int) : (term681 _70532 _70535) = (term407 _70532 _70535).
Proof. exact (MK_COMB (@lem5454424) (@lem5454423 _70532 _70535)). Qed.
Lemma lem5454426 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5454427 (_70532 : int) (_70535 : int) : (term679 _70532 _70535) = (term408 _70532 _70535).
Proof. exact (MK_COMB (@lem5454425 _70532 _70535) (@lem5454426)). Qed.
Lemma lem5454428 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term408 _70532 _70535.
Proof. exact (EQ_MP (@lem5454427 _70532 _70535) (@lem5454422 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454429 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term682 _70532 _70535.
Proof. exact (conj (@lem5454428 _70534 _70532 _70533 _70535 h1) (@lem5454354 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454431 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5454432 (_70532 : int) (_70535 : int) : term684 _70532 _70535.
Proof. exact (@lem5454431 (term405 _70532 _70535) (term380 _70532 _70535)). Qed.
Lemma lem5454433 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term685 _70532 _70535.
Proof. exact (@lem5454432 _70532 _70535 (@lem5454429 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454434 (_70532 : int) (_70535 : int) : (term686 _70532 _70535) = (term687 _70532 _70535).
Proof. exact (@lem1982753 (term360 _70532) (real_of_int _70532) (real_of_int _70535) (term379 _70535)). Qed.
Lemma lem5454435 (_70532 : int) : (term688 _70532) = (term689 _70532).
Proof. exact (@lem1982713 term335 (real_of_int _70532)). Qed.
Lemma lem5454437 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454438 : term272 = term369.
Proof. exact (@lem5454437 term120). Qed.
Lemma lem5454440 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5454441 : term335 = term336.
Proof. exact (@lem5454440 term120). Qed.
Lemma lem5454442 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5454443 : term690 = term691.
Proof. exact (MK_COMB (@lem5454442) (@lem5454441)). Qed.
Lemma lem5454444 : term692 = term693.
Proof. exact (MK_COMB (@lem5454443) (@lem5454438)). Qed.
Lemma lem5454445 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5454447 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454448 : term444 = term445.
Proof. exact (@lem5454447 (NUMERAL 0) term120). Qed.
Lemma lem5454449 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454450 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454451 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454450 h1) (fun h1 : term445 = True => @lem5454449)). Qed.
Lemma lem5454452 : term445 = True.
Proof. exact (EQ_MP (@lem5454451) (@lem5454449)). Qed.
Lemma lem5454453 : term444 = True.
Proof. exact (TRANS (@lem5454448) (@lem5454452)). Qed.
Lemma lem5454454 : True = term444.
Proof. exact (SYM (@lem5454453)). Qed.
Lemma lem5454455 : term444.
Proof. exact (EQ_MP (@lem5454454) (@lem0)). Qed.
Lemma lem5454456 : term695.
Proof. exact (@lem5454445 (@lem5454455)). Qed.
Lemma lem5454458 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454459 : term444 = term445.
Proof. exact (@lem5454458 (NUMERAL 0) term120). Qed.
Lemma lem5454460 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454461 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454462 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454461 h1) (fun h1 : term445 = True => @lem5454460)). Qed.
Lemma lem5454463 : term445 = True.
Proof. exact (EQ_MP (@lem5454462) (@lem5454460)). Qed.
Lemma lem5454464 : term444 = True.
Proof. exact (TRANS (@lem5454459) (@lem5454463)). Qed.
Lemma lem5454465 : True = term444.
Proof. exact (SYM (@lem5454464)). Qed.
Lemma lem5454466 : term444.
Proof. exact (EQ_MP (@lem5454465) (@lem0)). Qed.
Lemma lem5454467 : term696.
Proof. exact (@lem5454456 (@lem5454466)). Qed.
Lemma lem5454469 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454470 : term444 = term445.
Proof. exact (@lem5454469 (NUMERAL 0) term120). Qed.
Lemma lem5454471 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454472 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454473 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454472 h1) (fun h1 : term445 = True => @lem5454471)). Qed.
Lemma lem5454474 : term445 = True.
Proof. exact (EQ_MP (@lem5454473) (@lem5454471)). Qed.
Lemma lem5454475 : term444 = True.
Proof. exact (TRANS (@lem5454470) (@lem5454474)). Qed.
Lemma lem5454476 : True = term444.
Proof. exact (SYM (@lem5454475)). Qed.
Lemma lem5454477 : term444.
Proof. exact (EQ_MP (@lem5454476) (@lem0)). Qed.
Lemma lem5454478 : term697.
Proof. exact (@lem5454467 (@lem5454477)). Qed.
Lemma lem5454480 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454481 : term344 = term345.
Proof. exact (@lem5454480 term120 term120). Qed.
Lemma lem5454482 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454483 : term347 = term120.
Proof. exact (EQ_MP (@lem5454482) (@lem940073)). Qed.
Lemma lem5454484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454485 : term345 = term272.
Proof. exact (MK_COMB (@lem5454484) (@lem5454483)). Qed.
Lemma lem5454486 : term344 = term272.
Proof. exact (TRANS (@lem5454481) (@lem5454485)). Qed.
Lemma lem5454488 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5454489 : term370 = term375.
Proof. exact (@lem5454488 term120 term120). Qed.
Lemma lem5454490 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454491 : term347 = term120.
Proof. exact (EQ_MP (@lem5454490) (@lem940073)). Qed.
Lemma lem5454492 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454493 : term345 = term272.
Proof. exact (MK_COMB (@lem5454492) (@lem5454491)). Qed.
Lemma lem5454494 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5454495 : term375 = term335.
Proof. exact (MK_COMB (@lem5454494) (@lem5454493)). Qed.
Lemma lem5454496 : term370 = term335.
Proof. exact (TRANS (@lem5454489) (@lem5454495)). Qed.
Lemma lem5454497 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5454498 : term698 = term690.
Proof. exact (MK_COMB (@lem5454497) (@lem5454496)). Qed.
Lemma lem5454499 : term699 = term692.
Proof. exact (MK_COMB (@lem5454498) (@lem5454486)). Qed.
Lemma lem5454501 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5454502 : term692 = term260.
Proof. exact (@lem5454501 term120). Qed.
Lemma lem5454503 : term699 = term260.
Proof. exact (TRANS (@lem5454499) (@lem5454502)). Qed.
Lemma lem5454504 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5454505 : term701 = term454.
Proof. exact (MK_COMB (@lem5454504) (@lem5454503)). Qed.
Lemma lem5454506 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5454507 : term702 = term456.
Proof. exact (MK_COMB (@lem5454505) (@lem5454506)). Qed.
Lemma lem5454509 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454510 : term456 = term260.
Proof. exact (@lem5454509 term120). Qed.
Lemma lem5454511 : term702 = term260.
Proof. exact (TRANS (@lem5454507) (@lem5454510)). Qed.
Lemma lem5454513 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454514 : term344 = term345.
Proof. exact (@lem5454513 term120 term120). Qed.
Lemma lem5454515 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454516 : term347 = term120.
Proof. exact (EQ_MP (@lem5454515) (@lem940073)). Qed.
Lemma lem5454517 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454518 : term345 = term272.
Proof. exact (MK_COMB (@lem5454517) (@lem5454516)). Qed.
Lemma lem5454519 : term344 = term272.
Proof. exact (TRANS (@lem5454514) (@lem5454518)). Qed.
Lemma lem5454520 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5454521 : term458 = term456.
Proof. exact (MK_COMB (@lem5454520) (@lem5454519)). Qed.
Lemma lem5454523 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454524 : term456 = term260.
Proof. exact (@lem5454523 term120). Qed.
Lemma lem5454525 : term458 = term260.
Proof. exact (TRANS (@lem5454521) (@lem5454524)). Qed.
Lemma lem5454526 : term260 = term458.
Proof. exact (SYM (@lem5454525)). Qed.
Lemma lem5454527 : term702 = term458.
Proof. exact (TRANS (@lem5454511) (@lem5454526)). Qed.
Lemma lem5454528 : term693 = term332.
Proof. exact (@lem5454478 (@lem5454527)). Qed.
Lemma lem5454529 : term692 = term332.
Proof. exact (TRANS (@lem5454444) (@lem5454528)). Qed.
Lemma lem5454531 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5454532 : term332 = term260.
Proof. exact (@lem5454531 term260). Qed.
Lemma lem5454533 : term692 = term260.
Proof. exact (TRANS (@lem5454529) (@lem5454532)). Qed.
Lemma lem5454534 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5454535 : term703 = term454.
Proof. exact (MK_COMB (@lem5454534) (@lem5454533)). Qed.
Lemma lem5454536 (_70532 : int) : (real_of_int _70532) = (real_of_int _70532).
Proof. exact (eq_refl (real_of_int _70532)). Qed.
Lemma lem5454537 (_70532 : int) : (term689 _70532) = (term704 _70532).
Proof. exact (MK_COMB (@lem5454535) (@lem5454536 _70532)). Qed.
Lemma lem5454538 (_70532 : int) : (term688 _70532) = (term704 _70532).
Proof. exact (TRANS (@lem5454435 _70532) (@lem5454537 _70532)). Qed.
Lemma lem5454539 (_70532 : int) : (term704 _70532) = term260.
Proof. exact (@lem1982719 (real_of_int _70532)). Qed.
Lemma lem5454540 (_70532 : int) : (term688 _70532) = term260.
Proof. exact (TRANS (@lem5454538 _70532) (@lem5454539 _70532)). Qed.
Lemma lem5454541 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5454542 (_70532 : int) : (term705 _70532) = term706.
Proof. exact (MK_COMB (@lem5454541) (@lem5454540 _70532)). Qed.
Lemma lem5454543 (_70535 : int) : (term707 _70535) = (term708 _70535).
Proof. exact (@lem1982763 (real_of_int _70535) (term360 _70535) term335). Qed.
Lemma lem5454544 (_70535 : int) : (term709 _70535) = (term689 _70535).
Proof. exact (@lem1982715 term335 (real_of_int _70535)). Qed.
Lemma lem5454546 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454547 : term272 = term369.
Proof. exact (@lem5454546 term120). Qed.
Lemma lem5454549 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5454550 : term335 = term336.
Proof. exact (@lem5454549 term120). Qed.
Lemma lem5454551 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5454552 : term690 = term691.
Proof. exact (MK_COMB (@lem5454551) (@lem5454550)). Qed.
Lemma lem5454553 : term692 = term693.
Proof. exact (MK_COMB (@lem5454552) (@lem5454547)). Qed.
Lemma lem5454554 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5454556 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454557 : term444 = term445.
Proof. exact (@lem5454556 (NUMERAL 0) term120). Qed.
Lemma lem5454558 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454559 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454560 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454559 h1) (fun h1 : term445 = True => @lem5454558)). Qed.
Lemma lem5454561 : term445 = True.
Proof. exact (EQ_MP (@lem5454560) (@lem5454558)). Qed.
Lemma lem5454562 : term444 = True.
Proof. exact (TRANS (@lem5454557) (@lem5454561)). Qed.
Lemma lem5454563 : True = term444.
Proof. exact (SYM (@lem5454562)). Qed.
Lemma lem5454564 : term444.
Proof. exact (EQ_MP (@lem5454563) (@lem0)). Qed.
Lemma lem5454565 : term695.
Proof. exact (@lem5454554 (@lem5454564)). Qed.
Lemma lem5454567 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454568 : term444 = term445.
Proof. exact (@lem5454567 (NUMERAL 0) term120). Qed.
Lemma lem5454569 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454570 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454571 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454570 h1) (fun h1 : term445 = True => @lem5454569)). Qed.
Lemma lem5454572 : term445 = True.
Proof. exact (EQ_MP (@lem5454571) (@lem5454569)). Qed.
Lemma lem5454573 : term444 = True.
Proof. exact (TRANS (@lem5454568) (@lem5454572)). Qed.
Lemma lem5454574 : True = term444.
Proof. exact (SYM (@lem5454573)). Qed.
Lemma lem5454575 : term444.
Proof. exact (EQ_MP (@lem5454574) (@lem0)). Qed.
Lemma lem5454576 : term696.
Proof. exact (@lem5454565 (@lem5454575)). Qed.
Lemma lem5454578 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454579 : term444 = term445.
Proof. exact (@lem5454578 (NUMERAL 0) term120). Qed.
Lemma lem5454580 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454581 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454582 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454581 h1) (fun h1 : term445 = True => @lem5454580)). Qed.
Lemma lem5454583 : term445 = True.
Proof. exact (EQ_MP (@lem5454582) (@lem5454580)). Qed.
Lemma lem5454584 : term444 = True.
Proof. exact (TRANS (@lem5454579) (@lem5454583)). Qed.
Lemma lem5454585 : True = term444.
Proof. exact (SYM (@lem5454584)). Qed.
Lemma lem5454586 : term444.
Proof. exact (EQ_MP (@lem5454585) (@lem0)). Qed.
Lemma lem5454587 : term697.
Proof. exact (@lem5454576 (@lem5454586)). Qed.
Lemma lem5454589 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454590 : term344 = term345.
Proof. exact (@lem5454589 term120 term120). Qed.
Lemma lem5454591 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454592 : term347 = term120.
Proof. exact (EQ_MP (@lem5454591) (@lem940073)). Qed.
Lemma lem5454593 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454594 : term345 = term272.
Proof. exact (MK_COMB (@lem5454593) (@lem5454592)). Qed.
Lemma lem5454595 : term344 = term272.
Proof. exact (TRANS (@lem5454590) (@lem5454594)). Qed.
Lemma lem5454597 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5454598 : term370 = term375.
Proof. exact (@lem5454597 term120 term120). Qed.
Lemma lem5454599 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454600 : term347 = term120.
Proof. exact (EQ_MP (@lem5454599) (@lem940073)). Qed.
Lemma lem5454601 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454602 : term345 = term272.
Proof. exact (MK_COMB (@lem5454601) (@lem5454600)). Qed.
Lemma lem5454603 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5454604 : term375 = term335.
Proof. exact (MK_COMB (@lem5454603) (@lem5454602)). Qed.
Lemma lem5454605 : term370 = term335.
Proof. exact (TRANS (@lem5454598) (@lem5454604)). Qed.
Lemma lem5454606 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5454607 : term698 = term690.
Proof. exact (MK_COMB (@lem5454606) (@lem5454605)). Qed.
Lemma lem5454608 : term699 = term692.
Proof. exact (MK_COMB (@lem5454607) (@lem5454595)). Qed.
Lemma lem5454610 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5454611 : term692 = term260.
Proof. exact (@lem5454610 term120). Qed.
Lemma lem5454612 : term699 = term260.
Proof. exact (TRANS (@lem5454608) (@lem5454611)). Qed.
Lemma lem5454613 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5454614 : term701 = term454.
Proof. exact (MK_COMB (@lem5454613) (@lem5454612)). Qed.
Lemma lem5454615 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5454616 : term702 = term456.
Proof. exact (MK_COMB (@lem5454614) (@lem5454615)). Qed.
Lemma lem5454618 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454619 : term456 = term260.
Proof. exact (@lem5454618 term120). Qed.
Lemma lem5454620 : term702 = term260.
Proof. exact (TRANS (@lem5454616) (@lem5454619)). Qed.
Lemma lem5454622 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454623 : term344 = term345.
Proof. exact (@lem5454622 term120 term120). Qed.
Lemma lem5454624 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454625 : term347 = term120.
Proof. exact (EQ_MP (@lem5454624) (@lem940073)). Qed.
Lemma lem5454626 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454627 : term345 = term272.
Proof. exact (MK_COMB (@lem5454626) (@lem5454625)). Qed.
Lemma lem5454628 : term344 = term272.
Proof. exact (TRANS (@lem5454623) (@lem5454627)). Qed.
Lemma lem5454629 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5454630 : term458 = term456.
Proof. exact (MK_COMB (@lem5454629) (@lem5454628)). Qed.
Lemma lem5454632 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454633 : term456 = term260.
Proof. exact (@lem5454632 term120). Qed.
Lemma lem5454634 : term458 = term260.
Proof. exact (TRANS (@lem5454630) (@lem5454633)). Qed.
Lemma lem5454635 : term260 = term458.
Proof. exact (SYM (@lem5454634)). Qed.
Lemma lem5454636 : term702 = term458.
Proof. exact (TRANS (@lem5454620) (@lem5454635)). Qed.
Lemma lem5454637 : term693 = term332.
Proof. exact (@lem5454587 (@lem5454636)). Qed.
Lemma lem5454638 : term692 = term332.
Proof. exact (TRANS (@lem5454553) (@lem5454637)). Qed.
Lemma lem5454640 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5454641 : term332 = term260.
Proof. exact (@lem5454640 term260). Qed.
Lemma lem5454642 : term692 = term260.
Proof. exact (TRANS (@lem5454638) (@lem5454641)). Qed.
Lemma lem5454643 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5454644 : term703 = term454.
Proof. exact (MK_COMB (@lem5454643) (@lem5454642)). Qed.
Lemma lem5454645 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5454646 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5454644) (@lem5454645 _70535)). Qed.
Lemma lem5454647 (_70535 : int) : (term709 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5454544 _70535) (@lem5454646 _70535)). Qed.
Lemma lem5454648 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5454649 (_70535 : int) : (term709 _70535) = term260.
Proof. exact (TRANS (@lem5454647 _70535) (@lem5454648 _70535)). Qed.
Lemma lem5454650 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5454651 (_70535 : int) : (term710 _70535) = term706.
Proof. exact (MK_COMB (@lem5454650) (@lem5454649 _70535)). Qed.
Lemma lem5454652 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5454653 (_70535 : int) : (term708 _70535) = term711.
Proof. exact (MK_COMB (@lem5454651 _70535) (@lem5454652)). Qed.
Lemma lem5454654 (_70535 : int) : (term707 _70535) = term711.
Proof. exact (TRANS (@lem5454543 _70535) (@lem5454653 _70535)). Qed.
Lemma lem5454655 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5454656 (_70535 : int) : (term707 _70535) = term335.
Proof. exact (TRANS (@lem5454654 _70535) (@lem5454655)). Qed.
Lemma lem5454657 (_70532 : int) (_70535 : int) : (term687 _70532 _70535) = term711.
Proof. exact (MK_COMB (@lem5454542 _70532) (@lem5454656 _70535)). Qed.
Lemma lem5454658 (_70532 : int) (_70535 : int) : (term686 _70532 _70535) = term711.
Proof. exact (TRANS (@lem5454434 _70532 _70535) (@lem5454657 _70532 _70535)). Qed.
Lemma lem5454659 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5454660 (_70532 : int) (_70535 : int) : (term686 _70532 _70535) = term335.
Proof. exact (TRANS (@lem5454658 _70532 _70535) (@lem5454659)). Qed.
Lemma lem5454661 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5454662 (_70532 : int) (_70535 : int) : (term712 _70532 _70535) = term713.
Proof. exact (MK_COMB (@lem5454661) (@lem5454660 _70532 _70535)). Qed.
Lemma lem5454663 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5454664 (_70532 : int) (_70535 : int) : (term685 _70532 _70535) = term714.
Proof. exact (MK_COMB (@lem5454662 _70532 _70535) (@lem5454663)). Qed.
Lemma lem5454665 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : term714.
Proof. exact (EQ_MP (@lem5454664 _70532 _70535) (@lem5454433 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454667 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5454668 : term714 = term715.
Proof. exact (@lem5454667 term260 term335). Qed.
Lemma lem5454670 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5454671 : term335 = term336.
Proof. exact (@lem5454670 term120). Qed.
Lemma lem5454673 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454674 : term260 = term332.
Proof. exact (@lem5454673 (NUMERAL 0)). Qed.
Lemma lem5454675 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5454676 : term262 = term716.
Proof. exact (MK_COMB (@lem5454675) (@lem5454674)). Qed.
Lemma lem5454677 : term715 = term717.
Proof. exact (MK_COMB (@lem5454676) (@lem5454671)). Qed.
Lemma lem5454678 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5454680 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454681 : term444 = term445.
Proof. exact (@lem5454680 (NUMERAL 0) term120). Qed.
Lemma lem5454682 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454683 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454684 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454683 h1) (fun h1 : term445 = True => @lem5454682)). Qed.
Lemma lem5454685 : term445 = True.
Proof. exact (EQ_MP (@lem5454684) (@lem5454682)). Qed.
Lemma lem5454686 : term444 = True.
Proof. exact (TRANS (@lem5454681) (@lem5454685)). Qed.
Lemma lem5454687 : True = term444.
Proof. exact (SYM (@lem5454686)). Qed.
Lemma lem5454688 : term444.
Proof. exact (EQ_MP (@lem5454687) (@lem0)). Qed.
Lemma lem5454689 : term719.
Proof. exact (@lem5454678 (@lem5454688)). Qed.
Lemma lem5454691 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454692 : term444 = term445.
Proof. exact (@lem5454691 (NUMERAL 0) term120). Qed.
Lemma lem5454693 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454694 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454695 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454694 h1) (fun h1 : term445 = True => @lem5454693)). Qed.
Lemma lem5454696 : term445 = True.
Proof. exact (EQ_MP (@lem5454695) (@lem5454693)). Qed.
Lemma lem5454697 : term444 = True.
Proof. exact (TRANS (@lem5454692) (@lem5454696)). Qed.
Lemma lem5454698 : True = term444.
Proof. exact (SYM (@lem5454697)). Qed.
Lemma lem5454699 : term444.
Proof. exact (EQ_MP (@lem5454698) (@lem0)). Qed.
Lemma lem5454700 : term717 = term720.
Proof. exact (@lem5454689 (@lem5454699)). Qed.
Lemma lem5454702 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5454703 : term370 = term375.
Proof. exact (@lem5454702 term120 term120). Qed.
Lemma lem5454704 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454705 : term347 = term120.
Proof. exact (EQ_MP (@lem5454704) (@lem940073)). Qed.
Lemma lem5454706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454707 : term345 = term272.
Proof. exact (MK_COMB (@lem5454706) (@lem5454705)). Qed.
Lemma lem5454708 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5454709 : term375 = term335.
Proof. exact (MK_COMB (@lem5454708) (@lem5454707)). Qed.
Lemma lem5454710 : term370 = term335.
Proof. exact (TRANS (@lem5454703) (@lem5454709)). Qed.
Lemma lem5454712 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454713 : term456 = term260.
Proof. exact (@lem5454712 term120). Qed.
Lemma lem5454714 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5454715 : term721 = term262.
Proof. exact (MK_COMB (@lem5454714) (@lem5454713)). Qed.
Lemma lem5454716 : term720 = term715.
Proof. exact (MK_COMB (@lem5454715) (@lem5454710)). Qed.
Lemma lem5454718 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5454719 : term715 = term724.
Proof. exact (@lem5454718 (NUMERAL 0) term120). Qed.
Lemma lem5454720 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454721 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5454722 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454721 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5454720)). Qed.
Lemma lem5454723 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5454722) (@lem5454720)). Qed.
Lemma lem5454724 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5454725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5454726 : term725 = (and True).
Proof. exact (MK_COMB (@lem5454725) (@lem5454724)). Qed.
Lemma lem5454727 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5454726) (@lem5454723)). Qed.
Lemma lem5454729 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5454730 : term724 = False.
Proof. exact (TRANS (@lem5454727) (@lem5454729)). Qed.
Lemma lem5454731 : term715 = False.
Proof. exact (TRANS (@lem5454719) (@lem5454730)). Qed.
Lemma lem5454732 : term720 = False.
Proof. exact (TRANS (@lem5454716) (@lem5454731)). Qed.
Lemma lem5454733 : term717 = False.
Proof. exact (TRANS (@lem5454700) (@lem5454732)). Qed.
Lemma lem5454734 : term715 = False.
Proof. exact (TRANS (@lem5454677) (@lem5454733)). Qed.
Lemma lem5454735 : term714 = False.
Proof. exact (TRANS (@lem5454668) (@lem5454734)). Qed.
Lemma lem5454736 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term662 _70534 _70532 _70533 _70535) : False.
Proof. exact (EQ_MP (@lem5454735) (@lem5454665 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454737 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term726 _70534 _70532 _70533 _70535.
Proof. exact (h1). Qed.
Lemma lem5454738 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term655 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454737 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454740 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term624 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454738 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454742 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term593 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454740 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454743 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term355 _70534.
Proof. exact (proj1 (@lem5454740 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454744 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term562 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454742 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454746 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term531 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454744 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454748 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term412 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5454746 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454749 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term399 _70533 _70534 _70535.
Proof. exact (proj1 (@lem5454746 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454750 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term410 _70533 _70535.
Proof. exact (proj2 (@lem5454748 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454753 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5454754 : term663 = term444.
Proof. exact (@lem5454753 term260 term272). Qed.
Lemma lem5454756 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454757 : term272 = term369.
Proof. exact (@lem5454756 term120). Qed.
Lemma lem5454759 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454760 : term260 = term332.
Proof. exact (@lem5454759 (NUMERAL 0)). Qed.
Lemma lem5454761 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454762 : term664 = term665.
Proof. exact (MK_COMB (@lem5454761) (@lem5454760)). Qed.
Lemma lem5454763 : term444 = term666.
Proof. exact (MK_COMB (@lem5454762) (@lem5454757)). Qed.
Lemma lem5454764 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5454766 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454767 : term444 = term445.
Proof. exact (@lem5454766 (NUMERAL 0) term120). Qed.
Lemma lem5454768 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454769 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454770 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454769 h1) (fun h1 : term445 = True => @lem5454768)). Qed.
Lemma lem5454771 : term445 = True.
Proof. exact (EQ_MP (@lem5454770) (@lem5454768)). Qed.
Lemma lem5454772 : term444 = True.
Proof. exact (TRANS (@lem5454767) (@lem5454771)). Qed.
Lemma lem5454773 : True = term444.
Proof. exact (SYM (@lem5454772)). Qed.
Lemma lem5454774 : term444.
Proof. exact (EQ_MP (@lem5454773) (@lem0)). Qed.
Lemma lem5454775 : term668.
Proof. exact (@lem5454764 (@lem5454774)). Qed.
Lemma lem5454777 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454778 : term444 = term445.
Proof. exact (@lem5454777 (NUMERAL 0) term120). Qed.
Lemma lem5454779 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454780 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454781 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454780 h1) (fun h1 : term445 = True => @lem5454779)). Qed.
Lemma lem5454782 : term445 = True.
Proof. exact (EQ_MP (@lem5454781) (@lem5454779)). Qed.
Lemma lem5454783 : term444 = True.
Proof. exact (TRANS (@lem5454778) (@lem5454782)). Qed.
Lemma lem5454784 : True = term444.
Proof. exact (SYM (@lem5454783)). Qed.
Lemma lem5454785 : term444.
Proof. exact (EQ_MP (@lem5454784) (@lem0)). Qed.
Lemma lem5454786 : term666 = term669.
Proof. exact (@lem5454775 (@lem5454785)). Qed.
Lemma lem5454788 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454789 : term344 = term345.
Proof. exact (@lem5454788 term120 term120). Qed.
Lemma lem5454790 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454791 : term347 = term120.
Proof. exact (EQ_MP (@lem5454790) (@lem940073)). Qed.
Lemma lem5454792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454793 : term345 = term272.
Proof. exact (MK_COMB (@lem5454792) (@lem5454791)). Qed.
Lemma lem5454794 : term344 = term272.
Proof. exact (TRANS (@lem5454789) (@lem5454793)). Qed.
Lemma lem5454796 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454797 : term456 = term260.
Proof. exact (@lem5454796 term120). Qed.
Lemma lem5454798 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454799 : term670 = term664.
Proof. exact (MK_COMB (@lem5454798) (@lem5454797)). Qed.
Lemma lem5454800 : term669 = term444.
Proof. exact (MK_COMB (@lem5454799) (@lem5454794)). Qed.
Lemma lem5454802 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454803 : term444 = term445.
Proof. exact (@lem5454802 (NUMERAL 0) term120). Qed.
Lemma lem5454804 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454805 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454806 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454805 h1) (fun h1 : term445 = True => @lem5454804)). Qed.
Lemma lem5454807 : term445 = True.
Proof. exact (EQ_MP (@lem5454806) (@lem5454804)). Qed.
Lemma lem5454808 : term444 = True.
Proof. exact (TRANS (@lem5454803) (@lem5454807)). Qed.
Lemma lem5454809 : term669 = True.
Proof. exact (TRANS (@lem5454800) (@lem5454808)). Qed.
Lemma lem5454810 : term666 = True.
Proof. exact (TRANS (@lem5454786) (@lem5454809)). Qed.
Lemma lem5454811 : term444 = True.
Proof. exact (TRANS (@lem5454763) (@lem5454810)). Qed.
Lemma lem5454812 : term663 = True.
Proof. exact (TRANS (@lem5454754) (@lem5454811)). Qed.
Lemma lem5454813 : True = term663.
Proof. exact (SYM (@lem5454812)). Qed.
Lemma lem5454814 : term663.
Proof. exact (EQ_MP (@lem5454813) (@lem0)). Qed.
Lemma lem5454815 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term727 _70533 _70535.
Proof. exact (conj (@lem5454814) (@lem5454750 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454817 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5454818 (_70533 : int) (_70535 : int) : term728 _70533 _70535.
Proof. exact (@lem5454817 term272 (term404 _70533 _70535)). Qed.
Lemma lem5454819 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term729 _70533 _70535.
Proof. exact (@lem5454818 _70533 _70535 (@lem5454815 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454820 (_70533 : int) (_70535 : int) : (term730 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (@lem1982733 (term404 _70533 _70535)). Qed.
Lemma lem5454821 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5454822 (_70533 : int) (_70535 : int) : (term731 _70533 _70535) = (term409 _70533 _70535).
Proof. exact (MK_COMB (@lem5454821) (@lem5454820 _70533 _70535)). Qed.
Lemma lem5454823 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5454824 (_70533 : int) (_70535 : int) : (term729 _70533 _70535) = (term410 _70533 _70535).
Proof. exact (MK_COMB (@lem5454822 _70533 _70535) (@lem5454823)). Qed.
Lemma lem5454825 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term410 _70533 _70535.
Proof. exact (EQ_MP (@lem5454824 _70533 _70535) (@lem5454819 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454827 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5454828 : term663 = term444.
Proof. exact (@lem5454827 term260 term272). Qed.
Lemma lem5454830 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454831 : term272 = term369.
Proof. exact (@lem5454830 term120). Qed.
Lemma lem5454833 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454834 : term260 = term332.
Proof. exact (@lem5454833 (NUMERAL 0)). Qed.
Lemma lem5454835 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454836 : term664 = term665.
Proof. exact (MK_COMB (@lem5454835) (@lem5454834)). Qed.
Lemma lem5454837 : term444 = term666.
Proof. exact (MK_COMB (@lem5454836) (@lem5454831)). Qed.
Lemma lem5454838 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5454840 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454841 : term444 = term445.
Proof. exact (@lem5454840 (NUMERAL 0) term120). Qed.
Lemma lem5454842 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454843 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454844 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454843 h1) (fun h1 : term445 = True => @lem5454842)). Qed.
Lemma lem5454845 : term445 = True.
Proof. exact (EQ_MP (@lem5454844) (@lem5454842)). Qed.
Lemma lem5454846 : term444 = True.
Proof. exact (TRANS (@lem5454841) (@lem5454845)). Qed.
Lemma lem5454847 : True = term444.
Proof. exact (SYM (@lem5454846)). Qed.
Lemma lem5454848 : term444.
Proof. exact (EQ_MP (@lem5454847) (@lem0)). Qed.
Lemma lem5454849 : term668.
Proof. exact (@lem5454838 (@lem5454848)). Qed.
Lemma lem5454851 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454852 : term444 = term445.
Proof. exact (@lem5454851 (NUMERAL 0) term120). Qed.
Lemma lem5454853 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454854 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454855 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454854 h1) (fun h1 : term445 = True => @lem5454853)). Qed.
Lemma lem5454856 : term445 = True.
Proof. exact (EQ_MP (@lem5454855) (@lem5454853)). Qed.
Lemma lem5454857 : term444 = True.
Proof. exact (TRANS (@lem5454852) (@lem5454856)). Qed.
Lemma lem5454858 : True = term444.
Proof. exact (SYM (@lem5454857)). Qed.
Lemma lem5454859 : term444.
Proof. exact (EQ_MP (@lem5454858) (@lem0)). Qed.
Lemma lem5454860 : term666 = term669.
Proof. exact (@lem5454849 (@lem5454859)). Qed.
Lemma lem5454862 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454863 : term344 = term345.
Proof. exact (@lem5454862 term120 term120). Qed.
Lemma lem5454864 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454865 : term347 = term120.
Proof. exact (EQ_MP (@lem5454864) (@lem940073)). Qed.
Lemma lem5454866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454867 : term345 = term272.
Proof. exact (MK_COMB (@lem5454866) (@lem5454865)). Qed.
Lemma lem5454868 : term344 = term272.
Proof. exact (TRANS (@lem5454863) (@lem5454867)). Qed.
Lemma lem5454870 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454871 : term456 = term260.
Proof. exact (@lem5454870 term120). Qed.
Lemma lem5454872 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454873 : term670 = term664.
Proof. exact (MK_COMB (@lem5454872) (@lem5454871)). Qed.
Lemma lem5454874 : term669 = term444.
Proof. exact (MK_COMB (@lem5454873) (@lem5454868)). Qed.
Lemma lem5454876 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454877 : term444 = term445.
Proof. exact (@lem5454876 (NUMERAL 0) term120). Qed.
Lemma lem5454878 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454879 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454880 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454879 h1) (fun h1 : term445 = True => @lem5454878)). Qed.
Lemma lem5454881 : term445 = True.
Proof. exact (EQ_MP (@lem5454880) (@lem5454878)). Qed.
Lemma lem5454882 : term444 = True.
Proof. exact (TRANS (@lem5454877) (@lem5454881)). Qed.
Lemma lem5454883 : term669 = True.
Proof. exact (TRANS (@lem5454874) (@lem5454882)). Qed.
Lemma lem5454884 : term666 = True.
Proof. exact (TRANS (@lem5454860) (@lem5454883)). Qed.
Lemma lem5454885 : term444 = True.
Proof. exact (TRANS (@lem5454837) (@lem5454884)). Qed.
Lemma lem5454886 : term663 = True.
Proof. exact (TRANS (@lem5454828) (@lem5454885)). Qed.
Lemma lem5454887 : True = term663.
Proof. exact (SYM (@lem5454886)). Qed.
Lemma lem5454888 : term663.
Proof. exact (EQ_MP (@lem5454887) (@lem0)). Qed.
Lemma lem5454889 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term732 _70534.
Proof. exact (conj (@lem5454888) (@lem5454743 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454891 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5454892 (_70534 : int) : term733 _70534.
Proof. exact (@lem5454891 term272 (real_of_int _70534)). Qed.
Lemma lem5454893 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term734 _70534.
Proof. exact (@lem5454892 _70534 (@lem5454889 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454894 (_70534 : int) : (term735 _70534) = (real_of_int _70534).
Proof. exact (@lem1982733 (real_of_int _70534)). Qed.
Lemma lem5454895 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5454896 (_70534 : int) : (term736 _70534) = (term354 _70534).
Proof. exact (MK_COMB (@lem5454895) (@lem5454894 _70534)). Qed.
Lemma lem5454897 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5454898 (_70534 : int) : (term734 _70534) = (term355 _70534).
Proof. exact (MK_COMB (@lem5454896 _70534) (@lem5454897)). Qed.
Lemma lem5454899 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term355 _70534.
Proof. exact (EQ_MP (@lem5454898 _70534) (@lem5454893 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454901 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5454902 : term663 = term444.
Proof. exact (@lem5454901 term260 term272). Qed.
Lemma lem5454904 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454905 : term272 = term369.
Proof. exact (@lem5454904 term120). Qed.
Lemma lem5454907 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454908 : term260 = term332.
Proof. exact (@lem5454907 (NUMERAL 0)). Qed.
Lemma lem5454909 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454910 : term664 = term665.
Proof. exact (MK_COMB (@lem5454909) (@lem5454908)). Qed.
Lemma lem5454911 : term444 = term666.
Proof. exact (MK_COMB (@lem5454910) (@lem5454905)). Qed.
Lemma lem5454912 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5454914 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454915 : term444 = term445.
Proof. exact (@lem5454914 (NUMERAL 0) term120). Qed.
Lemma lem5454916 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454917 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454918 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454917 h1) (fun h1 : term445 = True => @lem5454916)). Qed.
Lemma lem5454919 : term445 = True.
Proof. exact (EQ_MP (@lem5454918) (@lem5454916)). Qed.
Lemma lem5454920 : term444 = True.
Proof. exact (TRANS (@lem5454915) (@lem5454919)). Qed.
Lemma lem5454921 : True = term444.
Proof. exact (SYM (@lem5454920)). Qed.
Lemma lem5454922 : term444.
Proof. exact (EQ_MP (@lem5454921) (@lem0)). Qed.
Lemma lem5454923 : term668.
Proof. exact (@lem5454912 (@lem5454922)). Qed.
Lemma lem5454925 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454926 : term444 = term445.
Proof. exact (@lem5454925 (NUMERAL 0) term120). Qed.
Lemma lem5454927 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454928 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454929 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454928 h1) (fun h1 : term445 = True => @lem5454927)). Qed.
Lemma lem5454930 : term445 = True.
Proof. exact (EQ_MP (@lem5454929) (@lem5454927)). Qed.
Lemma lem5454931 : term444 = True.
Proof. exact (TRANS (@lem5454926) (@lem5454930)). Qed.
Lemma lem5454932 : True = term444.
Proof. exact (SYM (@lem5454931)). Qed.
Lemma lem5454933 : term444.
Proof. exact (EQ_MP (@lem5454932) (@lem0)). Qed.
Lemma lem5454934 : term666 = term669.
Proof. exact (@lem5454923 (@lem5454933)). Qed.
Lemma lem5454936 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5454937 : term344 = term345.
Proof. exact (@lem5454936 term120 term120). Qed.
Lemma lem5454938 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5454939 : term347 = term120.
Proof. exact (EQ_MP (@lem5454938) (@lem940073)). Qed.
Lemma lem5454940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5454941 : term345 = term272.
Proof. exact (MK_COMB (@lem5454940) (@lem5454939)). Qed.
Lemma lem5454942 : term344 = term272.
Proof. exact (TRANS (@lem5454937) (@lem5454941)). Qed.
Lemma lem5454944 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5454945 : term456 = term260.
Proof. exact (@lem5454944 term120). Qed.
Lemma lem5454946 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5454947 : term670 = term664.
Proof. exact (MK_COMB (@lem5454946) (@lem5454945)). Qed.
Lemma lem5454948 : term669 = term444.
Proof. exact (MK_COMB (@lem5454947) (@lem5454942)). Qed.
Lemma lem5454950 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454951 : term444 = term445.
Proof. exact (@lem5454950 (NUMERAL 0) term120). Qed.
Lemma lem5454952 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454953 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454954 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454953 h1) (fun h1 : term445 = True => @lem5454952)). Qed.
Lemma lem5454955 : term445 = True.
Proof. exact (EQ_MP (@lem5454954) (@lem5454952)). Qed.
Lemma lem5454956 : term444 = True.
Proof. exact (TRANS (@lem5454951) (@lem5454955)). Qed.
Lemma lem5454957 : term669 = True.
Proof. exact (TRANS (@lem5454948) (@lem5454956)). Qed.
Lemma lem5454958 : term666 = True.
Proof. exact (TRANS (@lem5454934) (@lem5454957)). Qed.
Lemma lem5454959 : term444 = True.
Proof. exact (TRANS (@lem5454911) (@lem5454958)). Qed.
Lemma lem5454960 : term663 = True.
Proof. exact (TRANS (@lem5454902) (@lem5454959)). Qed.
Lemma lem5454961 : True = term663.
Proof. exact (SYM (@lem5454960)). Qed.
Lemma lem5454962 : term663.
Proof. exact (EQ_MP (@lem5454961) (@lem0)). Qed.
Lemma lem5454963 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term737 _70533 _70534 _70535.
Proof. exact (conj (@lem5454962) (@lem5454749 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454965 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5454966 (_70533 : int) (_70534 : int) (_70535 : int) : term738 _70533 _70534 _70535.
Proof. exact (@lem5454965 term272 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5454967 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term739 _70533 _70534 _70535.
Proof. exact (@lem5454966 _70533 _70534 _70535 (@lem5454963 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454968 (_70533 : int) (_70534 : int) (_70535 : int) : (term740 _70533 _70534 _70535) = (term396 _70533 _70534 _70535).
Proof. exact (@lem1982733 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5454969 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5454970 (_70533 : int) (_70534 : int) (_70535 : int) : (term741 _70533 _70534 _70535) = (term398 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454969) (@lem5454968 _70533 _70534 _70535)). Qed.
Lemma lem5454971 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5454972 (_70533 : int) (_70534 : int) (_70535 : int) : (term739 _70533 _70534 _70535) = (term399 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5454970 _70533 _70534 _70535) (@lem5454971)). Qed.
Lemma lem5454973 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term399 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5454972 _70533 _70534 _70535) (@lem5454967 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454974 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term742 _70533 _70535 _70534.
Proof. exact (conj (@lem5454973 _70534 _70532 _70533 _70535 h1) (@lem5454899 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454976 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5454977 (_70533 : int) (_70535 : int) (_70534 : int) : term743 _70533 _70535 _70534.
Proof. exact (@lem5454976 (term396 _70533 _70534 _70535) (real_of_int _70534)). Qed.
Lemma lem5454978 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term744 _70533 _70535 _70534.
Proof. exact (@lem5454977 _70533 _70535 _70534 (@lem5454974 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5454979 (_70533 : int) (_70535 : int) (_70534 : int) : (term745 _70533 _70535 _70534) = (term746 _70533 _70535 _70534).
Proof. exact (@lem1982755 (term360 _70533) (term395 _70534 _70535) (real_of_int _70534)). Qed.
Lemma lem5454980 (_70534 : int) (_70535 : int) : (term747 _70535 _70534) = (term748 _70534 _70535).
Proof. exact (@lem1982759 (term360 _70534) (real_of_int _70534) (term749 _70535)). Qed.
Lemma lem5454981 (_70534 : int) : (term688 _70534) = (term689 _70534).
Proof. exact (@lem1982713 term335 (real_of_int _70534)). Qed.
Lemma lem5454983 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5454984 : term272 = term369.
Proof. exact (@lem5454983 term120). Qed.
Lemma lem5454986 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5454987 : term335 = term336.
Proof. exact (@lem5454986 term120). Qed.
Lemma lem5454988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5454989 : term690 = term691.
Proof. exact (MK_COMB (@lem5454988) (@lem5454987)). Qed.
Lemma lem5454990 : term692 = term693.
Proof. exact (MK_COMB (@lem5454989) (@lem5454984)). Qed.
Lemma lem5454991 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5454993 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5454994 : term444 = term445.
Proof. exact (@lem5454993 (NUMERAL 0) term120). Qed.
Lemma lem5454995 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5454996 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5454997 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5454996 h1) (fun h1 : term445 = True => @lem5454995)). Qed.
Lemma lem5454998 : term445 = True.
Proof. exact (EQ_MP (@lem5454997) (@lem5454995)). Qed.
Lemma lem5454999 : term444 = True.
Proof. exact (TRANS (@lem5454994) (@lem5454998)). Qed.
Lemma lem5455000 : True = term444.
Proof. exact (SYM (@lem5454999)). Qed.
Lemma lem5455001 : term444.
Proof. exact (EQ_MP (@lem5455000) (@lem0)). Qed.
Lemma lem5455002 : term695.
Proof. exact (@lem5454991 (@lem5455001)). Qed.
Lemma lem5455004 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455005 : term444 = term445.
Proof. exact (@lem5455004 (NUMERAL 0) term120). Qed.
Lemma lem5455006 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455007 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455008 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455007 h1) (fun h1 : term445 = True => @lem5455006)). Qed.
Lemma lem5455009 : term445 = True.
Proof. exact (EQ_MP (@lem5455008) (@lem5455006)). Qed.
Lemma lem5455010 : term444 = True.
Proof. exact (TRANS (@lem5455005) (@lem5455009)). Qed.
Lemma lem5455011 : True = term444.
Proof. exact (SYM (@lem5455010)). Qed.
Lemma lem5455012 : term444.
Proof. exact (EQ_MP (@lem5455011) (@lem0)). Qed.
Lemma lem5455013 : term696.
Proof. exact (@lem5455002 (@lem5455012)). Qed.
Lemma lem5455015 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455016 : term444 = term445.
Proof. exact (@lem5455015 (NUMERAL 0) term120). Qed.
Lemma lem5455017 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455018 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455019 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455018 h1) (fun h1 : term445 = True => @lem5455017)). Qed.
Lemma lem5455020 : term445 = True.
Proof. exact (EQ_MP (@lem5455019) (@lem5455017)). Qed.
Lemma lem5455021 : term444 = True.
Proof. exact (TRANS (@lem5455016) (@lem5455020)). Qed.
Lemma lem5455022 : True = term444.
Proof. exact (SYM (@lem5455021)). Qed.
Lemma lem5455023 : term444.
Proof. exact (EQ_MP (@lem5455022) (@lem0)). Qed.
Lemma lem5455024 : term697.
Proof. exact (@lem5455013 (@lem5455023)). Qed.
Lemma lem5455026 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455027 : term344 = term345.
Proof. exact (@lem5455026 term120 term120). Qed.
Lemma lem5455028 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455029 : term347 = term120.
Proof. exact (EQ_MP (@lem5455028) (@lem940073)). Qed.
Lemma lem5455030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455031 : term345 = term272.
Proof. exact (MK_COMB (@lem5455030) (@lem5455029)). Qed.
Lemma lem5455032 : term344 = term272.
Proof. exact (TRANS (@lem5455027) (@lem5455031)). Qed.
Lemma lem5455034 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5455035 : term370 = term375.
Proof. exact (@lem5455034 term120 term120). Qed.
Lemma lem5455036 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455037 : term347 = term120.
Proof. exact (EQ_MP (@lem5455036) (@lem940073)). Qed.
Lemma lem5455038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455039 : term345 = term272.
Proof. exact (MK_COMB (@lem5455038) (@lem5455037)). Qed.
Lemma lem5455040 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5455041 : term375 = term335.
Proof. exact (MK_COMB (@lem5455040) (@lem5455039)). Qed.
Lemma lem5455042 : term370 = term335.
Proof. exact (TRANS (@lem5455035) (@lem5455041)). Qed.
Lemma lem5455043 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455044 : term698 = term690.
Proof. exact (MK_COMB (@lem5455043) (@lem5455042)). Qed.
Lemma lem5455045 : term699 = term692.
Proof. exact (MK_COMB (@lem5455044) (@lem5455032)). Qed.
Lemma lem5455047 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5455048 : term692 = term260.
Proof. exact (@lem5455047 term120). Qed.
Lemma lem5455049 : term699 = term260.
Proof. exact (TRANS (@lem5455045) (@lem5455048)). Qed.
Lemma lem5455050 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455051 : term701 = term454.
Proof. exact (MK_COMB (@lem5455050) (@lem5455049)). Qed.
Lemma lem5455052 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5455053 : term702 = term456.
Proof. exact (MK_COMB (@lem5455051) (@lem5455052)). Qed.
Lemma lem5455055 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455056 : term456 = term260.
Proof. exact (@lem5455055 term120). Qed.
Lemma lem5455057 : term702 = term260.
Proof. exact (TRANS (@lem5455053) (@lem5455056)). Qed.
Lemma lem5455059 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455060 : term344 = term345.
Proof. exact (@lem5455059 term120 term120). Qed.
Lemma lem5455061 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455062 : term347 = term120.
Proof. exact (EQ_MP (@lem5455061) (@lem940073)). Qed.
Lemma lem5455063 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455064 : term345 = term272.
Proof. exact (MK_COMB (@lem5455063) (@lem5455062)). Qed.
Lemma lem5455065 : term344 = term272.
Proof. exact (TRANS (@lem5455060) (@lem5455064)). Qed.
Lemma lem5455066 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5455067 : term458 = term456.
Proof. exact (MK_COMB (@lem5455066) (@lem5455065)). Qed.
Lemma lem5455069 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455070 : term456 = term260.
Proof. exact (@lem5455069 term120). Qed.
Lemma lem5455071 : term458 = term260.
Proof. exact (TRANS (@lem5455067) (@lem5455070)). Qed.
Lemma lem5455072 : term260 = term458.
Proof. exact (SYM (@lem5455071)). Qed.
Lemma lem5455073 : term702 = term458.
Proof. exact (TRANS (@lem5455057) (@lem5455072)). Qed.
Lemma lem5455074 : term693 = term332.
Proof. exact (@lem5455024 (@lem5455073)). Qed.
Lemma lem5455075 : term692 = term332.
Proof. exact (TRANS (@lem5454990) (@lem5455074)). Qed.
Lemma lem5455077 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5455078 : term332 = term260.
Proof. exact (@lem5455077 term260). Qed.
Lemma lem5455079 : term692 = term260.
Proof. exact (TRANS (@lem5455075) (@lem5455078)). Qed.
Lemma lem5455080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455081 : term703 = term454.
Proof. exact (MK_COMB (@lem5455080) (@lem5455079)). Qed.
Lemma lem5455082 (_70534 : int) : (real_of_int _70534) = (real_of_int _70534).
Proof. exact (eq_refl (real_of_int _70534)). Qed.
Lemma lem5455083 (_70534 : int) : (term689 _70534) = (term704 _70534).
Proof. exact (MK_COMB (@lem5455081) (@lem5455082 _70534)). Qed.
Lemma lem5455084 (_70534 : int) : (term688 _70534) = (term704 _70534).
Proof. exact (TRANS (@lem5454981 _70534) (@lem5455083 _70534)). Qed.
Lemma lem5455085 (_70534 : int) : (term704 _70534) = term260.
Proof. exact (@lem1982719 (real_of_int _70534)). Qed.
Lemma lem5455086 (_70534 : int) : (term688 _70534) = term260.
Proof. exact (TRANS (@lem5455084 _70534) (@lem5455085 _70534)). Qed.
Lemma lem5455087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455088 (_70534 : int) : (term705 _70534) = term706.
Proof. exact (MK_COMB (@lem5455087) (@lem5455086 _70534)). Qed.
Lemma lem5455089 (_70535 : int) : (term749 _70535) = (term749 _70535).
Proof. exact (eq_refl (term749 _70535)). Qed.
Lemma lem5455090 (_70534 : int) (_70535 : int) : (term748 _70534 _70535) = (term750 _70535).
Proof. exact (MK_COMB (@lem5455088 _70534) (@lem5455089 _70535)). Qed.
Lemma lem5455091 (_70534 : int) (_70535 : int) : (term747 _70535 _70534) = (term750 _70535).
Proof. exact (TRANS (@lem5454980 _70534 _70535) (@lem5455090 _70534 _70535)). Qed.
Lemma lem5455092 (_70535 : int) : (term750 _70535) = (term749 _70535).
Proof. exact (@lem1982721 (term749 _70535)). Qed.
Lemma lem5455093 (_70534 : int) (_70535 : int) : (term747 _70535 _70534) = (term749 _70535).
Proof. exact (TRANS (@lem5455091 _70534 _70535) (@lem5455092 _70535)). Qed.
Lemma lem5455094 (_70533 : int) : (term378 _70533) = (term378 _70533).
Proof. exact (eq_refl (term378 _70533)). Qed.
Lemma lem5455095 (_70534 : int) (_70533 : int) (_70535 : int) : (term746 _70533 _70535 _70534) = (term395 _70533 _70535).
Proof. exact (MK_COMB (@lem5455094 _70533) (@lem5455093 _70534 _70535)). Qed.
Lemma lem5455096 (_70534 : int) (_70533 : int) (_70535 : int) : (term745 _70533 _70535 _70534) = (term395 _70533 _70535).
Proof. exact (TRANS (@lem5454979 _70533 _70535 _70534) (@lem5455095 _70534 _70533 _70535)). Qed.
Lemma lem5455097 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5455098 (_70534 : int) (_70533 : int) (_70535 : int) : (term751 _70533 _70535 _70534) = (term413 _70533 _70535).
Proof. exact (MK_COMB (@lem5455097) (@lem5455096 _70534 _70533 _70535)). Qed.
Lemma lem5455099 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5455100 (_70534 : int) (_70533 : int) (_70535 : int) : (term744 _70533 _70535 _70534) = (term414 _70533 _70535).
Proof. exact (MK_COMB (@lem5455098 _70534 _70533 _70535) (@lem5455099)). Qed.
Lemma lem5455101 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term414 _70533 _70535.
Proof. exact (EQ_MP (@lem5455100 _70534 _70533 _70535) (@lem5454978 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455103 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5455104 : term663 = term444.
Proof. exact (@lem5455103 term260 term272). Qed.
Lemma lem5455106 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455107 : term272 = term369.
Proof. exact (@lem5455106 term120). Qed.
Lemma lem5455109 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455110 : term260 = term332.
Proof. exact (@lem5455109 (NUMERAL 0)). Qed.
Lemma lem5455111 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455112 : term664 = term665.
Proof. exact (MK_COMB (@lem5455111) (@lem5455110)). Qed.
Lemma lem5455113 : term444 = term666.
Proof. exact (MK_COMB (@lem5455112) (@lem5455107)). Qed.
Lemma lem5455114 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5455116 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455117 : term444 = term445.
Proof. exact (@lem5455116 (NUMERAL 0) term120). Qed.
Lemma lem5455118 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455119 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455120 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455119 h1) (fun h1 : term445 = True => @lem5455118)). Qed.
Lemma lem5455121 : term445 = True.
Proof. exact (EQ_MP (@lem5455120) (@lem5455118)). Qed.
Lemma lem5455122 : term444 = True.
Proof. exact (TRANS (@lem5455117) (@lem5455121)). Qed.
Lemma lem5455123 : True = term444.
Proof. exact (SYM (@lem5455122)). Qed.
Lemma lem5455124 : term444.
Proof. exact (EQ_MP (@lem5455123) (@lem0)). Qed.
Lemma lem5455125 : term668.
Proof. exact (@lem5455114 (@lem5455124)). Qed.
Lemma lem5455127 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455128 : term444 = term445.
Proof. exact (@lem5455127 (NUMERAL 0) term120). Qed.
Lemma lem5455129 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455130 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455131 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455130 h1) (fun h1 : term445 = True => @lem5455129)). Qed.
Lemma lem5455132 : term445 = True.
Proof. exact (EQ_MP (@lem5455131) (@lem5455129)). Qed.
Lemma lem5455133 : term444 = True.
Proof. exact (TRANS (@lem5455128) (@lem5455132)). Qed.
Lemma lem5455134 : True = term444.
Proof. exact (SYM (@lem5455133)). Qed.
Lemma lem5455135 : term444.
Proof. exact (EQ_MP (@lem5455134) (@lem0)). Qed.
Lemma lem5455136 : term666 = term669.
Proof. exact (@lem5455125 (@lem5455135)). Qed.
Lemma lem5455138 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455139 : term344 = term345.
Proof. exact (@lem5455138 term120 term120). Qed.
Lemma lem5455140 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455141 : term347 = term120.
Proof. exact (EQ_MP (@lem5455140) (@lem940073)). Qed.
Lemma lem5455142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455143 : term345 = term272.
Proof. exact (MK_COMB (@lem5455142) (@lem5455141)). Qed.
Lemma lem5455144 : term344 = term272.
Proof. exact (TRANS (@lem5455139) (@lem5455143)). Qed.
Lemma lem5455146 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455147 : term456 = term260.
Proof. exact (@lem5455146 term120). Qed.
Lemma lem5455148 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455149 : term670 = term664.
Proof. exact (MK_COMB (@lem5455148) (@lem5455147)). Qed.
Lemma lem5455150 : term669 = term444.
Proof. exact (MK_COMB (@lem5455149) (@lem5455144)). Qed.
Lemma lem5455152 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455153 : term444 = term445.
Proof. exact (@lem5455152 (NUMERAL 0) term120). Qed.
Lemma lem5455154 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455155 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455156 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455155 h1) (fun h1 : term445 = True => @lem5455154)). Qed.
Lemma lem5455157 : term445 = True.
Proof. exact (EQ_MP (@lem5455156) (@lem5455154)). Qed.
Lemma lem5455158 : term444 = True.
Proof. exact (TRANS (@lem5455153) (@lem5455157)). Qed.
Lemma lem5455159 : term669 = True.
Proof. exact (TRANS (@lem5455150) (@lem5455158)). Qed.
Lemma lem5455160 : term666 = True.
Proof. exact (TRANS (@lem5455136) (@lem5455159)). Qed.
Lemma lem5455161 : term444 = True.
Proof. exact (TRANS (@lem5455113) (@lem5455160)). Qed.
Lemma lem5455162 : term663 = True.
Proof. exact (TRANS (@lem5455104) (@lem5455161)). Qed.
Lemma lem5455163 : True = term663.
Proof. exact (SYM (@lem5455162)). Qed.
Lemma lem5455164 : term663.
Proof. exact (EQ_MP (@lem5455163) (@lem0)). Qed.
Lemma lem5455165 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term752 _70533 _70535.
Proof. exact (conj (@lem5455164) (@lem5455101 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455167 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5455168 (_70533 : int) (_70535 : int) : term753 _70533 _70535.
Proof. exact (@lem5455167 term272 (term395 _70533 _70535)). Qed.
Lemma lem5455169 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term754 _70533 _70535.
Proof. exact (@lem5455168 _70533 _70535 (@lem5455165 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455170 (_70533 : int) (_70535 : int) : (term755 _70533 _70535) = (term395 _70533 _70535).
Proof. exact (@lem1982733 (term395 _70533 _70535)). Qed.
Lemma lem5455171 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5455172 (_70533 : int) (_70535 : int) : (term756 _70533 _70535) = (term413 _70533 _70535).
Proof. exact (MK_COMB (@lem5455171) (@lem5455170 _70533 _70535)). Qed.
Lemma lem5455173 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5455174 (_70533 : int) (_70535 : int) : (term754 _70533 _70535) = (term414 _70533 _70535).
Proof. exact (MK_COMB (@lem5455172 _70533 _70535) (@lem5455173)). Qed.
Lemma lem5455175 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term414 _70533 _70535.
Proof. exact (EQ_MP (@lem5455174 _70533 _70535) (@lem5455169 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455176 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term493 _70533 _70535.
Proof. exact (conj (@lem5455175 _70534 _70532 _70533 _70535 h1) (@lem5454825 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455178 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5455179 (_70533 : int) (_70535 : int) : term757 _70533 _70535.
Proof. exact (@lem5455178 (term395 _70533 _70535) (term404 _70533 _70535)). Qed.
Lemma lem5455180 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term758 _70533 _70535.
Proof. exact (@lem5455179 _70533 _70535 (@lem5455176 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455181 (_70533 : int) (_70535 : int) : (term759 _70533 _70535) = (term760 _70533 _70535).
Proof. exact (@lem1982753 (term360 _70533) (real_of_int _70533) (term749 _70535) (term360 _70535)). Qed.
Lemma lem5455182 (_70533 : int) : (term688 _70533) = (term689 _70533).
Proof. exact (@lem1982713 term335 (real_of_int _70533)). Qed.
Lemma lem5455184 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455185 : term272 = term369.
Proof. exact (@lem5455184 term120). Qed.
Lemma lem5455187 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5455188 : term335 = term336.
Proof. exact (@lem5455187 term120). Qed.
Lemma lem5455189 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455190 : term690 = term691.
Proof. exact (MK_COMB (@lem5455189) (@lem5455188)). Qed.
Lemma lem5455191 : term692 = term693.
Proof. exact (MK_COMB (@lem5455190) (@lem5455185)). Qed.
Lemma lem5455192 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5455194 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455195 : term444 = term445.
Proof. exact (@lem5455194 (NUMERAL 0) term120). Qed.
Lemma lem5455196 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455197 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455198 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455197 h1) (fun h1 : term445 = True => @lem5455196)). Qed.
Lemma lem5455199 : term445 = True.
Proof. exact (EQ_MP (@lem5455198) (@lem5455196)). Qed.
Lemma lem5455200 : term444 = True.
Proof. exact (TRANS (@lem5455195) (@lem5455199)). Qed.
Lemma lem5455201 : True = term444.
Proof. exact (SYM (@lem5455200)). Qed.
Lemma lem5455202 : term444.
Proof. exact (EQ_MP (@lem5455201) (@lem0)). Qed.
Lemma lem5455203 : term695.
Proof. exact (@lem5455192 (@lem5455202)). Qed.
Lemma lem5455205 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455206 : term444 = term445.
Proof. exact (@lem5455205 (NUMERAL 0) term120). Qed.
Lemma lem5455207 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455208 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455209 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455208 h1) (fun h1 : term445 = True => @lem5455207)). Qed.
Lemma lem5455210 : term445 = True.
Proof. exact (EQ_MP (@lem5455209) (@lem5455207)). Qed.
Lemma lem5455211 : term444 = True.
Proof. exact (TRANS (@lem5455206) (@lem5455210)). Qed.
Lemma lem5455212 : True = term444.
Proof. exact (SYM (@lem5455211)). Qed.
Lemma lem5455213 : term444.
Proof. exact (EQ_MP (@lem5455212) (@lem0)). Qed.
Lemma lem5455214 : term696.
Proof. exact (@lem5455203 (@lem5455213)). Qed.
Lemma lem5455216 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455217 : term444 = term445.
Proof. exact (@lem5455216 (NUMERAL 0) term120). Qed.
Lemma lem5455218 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455219 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455220 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455219 h1) (fun h1 : term445 = True => @lem5455218)). Qed.
Lemma lem5455221 : term445 = True.
Proof. exact (EQ_MP (@lem5455220) (@lem5455218)). Qed.
Lemma lem5455222 : term444 = True.
Proof. exact (TRANS (@lem5455217) (@lem5455221)). Qed.
Lemma lem5455223 : True = term444.
Proof. exact (SYM (@lem5455222)). Qed.
Lemma lem5455224 : term444.
Proof. exact (EQ_MP (@lem5455223) (@lem0)). Qed.
Lemma lem5455225 : term697.
Proof. exact (@lem5455214 (@lem5455224)). Qed.
Lemma lem5455227 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455228 : term344 = term345.
Proof. exact (@lem5455227 term120 term120). Qed.
Lemma lem5455229 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455230 : term347 = term120.
Proof. exact (EQ_MP (@lem5455229) (@lem940073)). Qed.
Lemma lem5455231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455232 : term345 = term272.
Proof. exact (MK_COMB (@lem5455231) (@lem5455230)). Qed.
Lemma lem5455233 : term344 = term272.
Proof. exact (TRANS (@lem5455228) (@lem5455232)). Qed.
Lemma lem5455235 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5455236 : term370 = term375.
Proof. exact (@lem5455235 term120 term120). Qed.
Lemma lem5455237 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455238 : term347 = term120.
Proof. exact (EQ_MP (@lem5455237) (@lem940073)). Qed.
Lemma lem5455239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455240 : term345 = term272.
Proof. exact (MK_COMB (@lem5455239) (@lem5455238)). Qed.
Lemma lem5455241 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5455242 : term375 = term335.
Proof. exact (MK_COMB (@lem5455241) (@lem5455240)). Qed.
Lemma lem5455243 : term370 = term335.
Proof. exact (TRANS (@lem5455236) (@lem5455242)). Qed.
Lemma lem5455244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455245 : term698 = term690.
Proof. exact (MK_COMB (@lem5455244) (@lem5455243)). Qed.
Lemma lem5455246 : term699 = term692.
Proof. exact (MK_COMB (@lem5455245) (@lem5455233)). Qed.
Lemma lem5455248 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5455249 : term692 = term260.
Proof. exact (@lem5455248 term120). Qed.
Lemma lem5455250 : term699 = term260.
Proof. exact (TRANS (@lem5455246) (@lem5455249)). Qed.
Lemma lem5455251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455252 : term701 = term454.
Proof. exact (MK_COMB (@lem5455251) (@lem5455250)). Qed.
Lemma lem5455253 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5455254 : term702 = term456.
Proof. exact (MK_COMB (@lem5455252) (@lem5455253)). Qed.
Lemma lem5455256 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455257 : term456 = term260.
Proof. exact (@lem5455256 term120). Qed.
Lemma lem5455258 : term702 = term260.
Proof. exact (TRANS (@lem5455254) (@lem5455257)). Qed.
Lemma lem5455260 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455261 : term344 = term345.
Proof. exact (@lem5455260 term120 term120). Qed.
Lemma lem5455262 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455263 : term347 = term120.
Proof. exact (EQ_MP (@lem5455262) (@lem940073)). Qed.
Lemma lem5455264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455265 : term345 = term272.
Proof. exact (MK_COMB (@lem5455264) (@lem5455263)). Qed.
Lemma lem5455266 : term344 = term272.
Proof. exact (TRANS (@lem5455261) (@lem5455265)). Qed.
Lemma lem5455267 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5455268 : term458 = term456.
Proof. exact (MK_COMB (@lem5455267) (@lem5455266)). Qed.
Lemma lem5455270 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455271 : term456 = term260.
Proof. exact (@lem5455270 term120). Qed.
Lemma lem5455272 : term458 = term260.
Proof. exact (TRANS (@lem5455268) (@lem5455271)). Qed.
Lemma lem5455273 : term260 = term458.
Proof. exact (SYM (@lem5455272)). Qed.
Lemma lem5455274 : term702 = term458.
Proof. exact (TRANS (@lem5455258) (@lem5455273)). Qed.
Lemma lem5455275 : term693 = term332.
Proof. exact (@lem5455225 (@lem5455274)). Qed.
Lemma lem5455276 : term692 = term332.
Proof. exact (TRANS (@lem5455191) (@lem5455275)). Qed.
Lemma lem5455278 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5455279 : term332 = term260.
Proof. exact (@lem5455278 term260). Qed.
Lemma lem5455280 : term692 = term260.
Proof. exact (TRANS (@lem5455276) (@lem5455279)). Qed.
Lemma lem5455281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455282 : term703 = term454.
Proof. exact (MK_COMB (@lem5455281) (@lem5455280)). Qed.
Lemma lem5455283 (_70533 : int) : (real_of_int _70533) = (real_of_int _70533).
Proof. exact (eq_refl (real_of_int _70533)). Qed.
Lemma lem5455284 (_70533 : int) : (term689 _70533) = (term704 _70533).
Proof. exact (MK_COMB (@lem5455282) (@lem5455283 _70533)). Qed.
Lemma lem5455285 (_70533 : int) : (term688 _70533) = (term704 _70533).
Proof. exact (TRANS (@lem5455182 _70533) (@lem5455284 _70533)). Qed.
Lemma lem5455286 (_70533 : int) : (term704 _70533) = term260.
Proof. exact (@lem1982719 (real_of_int _70533)). Qed.
Lemma lem5455287 (_70533 : int) : (term688 _70533) = term260.
Proof. exact (TRANS (@lem5455285 _70533) (@lem5455286 _70533)). Qed.
Lemma lem5455288 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455289 (_70533 : int) : (term705 _70533) = term706.
Proof. exact (MK_COMB (@lem5455288) (@lem5455287 _70533)). Qed.
Lemma lem5455290 (_70535 : int) : (term761 _70535) = (term708 _70535).
Proof. exact (@lem1982759 (real_of_int _70535) (term360 _70535) term335). Qed.
Lemma lem5455291 (_70535 : int) : (term709 _70535) = (term689 _70535).
Proof. exact (@lem1982715 term335 (real_of_int _70535)). Qed.
Lemma lem5455293 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455294 : term272 = term369.
Proof. exact (@lem5455293 term120). Qed.
Lemma lem5455296 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5455297 : term335 = term336.
Proof. exact (@lem5455296 term120). Qed.
Lemma lem5455298 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455299 : term690 = term691.
Proof. exact (MK_COMB (@lem5455298) (@lem5455297)). Qed.
Lemma lem5455300 : term692 = term693.
Proof. exact (MK_COMB (@lem5455299) (@lem5455294)). Qed.
Lemma lem5455301 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5455303 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455304 : term444 = term445.
Proof. exact (@lem5455303 (NUMERAL 0) term120). Qed.
Lemma lem5455305 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455306 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455307 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455306 h1) (fun h1 : term445 = True => @lem5455305)). Qed.
Lemma lem5455308 : term445 = True.
Proof. exact (EQ_MP (@lem5455307) (@lem5455305)). Qed.
Lemma lem5455309 : term444 = True.
Proof. exact (TRANS (@lem5455304) (@lem5455308)). Qed.
Lemma lem5455310 : True = term444.
Proof. exact (SYM (@lem5455309)). Qed.
Lemma lem5455311 : term444.
Proof. exact (EQ_MP (@lem5455310) (@lem0)). Qed.
Lemma lem5455312 : term695.
Proof. exact (@lem5455301 (@lem5455311)). Qed.
Lemma lem5455314 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455315 : term444 = term445.
Proof. exact (@lem5455314 (NUMERAL 0) term120). Qed.
Lemma lem5455316 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455317 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455318 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455317 h1) (fun h1 : term445 = True => @lem5455316)). Qed.
Lemma lem5455319 : term445 = True.
Proof. exact (EQ_MP (@lem5455318) (@lem5455316)). Qed.
Lemma lem5455320 : term444 = True.
Proof. exact (TRANS (@lem5455315) (@lem5455319)). Qed.
Lemma lem5455321 : True = term444.
Proof. exact (SYM (@lem5455320)). Qed.
Lemma lem5455322 : term444.
Proof. exact (EQ_MP (@lem5455321) (@lem0)). Qed.
Lemma lem5455323 : term696.
Proof. exact (@lem5455312 (@lem5455322)). Qed.
Lemma lem5455325 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455326 : term444 = term445.
Proof. exact (@lem5455325 (NUMERAL 0) term120). Qed.
Lemma lem5455327 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455328 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455329 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455328 h1) (fun h1 : term445 = True => @lem5455327)). Qed.
Lemma lem5455330 : term445 = True.
Proof. exact (EQ_MP (@lem5455329) (@lem5455327)). Qed.
Lemma lem5455331 : term444 = True.
Proof. exact (TRANS (@lem5455326) (@lem5455330)). Qed.
Lemma lem5455332 : True = term444.
Proof. exact (SYM (@lem5455331)). Qed.
Lemma lem5455333 : term444.
Proof. exact (EQ_MP (@lem5455332) (@lem0)). Qed.
Lemma lem5455334 : term697.
Proof. exact (@lem5455323 (@lem5455333)). Qed.
Lemma lem5455336 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455337 : term344 = term345.
Proof. exact (@lem5455336 term120 term120). Qed.
Lemma lem5455338 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455339 : term347 = term120.
Proof. exact (EQ_MP (@lem5455338) (@lem940073)). Qed.
Lemma lem5455340 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455341 : term345 = term272.
Proof. exact (MK_COMB (@lem5455340) (@lem5455339)). Qed.
Lemma lem5455342 : term344 = term272.
Proof. exact (TRANS (@lem5455337) (@lem5455341)). Qed.
Lemma lem5455344 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5455345 : term370 = term375.
Proof. exact (@lem5455344 term120 term120). Qed.
Lemma lem5455346 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455347 : term347 = term120.
Proof. exact (EQ_MP (@lem5455346) (@lem940073)). Qed.
Lemma lem5455348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455349 : term345 = term272.
Proof. exact (MK_COMB (@lem5455348) (@lem5455347)). Qed.
Lemma lem5455350 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5455351 : term375 = term335.
Proof. exact (MK_COMB (@lem5455350) (@lem5455349)). Qed.
Lemma lem5455352 : term370 = term335.
Proof. exact (TRANS (@lem5455345) (@lem5455351)). Qed.
Lemma lem5455353 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455354 : term698 = term690.
Proof. exact (MK_COMB (@lem5455353) (@lem5455352)). Qed.
Lemma lem5455355 : term699 = term692.
Proof. exact (MK_COMB (@lem5455354) (@lem5455342)). Qed.
Lemma lem5455357 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5455358 : term692 = term260.
Proof. exact (@lem5455357 term120). Qed.
Lemma lem5455359 : term699 = term260.
Proof. exact (TRANS (@lem5455355) (@lem5455358)). Qed.
Lemma lem5455360 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455361 : term701 = term454.
Proof. exact (MK_COMB (@lem5455360) (@lem5455359)). Qed.
Lemma lem5455362 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5455363 : term702 = term456.
Proof. exact (MK_COMB (@lem5455361) (@lem5455362)). Qed.
Lemma lem5455365 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455366 : term456 = term260.
Proof. exact (@lem5455365 term120). Qed.
Lemma lem5455367 : term702 = term260.
Proof. exact (TRANS (@lem5455363) (@lem5455366)). Qed.
Lemma lem5455369 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455370 : term344 = term345.
Proof. exact (@lem5455369 term120 term120). Qed.
Lemma lem5455371 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455372 : term347 = term120.
Proof. exact (EQ_MP (@lem5455371) (@lem940073)). Qed.
Lemma lem5455373 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455374 : term345 = term272.
Proof. exact (MK_COMB (@lem5455373) (@lem5455372)). Qed.
Lemma lem5455375 : term344 = term272.
Proof. exact (TRANS (@lem5455370) (@lem5455374)). Qed.
Lemma lem5455376 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5455377 : term458 = term456.
Proof. exact (MK_COMB (@lem5455376) (@lem5455375)). Qed.
Lemma lem5455379 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455380 : term456 = term260.
Proof. exact (@lem5455379 term120). Qed.
Lemma lem5455381 : term458 = term260.
Proof. exact (TRANS (@lem5455377) (@lem5455380)). Qed.
Lemma lem5455382 : term260 = term458.
Proof. exact (SYM (@lem5455381)). Qed.
Lemma lem5455383 : term702 = term458.
Proof. exact (TRANS (@lem5455367) (@lem5455382)). Qed.
Lemma lem5455384 : term693 = term332.
Proof. exact (@lem5455334 (@lem5455383)). Qed.
Lemma lem5455385 : term692 = term332.
Proof. exact (TRANS (@lem5455300) (@lem5455384)). Qed.
Lemma lem5455387 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5455388 : term332 = term260.
Proof. exact (@lem5455387 term260). Qed.
Lemma lem5455389 : term692 = term260.
Proof. exact (TRANS (@lem5455385) (@lem5455388)). Qed.
Lemma lem5455390 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455391 : term703 = term454.
Proof. exact (MK_COMB (@lem5455390) (@lem5455389)). Qed.
Lemma lem5455392 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5455393 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5455391) (@lem5455392 _70535)). Qed.
Lemma lem5455394 (_70535 : int) : (term709 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5455291 _70535) (@lem5455393 _70535)). Qed.
Lemma lem5455395 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5455396 (_70535 : int) : (term709 _70535) = term260.
Proof. exact (TRANS (@lem5455394 _70535) (@lem5455395 _70535)). Qed.
Lemma lem5455397 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455398 (_70535 : int) : (term710 _70535) = term706.
Proof. exact (MK_COMB (@lem5455397) (@lem5455396 _70535)). Qed.
Lemma lem5455399 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5455400 (_70535 : int) : (term708 _70535) = term711.
Proof. exact (MK_COMB (@lem5455398 _70535) (@lem5455399)). Qed.
Lemma lem5455401 (_70535 : int) : (term761 _70535) = term711.
Proof. exact (TRANS (@lem5455290 _70535) (@lem5455400 _70535)). Qed.
Lemma lem5455402 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5455403 (_70535 : int) : (term761 _70535) = term335.
Proof. exact (TRANS (@lem5455401 _70535) (@lem5455402)). Qed.
Lemma lem5455404 (_70533 : int) (_70535 : int) : (term760 _70533 _70535) = term711.
Proof. exact (MK_COMB (@lem5455289 _70533) (@lem5455403 _70535)). Qed.
Lemma lem5455405 (_70533 : int) (_70535 : int) : (term759 _70533 _70535) = term711.
Proof. exact (TRANS (@lem5455181 _70533 _70535) (@lem5455404 _70533 _70535)). Qed.
Lemma lem5455406 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5455407 (_70533 : int) (_70535 : int) : (term759 _70533 _70535) = term335.
Proof. exact (TRANS (@lem5455405 _70533 _70535) (@lem5455406)). Qed.
Lemma lem5455408 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5455409 (_70533 : int) (_70535 : int) : (term762 _70533 _70535) = term713.
Proof. exact (MK_COMB (@lem5455408) (@lem5455407 _70533 _70535)). Qed.
Lemma lem5455410 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5455411 (_70533 : int) (_70535 : int) : (term758 _70533 _70535) = term714.
Proof. exact (MK_COMB (@lem5455409 _70533 _70535) (@lem5455410)). Qed.
Lemma lem5455412 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : term714.
Proof. exact (EQ_MP (@lem5455411 _70533 _70535) (@lem5455180 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455414 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5455415 : term714 = term715.
Proof. exact (@lem5455414 term260 term335). Qed.
Lemma lem5455417 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5455418 : term335 = term336.
Proof. exact (@lem5455417 term120). Qed.
Lemma lem5455420 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455421 : term260 = term332.
Proof. exact (@lem5455420 (NUMERAL 0)). Qed.
Lemma lem5455422 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5455423 : term262 = term716.
Proof. exact (MK_COMB (@lem5455422) (@lem5455421)). Qed.
Lemma lem5455424 : term715 = term717.
Proof. exact (MK_COMB (@lem5455423) (@lem5455418)). Qed.
Lemma lem5455425 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5455427 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455428 : term444 = term445.
Proof. exact (@lem5455427 (NUMERAL 0) term120). Qed.
Lemma lem5455429 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455430 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455431 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455430 h1) (fun h1 : term445 = True => @lem5455429)). Qed.
Lemma lem5455432 : term445 = True.
Proof. exact (EQ_MP (@lem5455431) (@lem5455429)). Qed.
Lemma lem5455433 : term444 = True.
Proof. exact (TRANS (@lem5455428) (@lem5455432)). Qed.
Lemma lem5455434 : True = term444.
Proof. exact (SYM (@lem5455433)). Qed.
Lemma lem5455435 : term444.
Proof. exact (EQ_MP (@lem5455434) (@lem0)). Qed.
Lemma lem5455436 : term719.
Proof. exact (@lem5455425 (@lem5455435)). Qed.
Lemma lem5455438 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455439 : term444 = term445.
Proof. exact (@lem5455438 (NUMERAL 0) term120). Qed.
Lemma lem5455440 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455441 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455442 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455441 h1) (fun h1 : term445 = True => @lem5455440)). Qed.
Lemma lem5455443 : term445 = True.
Proof. exact (EQ_MP (@lem5455442) (@lem5455440)). Qed.
Lemma lem5455444 : term444 = True.
Proof. exact (TRANS (@lem5455439) (@lem5455443)). Qed.
Lemma lem5455445 : True = term444.
Proof. exact (SYM (@lem5455444)). Qed.
Lemma lem5455446 : term444.
Proof. exact (EQ_MP (@lem5455445) (@lem0)). Qed.
Lemma lem5455447 : term717 = term720.
Proof. exact (@lem5455436 (@lem5455446)). Qed.
Lemma lem5455449 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5455450 : term370 = term375.
Proof. exact (@lem5455449 term120 term120). Qed.
Lemma lem5455451 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455452 : term347 = term120.
Proof. exact (EQ_MP (@lem5455451) (@lem940073)). Qed.
Lemma lem5455453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455454 : term345 = term272.
Proof. exact (MK_COMB (@lem5455453) (@lem5455452)). Qed.
Lemma lem5455455 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5455456 : term375 = term335.
Proof. exact (MK_COMB (@lem5455455) (@lem5455454)). Qed.
Lemma lem5455457 : term370 = term335.
Proof. exact (TRANS (@lem5455450) (@lem5455456)). Qed.
Lemma lem5455459 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455460 : term456 = term260.
Proof. exact (@lem5455459 term120). Qed.
Lemma lem5455461 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5455462 : term721 = term262.
Proof. exact (MK_COMB (@lem5455461) (@lem5455460)). Qed.
Lemma lem5455463 : term720 = term715.
Proof. exact (MK_COMB (@lem5455462) (@lem5455457)). Qed.
Lemma lem5455465 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5455466 : term715 = term724.
Proof. exact (@lem5455465 (NUMERAL 0) term120). Qed.
Lemma lem5455467 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455468 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5455469 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455468 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5455467)). Qed.
Lemma lem5455470 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5455469) (@lem5455467)). Qed.
Lemma lem5455471 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5455472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5455473 : term725 = (and True).
Proof. exact (MK_COMB (@lem5455472) (@lem5455471)). Qed.
Lemma lem5455474 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5455473) (@lem5455470)). Qed.
Lemma lem5455476 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5455477 : term724 = False.
Proof. exact (TRANS (@lem5455474) (@lem5455476)). Qed.
Lemma lem5455478 : term715 = False.
Proof. exact (TRANS (@lem5455466) (@lem5455477)). Qed.
Lemma lem5455479 : term720 = False.
Proof. exact (TRANS (@lem5455463) (@lem5455478)). Qed.
Lemma lem5455480 : term717 = False.
Proof. exact (TRANS (@lem5455447) (@lem5455479)). Qed.
Lemma lem5455481 : term715 = False.
Proof. exact (TRANS (@lem5455424) (@lem5455480)). Qed.
Lemma lem5455482 : term714 = False.
Proof. exact (TRANS (@lem5455415) (@lem5455481)). Qed.
Lemma lem5455483 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term726 _70534 _70532 _70533 _70535) : False.
Proof. exact (EQ_MP (@lem5455482) (@lem5455412 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5455484 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term653 _70534 _70532 _70533 _70535) : False.
Proof. exact (or_elim (@lem5454265 _70534 _70532 _70533 _70535 h1) (fun h0 : term662 _70534 _70532 _70533 _70535 => @lem5454736 _70534 _70532 _70533 _70535 h0) (fun h0 : term726 _70534 _70532 _70533 _70535 => @lem5455483 _70534 _70532 _70533 _70535 h0)). Qed.
Lemma lem5455485 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term649 _70532 _70533 _70534 _70535) : term649 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5455486 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term763 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5455487 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term650 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5455486 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455489 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term619 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5455487 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455491 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term588 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5455489 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455493 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term557 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5455491 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455495 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term526 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5455493 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455496 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term363 _70532 _70533.
Proof. exact (proj1 (@lem5455493 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455497 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term423 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5455495 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455498 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term383 _70532 _70535.
Proof. exact (proj1 (@lem5455495 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455500 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term414 _70533 _70535.
Proof. exact (proj1 (@lem5455497 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455502 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5455503 : term663 = term444.
Proof. exact (@lem5455502 term260 term272). Qed.
Lemma lem5455505 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455506 : term272 = term369.
Proof. exact (@lem5455505 term120). Qed.
Lemma lem5455508 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455509 : term260 = term332.
Proof. exact (@lem5455508 (NUMERAL 0)). Qed.
Lemma lem5455510 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455511 : term664 = term665.
Proof. exact (MK_COMB (@lem5455510) (@lem5455509)). Qed.
Lemma lem5455512 : term444 = term666.
Proof. exact (MK_COMB (@lem5455511) (@lem5455506)). Qed.
Lemma lem5455513 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5455515 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455516 : term444 = term445.
Proof. exact (@lem5455515 (NUMERAL 0) term120). Qed.
Lemma lem5455517 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455518 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455519 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455518 h1) (fun h1 : term445 = True => @lem5455517)). Qed.
Lemma lem5455520 : term445 = True.
Proof. exact (EQ_MP (@lem5455519) (@lem5455517)). Qed.
Lemma lem5455521 : term444 = True.
Proof. exact (TRANS (@lem5455516) (@lem5455520)). Qed.
Lemma lem5455522 : True = term444.
Proof. exact (SYM (@lem5455521)). Qed.
Lemma lem5455523 : term444.
Proof. exact (EQ_MP (@lem5455522) (@lem0)). Qed.
Lemma lem5455524 : term668.
Proof. exact (@lem5455513 (@lem5455523)). Qed.
Lemma lem5455526 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455527 : term444 = term445.
Proof. exact (@lem5455526 (NUMERAL 0) term120). Qed.
Lemma lem5455528 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455529 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455530 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455529 h1) (fun h1 : term445 = True => @lem5455528)). Qed.
Lemma lem5455531 : term445 = True.
Proof. exact (EQ_MP (@lem5455530) (@lem5455528)). Qed.
Lemma lem5455532 : term444 = True.
Proof. exact (TRANS (@lem5455527) (@lem5455531)). Qed.
Lemma lem5455533 : True = term444.
Proof. exact (SYM (@lem5455532)). Qed.
Lemma lem5455534 : term444.
Proof. exact (EQ_MP (@lem5455533) (@lem0)). Qed.
Lemma lem5455535 : term666 = term669.
Proof. exact (@lem5455524 (@lem5455534)). Qed.
Lemma lem5455537 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455538 : term344 = term345.
Proof. exact (@lem5455537 term120 term120). Qed.
Lemma lem5455539 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455540 : term347 = term120.
Proof. exact (EQ_MP (@lem5455539) (@lem940073)). Qed.
Lemma lem5455541 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455542 : term345 = term272.
Proof. exact (MK_COMB (@lem5455541) (@lem5455540)). Qed.
Lemma lem5455543 : term344 = term272.
Proof. exact (TRANS (@lem5455538) (@lem5455542)). Qed.
Lemma lem5455545 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455546 : term456 = term260.
Proof. exact (@lem5455545 term120). Qed.
Lemma lem5455547 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455548 : term670 = term664.
Proof. exact (MK_COMB (@lem5455547) (@lem5455546)). Qed.
Lemma lem5455549 : term669 = term444.
Proof. exact (MK_COMB (@lem5455548) (@lem5455543)). Qed.
Lemma lem5455551 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455552 : term444 = term445.
Proof. exact (@lem5455551 (NUMERAL 0) term120). Qed.
Lemma lem5455553 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455554 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455555 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455554 h1) (fun h1 : term445 = True => @lem5455553)). Qed.
Lemma lem5455556 : term445 = True.
Proof. exact (EQ_MP (@lem5455555) (@lem5455553)). Qed.
Lemma lem5455557 : term444 = True.
Proof. exact (TRANS (@lem5455552) (@lem5455556)). Qed.
Lemma lem5455558 : term669 = True.
Proof. exact (TRANS (@lem5455549) (@lem5455557)). Qed.
Lemma lem5455559 : term666 = True.
Proof. exact (TRANS (@lem5455535) (@lem5455558)). Qed.
Lemma lem5455560 : term444 = True.
Proof. exact (TRANS (@lem5455512) (@lem5455559)). Qed.
Lemma lem5455561 : term663 = True.
Proof. exact (TRANS (@lem5455503) (@lem5455560)). Qed.
Lemma lem5455562 : True = term663.
Proof. exact (SYM (@lem5455561)). Qed.
Lemma lem5455563 : term663.
Proof. exact (EQ_MP (@lem5455562) (@lem0)). Qed.
Lemma lem5455564 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term752 _70533 _70535.
Proof. exact (conj (@lem5455563) (@lem5455500 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455566 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5455567 (_70533 : int) (_70535 : int) : term753 _70533 _70535.
Proof. exact (@lem5455566 term272 (term395 _70533 _70535)). Qed.
Lemma lem5455568 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term754 _70533 _70535.
Proof. exact (@lem5455567 _70533 _70535 (@lem5455564 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455569 (_70533 : int) (_70535 : int) : (term755 _70533 _70535) = (term395 _70533 _70535).
Proof. exact (@lem1982733 (term395 _70533 _70535)). Qed.
Lemma lem5455570 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5455571 (_70533 : int) (_70535 : int) : (term756 _70533 _70535) = (term413 _70533 _70535).
Proof. exact (MK_COMB (@lem5455570) (@lem5455569 _70533 _70535)). Qed.
Lemma lem5455572 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5455573 (_70533 : int) (_70535 : int) : (term754 _70533 _70535) = (term414 _70533 _70535).
Proof. exact (MK_COMB (@lem5455571 _70533 _70535) (@lem5455572)). Qed.
Lemma lem5455574 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term414 _70533 _70535.
Proof. exact (EQ_MP (@lem5455573 _70533 _70535) (@lem5455568 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455576 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5455577 : term663 = term444.
Proof. exact (@lem5455576 term260 term272). Qed.
Lemma lem5455579 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455580 : term272 = term369.
Proof. exact (@lem5455579 term120). Qed.
Lemma lem5455582 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455583 : term260 = term332.
Proof. exact (@lem5455582 (NUMERAL 0)). Qed.
Lemma lem5455584 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455585 : term664 = term665.
Proof. exact (MK_COMB (@lem5455584) (@lem5455583)). Qed.
Lemma lem5455586 : term444 = term666.
Proof. exact (MK_COMB (@lem5455585) (@lem5455580)). Qed.
Lemma lem5455587 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5455589 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455590 : term444 = term445.
Proof. exact (@lem5455589 (NUMERAL 0) term120). Qed.
Lemma lem5455591 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455592 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455593 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455592 h1) (fun h1 : term445 = True => @lem5455591)). Qed.
Lemma lem5455594 : term445 = True.
Proof. exact (EQ_MP (@lem5455593) (@lem5455591)). Qed.
Lemma lem5455595 : term444 = True.
Proof. exact (TRANS (@lem5455590) (@lem5455594)). Qed.
Lemma lem5455596 : True = term444.
Proof. exact (SYM (@lem5455595)). Qed.
Lemma lem5455597 : term444.
Proof. exact (EQ_MP (@lem5455596) (@lem0)). Qed.
Lemma lem5455598 : term668.
Proof. exact (@lem5455587 (@lem5455597)). Qed.
Lemma lem5455600 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455601 : term444 = term445.
Proof. exact (@lem5455600 (NUMERAL 0) term120). Qed.
Lemma lem5455602 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455603 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455604 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455603 h1) (fun h1 : term445 = True => @lem5455602)). Qed.
Lemma lem5455605 : term445 = True.
Proof. exact (EQ_MP (@lem5455604) (@lem5455602)). Qed.
Lemma lem5455606 : term444 = True.
Proof. exact (TRANS (@lem5455601) (@lem5455605)). Qed.
Lemma lem5455607 : True = term444.
Proof. exact (SYM (@lem5455606)). Qed.
Lemma lem5455608 : term444.
Proof. exact (EQ_MP (@lem5455607) (@lem0)). Qed.
Lemma lem5455609 : term666 = term669.
Proof. exact (@lem5455598 (@lem5455608)). Qed.
Lemma lem5455611 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455612 : term344 = term345.
Proof. exact (@lem5455611 term120 term120). Qed.
Lemma lem5455613 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455614 : term347 = term120.
Proof. exact (EQ_MP (@lem5455613) (@lem940073)). Qed.
Lemma lem5455615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455616 : term345 = term272.
Proof. exact (MK_COMB (@lem5455615) (@lem5455614)). Qed.
Lemma lem5455617 : term344 = term272.
Proof. exact (TRANS (@lem5455612) (@lem5455616)). Qed.
Lemma lem5455619 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455620 : term456 = term260.
Proof. exact (@lem5455619 term120). Qed.
Lemma lem5455621 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455622 : term670 = term664.
Proof. exact (MK_COMB (@lem5455621) (@lem5455620)). Qed.
Lemma lem5455623 : term669 = term444.
Proof. exact (MK_COMB (@lem5455622) (@lem5455617)). Qed.
Lemma lem5455625 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455626 : term444 = term445.
Proof. exact (@lem5455625 (NUMERAL 0) term120). Qed.
Lemma lem5455627 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455628 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455629 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455628 h1) (fun h1 : term445 = True => @lem5455627)). Qed.
Lemma lem5455630 : term445 = True.
Proof. exact (EQ_MP (@lem5455629) (@lem5455627)). Qed.
Lemma lem5455631 : term444 = True.
Proof. exact (TRANS (@lem5455626) (@lem5455630)). Qed.
Lemma lem5455632 : term669 = True.
Proof. exact (TRANS (@lem5455623) (@lem5455631)). Qed.
Lemma lem5455633 : term666 = True.
Proof. exact (TRANS (@lem5455609) (@lem5455632)). Qed.
Lemma lem5455634 : term444 = True.
Proof. exact (TRANS (@lem5455586) (@lem5455633)). Qed.
Lemma lem5455635 : term663 = True.
Proof. exact (TRANS (@lem5455577) (@lem5455634)). Qed.
Lemma lem5455636 : True = term663.
Proof. exact (SYM (@lem5455635)). Qed.
Lemma lem5455637 : term663.
Proof. exact (EQ_MP (@lem5455636) (@lem0)). Qed.
Lemma lem5455638 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term671 _70532 _70535.
Proof. exact (conj (@lem5455637) (@lem5455498 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455640 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5455641 (_70532 : int) (_70535 : int) : term673 _70532 _70535.
Proof. exact (@lem5455640 term272 (term380 _70532 _70535)). Qed.
Lemma lem5455642 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term674 _70532 _70535.
Proof. exact (@lem5455641 _70532 _70535 (@lem5455638 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455643 (_70532 : int) (_70535 : int) : (term675 _70532 _70535) = (term380 _70532 _70535).
Proof. exact (@lem1982733 (term380 _70532 _70535)). Qed.
Lemma lem5455644 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5455645 (_70532 : int) (_70535 : int) : (term676 _70532 _70535) = (term382 _70532 _70535).
Proof. exact (MK_COMB (@lem5455644) (@lem5455643 _70532 _70535)). Qed.
Lemma lem5455646 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5455647 (_70532 : int) (_70535 : int) : (term674 _70532 _70535) = (term383 _70532 _70535).
Proof. exact (MK_COMB (@lem5455645 _70532 _70535) (@lem5455646)). Qed.
Lemma lem5455648 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term383 _70532 _70535.
Proof. exact (EQ_MP (@lem5455647 _70532 _70535) (@lem5455642 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455650 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5455651 : term663 = term444.
Proof. exact (@lem5455650 term260 term272). Qed.
Lemma lem5455653 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455654 : term272 = term369.
Proof. exact (@lem5455653 term120). Qed.
Lemma lem5455656 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455657 : term260 = term332.
Proof. exact (@lem5455656 (NUMERAL 0)). Qed.
Lemma lem5455658 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455659 : term664 = term665.
Proof. exact (MK_COMB (@lem5455658) (@lem5455657)). Qed.
Lemma lem5455660 : term444 = term666.
Proof. exact (MK_COMB (@lem5455659) (@lem5455654)). Qed.
Lemma lem5455661 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5455663 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455664 : term444 = term445.
Proof. exact (@lem5455663 (NUMERAL 0) term120). Qed.
Lemma lem5455665 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455666 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455667 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455666 h1) (fun h1 : term445 = True => @lem5455665)). Qed.
Lemma lem5455668 : term445 = True.
Proof. exact (EQ_MP (@lem5455667) (@lem5455665)). Qed.
Lemma lem5455669 : term444 = True.
Proof. exact (TRANS (@lem5455664) (@lem5455668)). Qed.
Lemma lem5455670 : True = term444.
Proof. exact (SYM (@lem5455669)). Qed.
Lemma lem5455671 : term444.
Proof. exact (EQ_MP (@lem5455670) (@lem0)). Qed.
Lemma lem5455672 : term668.
Proof. exact (@lem5455661 (@lem5455671)). Qed.
Lemma lem5455674 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455675 : term444 = term445.
Proof. exact (@lem5455674 (NUMERAL 0) term120). Qed.
Lemma lem5455676 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455677 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455678 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455677 h1) (fun h1 : term445 = True => @lem5455676)). Qed.
Lemma lem5455679 : term445 = True.
Proof. exact (EQ_MP (@lem5455678) (@lem5455676)). Qed.
Lemma lem5455680 : term444 = True.
Proof. exact (TRANS (@lem5455675) (@lem5455679)). Qed.
Lemma lem5455681 : True = term444.
Proof. exact (SYM (@lem5455680)). Qed.
Lemma lem5455682 : term444.
Proof. exact (EQ_MP (@lem5455681) (@lem0)). Qed.
Lemma lem5455683 : term666 = term669.
Proof. exact (@lem5455672 (@lem5455682)). Qed.
Lemma lem5455685 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455686 : term344 = term345.
Proof. exact (@lem5455685 term120 term120). Qed.
Lemma lem5455687 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455688 : term347 = term120.
Proof. exact (EQ_MP (@lem5455687) (@lem940073)). Qed.
Lemma lem5455689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455690 : term345 = term272.
Proof. exact (MK_COMB (@lem5455689) (@lem5455688)). Qed.
Lemma lem5455691 : term344 = term272.
Proof. exact (TRANS (@lem5455686) (@lem5455690)). Qed.
Lemma lem5455693 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455694 : term456 = term260.
Proof. exact (@lem5455693 term120). Qed.
Lemma lem5455695 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455696 : term670 = term664.
Proof. exact (MK_COMB (@lem5455695) (@lem5455694)). Qed.
Lemma lem5455697 : term669 = term444.
Proof. exact (MK_COMB (@lem5455696) (@lem5455691)). Qed.
Lemma lem5455699 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455700 : term444 = term445.
Proof. exact (@lem5455699 (NUMERAL 0) term120). Qed.
Lemma lem5455701 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455702 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455703 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455702 h1) (fun h1 : term445 = True => @lem5455701)). Qed.
Lemma lem5455704 : term445 = True.
Proof. exact (EQ_MP (@lem5455703) (@lem5455701)). Qed.
Lemma lem5455705 : term444 = True.
Proof. exact (TRANS (@lem5455700) (@lem5455704)). Qed.
Lemma lem5455706 : term669 = True.
Proof. exact (TRANS (@lem5455697) (@lem5455705)). Qed.
Lemma lem5455707 : term666 = True.
Proof. exact (TRANS (@lem5455683) (@lem5455706)). Qed.
Lemma lem5455708 : term444 = True.
Proof. exact (TRANS (@lem5455660) (@lem5455707)). Qed.
Lemma lem5455709 : term663 = True.
Proof. exact (TRANS (@lem5455651) (@lem5455708)). Qed.
Lemma lem5455710 : True = term663.
Proof. exact (SYM (@lem5455709)). Qed.
Lemma lem5455711 : term663.
Proof. exact (EQ_MP (@lem5455710) (@lem0)). Qed.
Lemma lem5455712 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term764 _70532 _70533.
Proof. exact (conj (@lem5455711) (@lem5455496 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455714 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5455715 (_70532 : int) (_70533 : int) : term765 _70532 _70533.
Proof. exact (@lem5455714 term272 (term359 _70532 _70533)). Qed.
Lemma lem5455716 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term766 _70532 _70533.
Proof. exact (@lem5455715 _70532 _70533 (@lem5455712 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455717 (_70532 : int) (_70533 : int) : (term767 _70532 _70533) = (term359 _70532 _70533).
Proof. exact (@lem1982733 (term359 _70532 _70533)). Qed.
Lemma lem5455718 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5455719 (_70532 : int) (_70533 : int) : (term768 _70532 _70533) = (term362 _70532 _70533).
Proof. exact (MK_COMB (@lem5455718) (@lem5455717 _70532 _70533)). Qed.
Lemma lem5455720 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5455721 (_70532 : int) (_70533 : int) : (term766 _70532 _70533) = (term363 _70532 _70533).
Proof. exact (MK_COMB (@lem5455719 _70532 _70533) (@lem5455720)). Qed.
Lemma lem5455722 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term363 _70532 _70533.
Proof. exact (EQ_MP (@lem5455721 _70532 _70533) (@lem5455716 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455723 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term769 _70533 _70532 _70535.
Proof. exact (conj (@lem5455722 _70532 _70533 _70534 _70535 h1) (@lem5455648 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455725 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5455726 (_70533 : int) (_70532 : int) (_70535 : int) : term770 _70533 _70532 _70535.
Proof. exact (@lem5455725 (term359 _70532 _70533) (term380 _70532 _70535)). Qed.
Lemma lem5455727 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term771 _70533 _70532 _70535.
Proof. exact (@lem5455726 _70533 _70532 _70535 (@lem5455723 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455728 (_70532 : int) (_70533 : int) (_70535 : int) : (term772 _70533 _70532 _70535) = (term773 _70532 _70533 _70535).
Proof. exact (@lem1982753 (term360 _70532) (real_of_int _70532) (term274 _70533) (term379 _70535)). Qed.
Lemma lem5455729 (_70532 : int) : (term688 _70532) = (term689 _70532).
Proof. exact (@lem1982713 term335 (real_of_int _70532)). Qed.
Lemma lem5455731 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455732 : term272 = term369.
Proof. exact (@lem5455731 term120). Qed.
Lemma lem5455734 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5455735 : term335 = term336.
Proof. exact (@lem5455734 term120). Qed.
Lemma lem5455736 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455737 : term690 = term691.
Proof. exact (MK_COMB (@lem5455736) (@lem5455735)). Qed.
Lemma lem5455738 : term692 = term693.
Proof. exact (MK_COMB (@lem5455737) (@lem5455732)). Qed.
Lemma lem5455739 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5455741 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455742 : term444 = term445.
Proof. exact (@lem5455741 (NUMERAL 0) term120). Qed.
Lemma lem5455743 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455744 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455745 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455744 h1) (fun h1 : term445 = True => @lem5455743)). Qed.
Lemma lem5455746 : term445 = True.
Proof. exact (EQ_MP (@lem5455745) (@lem5455743)). Qed.
Lemma lem5455747 : term444 = True.
Proof. exact (TRANS (@lem5455742) (@lem5455746)). Qed.
Lemma lem5455748 : True = term444.
Proof. exact (SYM (@lem5455747)). Qed.
Lemma lem5455749 : term444.
Proof. exact (EQ_MP (@lem5455748) (@lem0)). Qed.
Lemma lem5455750 : term695.
Proof. exact (@lem5455739 (@lem5455749)). Qed.
Lemma lem5455752 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455753 : term444 = term445.
Proof. exact (@lem5455752 (NUMERAL 0) term120). Qed.
Lemma lem5455754 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455755 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455756 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455755 h1) (fun h1 : term445 = True => @lem5455754)). Qed.
Lemma lem5455757 : term445 = True.
Proof. exact (EQ_MP (@lem5455756) (@lem5455754)). Qed.
Lemma lem5455758 : term444 = True.
Proof. exact (TRANS (@lem5455753) (@lem5455757)). Qed.
Lemma lem5455759 : True = term444.
Proof. exact (SYM (@lem5455758)). Qed.
Lemma lem5455760 : term444.
Proof. exact (EQ_MP (@lem5455759) (@lem0)). Qed.
Lemma lem5455761 : term696.
Proof. exact (@lem5455750 (@lem5455760)). Qed.
Lemma lem5455763 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455764 : term444 = term445.
Proof. exact (@lem5455763 (NUMERAL 0) term120). Qed.
Lemma lem5455765 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455766 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455767 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455766 h1) (fun h1 : term445 = True => @lem5455765)). Qed.
Lemma lem5455768 : term445 = True.
Proof. exact (EQ_MP (@lem5455767) (@lem5455765)). Qed.
Lemma lem5455769 : term444 = True.
Proof. exact (TRANS (@lem5455764) (@lem5455768)). Qed.
Lemma lem5455770 : True = term444.
Proof. exact (SYM (@lem5455769)). Qed.
Lemma lem5455771 : term444.
Proof. exact (EQ_MP (@lem5455770) (@lem0)). Qed.
Lemma lem5455772 : term697.
Proof. exact (@lem5455761 (@lem5455771)). Qed.
Lemma lem5455774 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455775 : term344 = term345.
Proof. exact (@lem5455774 term120 term120). Qed.
Lemma lem5455776 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455777 : term347 = term120.
Proof. exact (EQ_MP (@lem5455776) (@lem940073)). Qed.
Lemma lem5455778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455779 : term345 = term272.
Proof. exact (MK_COMB (@lem5455778) (@lem5455777)). Qed.
Lemma lem5455780 : term344 = term272.
Proof. exact (TRANS (@lem5455775) (@lem5455779)). Qed.
Lemma lem5455782 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5455783 : term370 = term375.
Proof. exact (@lem5455782 term120 term120). Qed.
Lemma lem5455784 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455785 : term347 = term120.
Proof. exact (EQ_MP (@lem5455784) (@lem940073)). Qed.
Lemma lem5455786 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455787 : term345 = term272.
Proof. exact (MK_COMB (@lem5455786) (@lem5455785)). Qed.
Lemma lem5455788 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5455789 : term375 = term335.
Proof. exact (MK_COMB (@lem5455788) (@lem5455787)). Qed.
Lemma lem5455790 : term370 = term335.
Proof. exact (TRANS (@lem5455783) (@lem5455789)). Qed.
Lemma lem5455791 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455792 : term698 = term690.
Proof. exact (MK_COMB (@lem5455791) (@lem5455790)). Qed.
Lemma lem5455793 : term699 = term692.
Proof. exact (MK_COMB (@lem5455792) (@lem5455780)). Qed.
Lemma lem5455795 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5455796 : term692 = term260.
Proof. exact (@lem5455795 term120). Qed.
Lemma lem5455797 : term699 = term260.
Proof. exact (TRANS (@lem5455793) (@lem5455796)). Qed.
Lemma lem5455798 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455799 : term701 = term454.
Proof. exact (MK_COMB (@lem5455798) (@lem5455797)). Qed.
Lemma lem5455800 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5455801 : term702 = term456.
Proof. exact (MK_COMB (@lem5455799) (@lem5455800)). Qed.
Lemma lem5455803 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455804 : term456 = term260.
Proof. exact (@lem5455803 term120). Qed.
Lemma lem5455805 : term702 = term260.
Proof. exact (TRANS (@lem5455801) (@lem5455804)). Qed.
Lemma lem5455807 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455808 : term344 = term345.
Proof. exact (@lem5455807 term120 term120). Qed.
Lemma lem5455809 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455810 : term347 = term120.
Proof. exact (EQ_MP (@lem5455809) (@lem940073)). Qed.
Lemma lem5455811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455812 : term345 = term272.
Proof. exact (MK_COMB (@lem5455811) (@lem5455810)). Qed.
Lemma lem5455813 : term344 = term272.
Proof. exact (TRANS (@lem5455808) (@lem5455812)). Qed.
Lemma lem5455814 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5455815 : term458 = term456.
Proof. exact (MK_COMB (@lem5455814) (@lem5455813)). Qed.
Lemma lem5455817 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455818 : term456 = term260.
Proof. exact (@lem5455817 term120). Qed.
Lemma lem5455819 : term458 = term260.
Proof. exact (TRANS (@lem5455815) (@lem5455818)). Qed.
Lemma lem5455820 : term260 = term458.
Proof. exact (SYM (@lem5455819)). Qed.
Lemma lem5455821 : term702 = term458.
Proof. exact (TRANS (@lem5455805) (@lem5455820)). Qed.
Lemma lem5455822 : term693 = term332.
Proof. exact (@lem5455772 (@lem5455821)). Qed.
Lemma lem5455823 : term692 = term332.
Proof. exact (TRANS (@lem5455738) (@lem5455822)). Qed.
Lemma lem5455825 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5455826 : term332 = term260.
Proof. exact (@lem5455825 term260). Qed.
Lemma lem5455827 : term692 = term260.
Proof. exact (TRANS (@lem5455823) (@lem5455826)). Qed.
Lemma lem5455828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455829 : term703 = term454.
Proof. exact (MK_COMB (@lem5455828) (@lem5455827)). Qed.
Lemma lem5455830 (_70532 : int) : (real_of_int _70532) = (real_of_int _70532).
Proof. exact (eq_refl (real_of_int _70532)). Qed.
Lemma lem5455831 (_70532 : int) : (term689 _70532) = (term704 _70532).
Proof. exact (MK_COMB (@lem5455829) (@lem5455830 _70532)). Qed.
Lemma lem5455832 (_70532 : int) : (term688 _70532) = (term704 _70532).
Proof. exact (TRANS (@lem5455729 _70532) (@lem5455831 _70532)). Qed.
Lemma lem5455833 (_70532 : int) : (term704 _70532) = term260.
Proof. exact (@lem1982719 (real_of_int _70532)). Qed.
Lemma lem5455834 (_70532 : int) : (term688 _70532) = term260.
Proof. exact (TRANS (@lem5455832 _70532) (@lem5455833 _70532)). Qed.
Lemma lem5455835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455836 (_70532 : int) : (term705 _70532) = term706.
Proof. exact (MK_COMB (@lem5455835) (@lem5455834 _70532)). Qed.
Lemma lem5455837 (_70533 : int) (_70535 : int) : (term434 _70533 _70535) = (term435 _70533 _70535).
Proof. exact (@lem1982755 (real_of_int _70533) term272 (term379 _70535)). Qed.
Lemma lem5455838 (_70535 : int) : (term436 _70535) = (term437 _70535).
Proof. exact (@lem1982757 (term360 _70535) term272 term335). Qed.
Lemma lem5455840 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5455841 : term335 = term336.
Proof. exact (@lem5455840 term120). Qed.
Lemma lem5455843 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455844 : term272 = term369.
Proof. exact (@lem5455843 term120). Qed.
Lemma lem5455845 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455846 : term438 = term439.
Proof. exact (MK_COMB (@lem5455845) (@lem5455844)). Qed.
Lemma lem5455847 : term440 = term441.
Proof. exact (MK_COMB (@lem5455846) (@lem5455841)). Qed.
Lemma lem5455848 : term442.
Proof. exact (@lem1981473 term272 term272 term335 term272 term260 term272). Qed.
Lemma lem5455850 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455851 : term444 = term445.
Proof. exact (@lem5455850 (NUMERAL 0) term120). Qed.
Lemma lem5455852 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455853 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455854 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455853 h1) (fun h1 : term445 = True => @lem5455852)). Qed.
Lemma lem5455855 : term445 = True.
Proof. exact (EQ_MP (@lem5455854) (@lem5455852)). Qed.
Lemma lem5455856 : term444 = True.
Proof. exact (TRANS (@lem5455851) (@lem5455855)). Qed.
Lemma lem5455857 : True = term444.
Proof. exact (SYM (@lem5455856)). Qed.
Lemma lem5455858 : term444.
Proof. exact (EQ_MP (@lem5455857) (@lem0)). Qed.
Lemma lem5455859 : term447.
Proof. exact (@lem5455848 (@lem5455858)). Qed.
Lemma lem5455861 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455862 : term444 = term445.
Proof. exact (@lem5455861 (NUMERAL 0) term120). Qed.
Lemma lem5455863 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455864 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455865 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455864 h1) (fun h1 : term445 = True => @lem5455863)). Qed.
Lemma lem5455866 : term445 = True.
Proof. exact (EQ_MP (@lem5455865) (@lem5455863)). Qed.
Lemma lem5455867 : term444 = True.
Proof. exact (TRANS (@lem5455862) (@lem5455866)). Qed.
Lemma lem5455868 : True = term444.
Proof. exact (SYM (@lem5455867)). Qed.
Lemma lem5455869 : term444.
Proof. exact (EQ_MP (@lem5455868) (@lem0)). Qed.
Lemma lem5455870 : term448.
Proof. exact (@lem5455859 (@lem5455869)). Qed.
Lemma lem5455872 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455873 : term444 = term445.
Proof. exact (@lem5455872 (NUMERAL 0) term120). Qed.
Lemma lem5455874 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455875 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455876 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455875 h1) (fun h1 : term445 = True => @lem5455874)). Qed.
Lemma lem5455877 : term445 = True.
Proof. exact (EQ_MP (@lem5455876) (@lem5455874)). Qed.
Lemma lem5455878 : term444 = True.
Proof. exact (TRANS (@lem5455873) (@lem5455877)). Qed.
Lemma lem5455879 : True = term444.
Proof. exact (SYM (@lem5455878)). Qed.
Lemma lem5455880 : term444.
Proof. exact (EQ_MP (@lem5455879) (@lem0)). Qed.
Lemma lem5455881 : term449.
Proof. exact (@lem5455870 (@lem5455880)). Qed.
Lemma lem5455883 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5455884 : term370 = term375.
Proof. exact (@lem5455883 term120 term120). Qed.
Lemma lem5455885 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455886 : term347 = term120.
Proof. exact (EQ_MP (@lem5455885) (@lem940073)). Qed.
Lemma lem5455887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455888 : term345 = term272.
Proof. exact (MK_COMB (@lem5455887) (@lem5455886)). Qed.
Lemma lem5455889 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5455890 : term375 = term335.
Proof. exact (MK_COMB (@lem5455889) (@lem5455888)). Qed.
Lemma lem5455891 : term370 = term335.
Proof. exact (TRANS (@lem5455884) (@lem5455890)). Qed.
Lemma lem5455893 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455894 : term344 = term345.
Proof. exact (@lem5455893 term120 term120). Qed.
Lemma lem5455895 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455896 : term347 = term120.
Proof. exact (EQ_MP (@lem5455895) (@lem940073)). Qed.
Lemma lem5455897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455898 : term345 = term272.
Proof. exact (MK_COMB (@lem5455897) (@lem5455896)). Qed.
Lemma lem5455899 : term344 = term272.
Proof. exact (TRANS (@lem5455894) (@lem5455898)). Qed.
Lemma lem5455900 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5455901 : term450 = term438.
Proof. exact (MK_COMB (@lem5455900) (@lem5455899)). Qed.
Lemma lem5455902 : term451 = term440.
Proof. exact (MK_COMB (@lem5455901) (@lem5455891)). Qed.
Lemma lem5455904 (m : nat) : (term452 m) = term260.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5455905 : term440 = term260.
Proof. exact (@lem5455904 term120). Qed.
Lemma lem5455906 : term451 = term260.
Proof. exact (TRANS (@lem5455902) (@lem5455905)). Qed.
Lemma lem5455907 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5455908 : term453 = term454.
Proof. exact (MK_COMB (@lem5455907) (@lem5455906)). Qed.
Lemma lem5455909 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5455910 : term455 = term456.
Proof. exact (MK_COMB (@lem5455908) (@lem5455909)). Qed.
Lemma lem5455912 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455913 : term456 = term260.
Proof. exact (@lem5455912 term120). Qed.
Lemma lem5455914 : term455 = term260.
Proof. exact (TRANS (@lem5455910) (@lem5455913)). Qed.
Lemma lem5455916 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455917 : term344 = term345.
Proof. exact (@lem5455916 term120 term120). Qed.
Lemma lem5455918 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455919 : term347 = term120.
Proof. exact (EQ_MP (@lem5455918) (@lem940073)). Qed.
Lemma lem5455920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455921 : term345 = term272.
Proof. exact (MK_COMB (@lem5455920) (@lem5455919)). Qed.
Lemma lem5455922 : term344 = term272.
Proof. exact (TRANS (@lem5455917) (@lem5455921)). Qed.
Lemma lem5455923 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5455924 : term458 = term456.
Proof. exact (MK_COMB (@lem5455923) (@lem5455922)). Qed.
Lemma lem5455926 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455927 : term456 = term260.
Proof. exact (@lem5455926 term120). Qed.
Lemma lem5455928 : term458 = term260.
Proof. exact (TRANS (@lem5455924) (@lem5455927)). Qed.
Lemma lem5455929 : term260 = term458.
Proof. exact (SYM (@lem5455928)). Qed.
Lemma lem5455930 : term455 = term458.
Proof. exact (TRANS (@lem5455914) (@lem5455929)). Qed.
Lemma lem5455931 : term441 = term332.
Proof. exact (@lem5455881 (@lem5455930)). Qed.
Lemma lem5455932 : term440 = term332.
Proof. exact (TRANS (@lem5455847) (@lem5455931)). Qed.
Lemma lem5455934 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5455935 : term332 = term260.
Proof. exact (@lem5455934 term260). Qed.
Lemma lem5455936 : term440 = term260.
Proof. exact (TRANS (@lem5455932) (@lem5455935)). Qed.
Lemma lem5455937 (_70535 : int) : (term378 _70535) = (term378 _70535).
Proof. exact (eq_refl (term378 _70535)). Qed.
Lemma lem5455938 (_70535 : int) : (term437 _70535) = (term459 _70535).
Proof. exact (MK_COMB (@lem5455937 _70535) (@lem5455936)). Qed.
Lemma lem5455939 (_70535 : int) : (term436 _70535) = (term459 _70535).
Proof. exact (TRANS (@lem5455838 _70535) (@lem5455938 _70535)). Qed.
Lemma lem5455940 (_70535 : int) : (term459 _70535) = (term360 _70535).
Proof. exact (@lem1982723 (term360 _70535)). Qed.
Lemma lem5455941 (_70535 : int) : (term436 _70535) = (term360 _70535).
Proof. exact (TRANS (@lem5455939 _70535) (@lem5455940 _70535)). Qed.
Lemma lem5455942 (_70533 : int) : (term273 _70533) = (term273 _70533).
Proof. exact (eq_refl (term273 _70533)). Qed.
Lemma lem5455943 (_70533 : int) (_70535 : int) : (term435 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (MK_COMB (@lem5455942 _70533) (@lem5455941 _70535)). Qed.
Lemma lem5455944 (_70533 : int) (_70535 : int) : (term434 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (TRANS (@lem5455837 _70533 _70535) (@lem5455943 _70533 _70535)). Qed.
Lemma lem5455945 (_70532 : int) (_70533 : int) (_70535 : int) : (term773 _70532 _70533 _70535) = (term774 _70533 _70535).
Proof. exact (MK_COMB (@lem5455836 _70532) (@lem5455944 _70533 _70535)). Qed.
Lemma lem5455946 (_70532 : int) (_70533 : int) (_70535 : int) : (term772 _70533 _70532 _70535) = (term774 _70533 _70535).
Proof. exact (TRANS (@lem5455728 _70532 _70533 _70535) (@lem5455945 _70532 _70533 _70535)). Qed.
Lemma lem5455947 (_70533 : int) (_70535 : int) : (term774 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (@lem1982721 (term404 _70533 _70535)). Qed.
Lemma lem5455948 (_70532 : int) (_70533 : int) (_70535 : int) : (term772 _70533 _70532 _70535) = (term404 _70533 _70535).
Proof. exact (TRANS (@lem5455946 _70532 _70533 _70535) (@lem5455947 _70533 _70535)). Qed.
Lemma lem5455949 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5455950 (_70532 : int) (_70533 : int) (_70535 : int) : (term775 _70533 _70532 _70535) = (term409 _70533 _70535).
Proof. exact (MK_COMB (@lem5455949) (@lem5455948 _70532 _70533 _70535)). Qed.
Lemma lem5455951 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5455952 (_70532 : int) (_70533 : int) (_70535 : int) : (term771 _70533 _70532 _70535) = (term410 _70533 _70535).
Proof. exact (MK_COMB (@lem5455950 _70532 _70533 _70535) (@lem5455951)). Qed.
Lemma lem5455953 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term410 _70533 _70535.
Proof. exact (EQ_MP (@lem5455952 _70532 _70533 _70535) (@lem5455727 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5455955 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5455956 : term663 = term444.
Proof. exact (@lem5455955 term260 term272). Qed.
Lemma lem5455958 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455959 : term272 = term369.
Proof. exact (@lem5455958 term120). Qed.
Lemma lem5455961 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5455962 : term260 = term332.
Proof. exact (@lem5455961 (NUMERAL 0)). Qed.
Lemma lem5455963 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5455964 : term664 = term665.
Proof. exact (MK_COMB (@lem5455963) (@lem5455962)). Qed.
Lemma lem5455965 : term444 = term666.
Proof. exact (MK_COMB (@lem5455964) (@lem5455959)). Qed.
Lemma lem5455966 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5455968 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455969 : term444 = term445.
Proof. exact (@lem5455968 (NUMERAL 0) term120). Qed.
Lemma lem5455970 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455971 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455972 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455971 h1) (fun h1 : term445 = True => @lem5455970)). Qed.
Lemma lem5455973 : term445 = True.
Proof. exact (EQ_MP (@lem5455972) (@lem5455970)). Qed.
Lemma lem5455974 : term444 = True.
Proof. exact (TRANS (@lem5455969) (@lem5455973)). Qed.
Lemma lem5455975 : True = term444.
Proof. exact (SYM (@lem5455974)). Qed.
Lemma lem5455976 : term444.
Proof. exact (EQ_MP (@lem5455975) (@lem0)). Qed.
Lemma lem5455977 : term668.
Proof. exact (@lem5455966 (@lem5455976)). Qed.
Lemma lem5455979 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5455980 : term444 = term445.
Proof. exact (@lem5455979 (NUMERAL 0) term120). Qed.
Lemma lem5455981 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5455982 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5455983 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5455982 h1) (fun h1 : term445 = True => @lem5455981)). Qed.
Lemma lem5455984 : term445 = True.
Proof. exact (EQ_MP (@lem5455983) (@lem5455981)). Qed.
Lemma lem5455985 : term444 = True.
Proof. exact (TRANS (@lem5455980) (@lem5455984)). Qed.
Lemma lem5455986 : True = term444.
Proof. exact (SYM (@lem5455985)). Qed.
Lemma lem5455987 : term444.
Proof. exact (EQ_MP (@lem5455986) (@lem0)). Qed.
Lemma lem5455988 : term666 = term669.
Proof. exact (@lem5455977 (@lem5455987)). Qed.
Lemma lem5455990 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5455991 : term344 = term345.
Proof. exact (@lem5455990 term120 term120). Qed.
Lemma lem5455992 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5455993 : term347 = term120.
Proof. exact (EQ_MP (@lem5455992) (@lem940073)). Qed.
Lemma lem5455994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5455995 : term345 = term272.
Proof. exact (MK_COMB (@lem5455994) (@lem5455993)). Qed.
Lemma lem5455996 : term344 = term272.
Proof. exact (TRANS (@lem5455991) (@lem5455995)). Qed.
Lemma lem5455998 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5455999 : term456 = term260.
Proof. exact (@lem5455998 term120). Qed.
Lemma lem5456000 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5456001 : term670 = term664.
Proof. exact (MK_COMB (@lem5456000) (@lem5455999)). Qed.
Lemma lem5456002 : term669 = term444.
Proof. exact (MK_COMB (@lem5456001) (@lem5455996)). Qed.
Lemma lem5456004 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456005 : term444 = term445.
Proof. exact (@lem5456004 (NUMERAL 0) term120). Qed.
Lemma lem5456006 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456007 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456008 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456007 h1) (fun h1 : term445 = True => @lem5456006)). Qed.
Lemma lem5456009 : term445 = True.
Proof. exact (EQ_MP (@lem5456008) (@lem5456006)). Qed.
Lemma lem5456010 : term444 = True.
Proof. exact (TRANS (@lem5456005) (@lem5456009)). Qed.
Lemma lem5456011 : term669 = True.
Proof. exact (TRANS (@lem5456002) (@lem5456010)). Qed.
Lemma lem5456012 : term666 = True.
Proof. exact (TRANS (@lem5455988) (@lem5456011)). Qed.
Lemma lem5456013 : term444 = True.
Proof. exact (TRANS (@lem5455965) (@lem5456012)). Qed.
Lemma lem5456014 : term663 = True.
Proof. exact (TRANS (@lem5455956) (@lem5456013)). Qed.
Lemma lem5456015 : True = term663.
Proof. exact (SYM (@lem5456014)). Qed.
Lemma lem5456016 : term663.
Proof. exact (EQ_MP (@lem5456015) (@lem0)). Qed.
Lemma lem5456017 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term727 _70533 _70535.
Proof. exact (conj (@lem5456016) (@lem5455953 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456019 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5456020 (_70533 : int) (_70535 : int) : term728 _70533 _70535.
Proof. exact (@lem5456019 term272 (term404 _70533 _70535)). Qed.
Lemma lem5456021 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term729 _70533 _70535.
Proof. exact (@lem5456020 _70533 _70535 (@lem5456017 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456022 (_70533 : int) (_70535 : int) : (term730 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (@lem1982733 (term404 _70533 _70535)). Qed.
Lemma lem5456023 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5456024 (_70533 : int) (_70535 : int) : (term731 _70533 _70535) = (term409 _70533 _70535).
Proof. exact (MK_COMB (@lem5456023) (@lem5456022 _70533 _70535)). Qed.
Lemma lem5456025 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5456026 (_70533 : int) (_70535 : int) : (term729 _70533 _70535) = (term410 _70533 _70535).
Proof. exact (MK_COMB (@lem5456024 _70533 _70535) (@lem5456025)). Qed.
Lemma lem5456027 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term410 _70533 _70535.
Proof. exact (EQ_MP (@lem5456026 _70533 _70535) (@lem5456021 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456028 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term776 _70533 _70535.
Proof. exact (conj (@lem5456027 _70532 _70533 _70534 _70535 h1) (@lem5455574 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456030 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5456031 (_70533 : int) (_70535 : int) : term777 _70533 _70535.
Proof. exact (@lem5456030 (term404 _70533 _70535) (term395 _70533 _70535)). Qed.
Lemma lem5456032 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term778 _70533 _70535.
Proof. exact (@lem5456031 _70533 _70535 (@lem5456028 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456033 (_70533 : int) (_70535 : int) : (term779 _70533 _70535) = (term780 _70533 _70535).
Proof. exact (@lem1982753 (real_of_int _70533) (term360 _70533) (term360 _70535) (term749 _70535)). Qed.
Lemma lem5456034 (_70533 : int) : (term709 _70533) = (term689 _70533).
Proof. exact (@lem1982715 term335 (real_of_int _70533)). Qed.
Lemma lem5456036 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456037 : term272 = term369.
Proof. exact (@lem5456036 term120). Qed.
Lemma lem5456039 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5456040 : term335 = term336.
Proof. exact (@lem5456039 term120). Qed.
Lemma lem5456041 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456042 : term690 = term691.
Proof. exact (MK_COMB (@lem5456041) (@lem5456040)). Qed.
Lemma lem5456043 : term692 = term693.
Proof. exact (MK_COMB (@lem5456042) (@lem5456037)). Qed.
Lemma lem5456044 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5456046 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456047 : term444 = term445.
Proof. exact (@lem5456046 (NUMERAL 0) term120). Qed.
Lemma lem5456048 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456049 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456050 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456049 h1) (fun h1 : term445 = True => @lem5456048)). Qed.
Lemma lem5456051 : term445 = True.
Proof. exact (EQ_MP (@lem5456050) (@lem5456048)). Qed.
Lemma lem5456052 : term444 = True.
Proof. exact (TRANS (@lem5456047) (@lem5456051)). Qed.
Lemma lem5456053 : True = term444.
Proof. exact (SYM (@lem5456052)). Qed.
Lemma lem5456054 : term444.
Proof. exact (EQ_MP (@lem5456053) (@lem0)). Qed.
Lemma lem5456055 : term695.
Proof. exact (@lem5456044 (@lem5456054)). Qed.
Lemma lem5456057 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456058 : term444 = term445.
Proof. exact (@lem5456057 (NUMERAL 0) term120). Qed.
Lemma lem5456059 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456060 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456061 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456060 h1) (fun h1 : term445 = True => @lem5456059)). Qed.
Lemma lem5456062 : term445 = True.
Proof. exact (EQ_MP (@lem5456061) (@lem5456059)). Qed.
Lemma lem5456063 : term444 = True.
Proof. exact (TRANS (@lem5456058) (@lem5456062)). Qed.
Lemma lem5456064 : True = term444.
Proof. exact (SYM (@lem5456063)). Qed.
Lemma lem5456065 : term444.
Proof. exact (EQ_MP (@lem5456064) (@lem0)). Qed.
Lemma lem5456066 : term696.
Proof. exact (@lem5456055 (@lem5456065)). Qed.
Lemma lem5456068 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456069 : term444 = term445.
Proof. exact (@lem5456068 (NUMERAL 0) term120). Qed.
Lemma lem5456070 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456071 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456072 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456071 h1) (fun h1 : term445 = True => @lem5456070)). Qed.
Lemma lem5456073 : term445 = True.
Proof. exact (EQ_MP (@lem5456072) (@lem5456070)). Qed.
Lemma lem5456074 : term444 = True.
Proof. exact (TRANS (@lem5456069) (@lem5456073)). Qed.
Lemma lem5456075 : True = term444.
Proof. exact (SYM (@lem5456074)). Qed.
Lemma lem5456076 : term444.
Proof. exact (EQ_MP (@lem5456075) (@lem0)). Qed.
Lemma lem5456077 : term697.
Proof. exact (@lem5456066 (@lem5456076)). Qed.
Lemma lem5456079 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456080 : term344 = term345.
Proof. exact (@lem5456079 term120 term120). Qed.
Lemma lem5456081 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456082 : term347 = term120.
Proof. exact (EQ_MP (@lem5456081) (@lem940073)). Qed.
Lemma lem5456083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456084 : term345 = term272.
Proof. exact (MK_COMB (@lem5456083) (@lem5456082)). Qed.
Lemma lem5456085 : term344 = term272.
Proof. exact (TRANS (@lem5456080) (@lem5456084)). Qed.
Lemma lem5456087 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5456088 : term370 = term375.
Proof. exact (@lem5456087 term120 term120). Qed.
Lemma lem5456089 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456090 : term347 = term120.
Proof. exact (EQ_MP (@lem5456089) (@lem940073)). Qed.
Lemma lem5456091 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456092 : term345 = term272.
Proof. exact (MK_COMB (@lem5456091) (@lem5456090)). Qed.
Lemma lem5456093 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5456094 : term375 = term335.
Proof. exact (MK_COMB (@lem5456093) (@lem5456092)). Qed.
Lemma lem5456095 : term370 = term335.
Proof. exact (TRANS (@lem5456088) (@lem5456094)). Qed.
Lemma lem5456096 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456097 : term698 = term690.
Proof. exact (MK_COMB (@lem5456096) (@lem5456095)). Qed.
Lemma lem5456098 : term699 = term692.
Proof. exact (MK_COMB (@lem5456097) (@lem5456085)). Qed.
Lemma lem5456100 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5456101 : term692 = term260.
Proof. exact (@lem5456100 term120). Qed.
Lemma lem5456102 : term699 = term260.
Proof. exact (TRANS (@lem5456098) (@lem5456101)). Qed.
Lemma lem5456103 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456104 : term701 = term454.
Proof. exact (MK_COMB (@lem5456103) (@lem5456102)). Qed.
Lemma lem5456105 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5456106 : term702 = term456.
Proof. exact (MK_COMB (@lem5456104) (@lem5456105)). Qed.
Lemma lem5456108 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456109 : term456 = term260.
Proof. exact (@lem5456108 term120). Qed.
Lemma lem5456110 : term702 = term260.
Proof. exact (TRANS (@lem5456106) (@lem5456109)). Qed.
Lemma lem5456112 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456113 : term344 = term345.
Proof. exact (@lem5456112 term120 term120). Qed.
Lemma lem5456114 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456115 : term347 = term120.
Proof. exact (EQ_MP (@lem5456114) (@lem940073)). Qed.
Lemma lem5456116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456117 : term345 = term272.
Proof. exact (MK_COMB (@lem5456116) (@lem5456115)). Qed.
Lemma lem5456118 : term344 = term272.
Proof. exact (TRANS (@lem5456113) (@lem5456117)). Qed.
Lemma lem5456119 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5456120 : term458 = term456.
Proof. exact (MK_COMB (@lem5456119) (@lem5456118)). Qed.
Lemma lem5456122 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456123 : term456 = term260.
Proof. exact (@lem5456122 term120). Qed.
Lemma lem5456124 : term458 = term260.
Proof. exact (TRANS (@lem5456120) (@lem5456123)). Qed.
Lemma lem5456125 : term260 = term458.
Proof. exact (SYM (@lem5456124)). Qed.
Lemma lem5456126 : term702 = term458.
Proof. exact (TRANS (@lem5456110) (@lem5456125)). Qed.
Lemma lem5456127 : term693 = term332.
Proof. exact (@lem5456077 (@lem5456126)). Qed.
Lemma lem5456128 : term692 = term332.
Proof. exact (TRANS (@lem5456043) (@lem5456127)). Qed.
Lemma lem5456130 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5456131 : term332 = term260.
Proof. exact (@lem5456130 term260). Qed.
Lemma lem5456132 : term692 = term260.
Proof. exact (TRANS (@lem5456128) (@lem5456131)). Qed.
Lemma lem5456133 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456134 : term703 = term454.
Proof. exact (MK_COMB (@lem5456133) (@lem5456132)). Qed.
Lemma lem5456135 (_70533 : int) : (real_of_int _70533) = (real_of_int _70533).
Proof. exact (eq_refl (real_of_int _70533)). Qed.
Lemma lem5456136 (_70533 : int) : (term689 _70533) = (term704 _70533).
Proof. exact (MK_COMB (@lem5456134) (@lem5456135 _70533)). Qed.
Lemma lem5456137 (_70533 : int) : (term709 _70533) = (term704 _70533).
Proof. exact (TRANS (@lem5456034 _70533) (@lem5456136 _70533)). Qed.
Lemma lem5456138 (_70533 : int) : (term704 _70533) = term260.
Proof. exact (@lem1982719 (real_of_int _70533)). Qed.
Lemma lem5456139 (_70533 : int) : (term709 _70533) = term260.
Proof. exact (TRANS (@lem5456137 _70533) (@lem5456138 _70533)). Qed.
Lemma lem5456140 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456141 (_70533 : int) : (term710 _70533) = term706.
Proof. exact (MK_COMB (@lem5456140) (@lem5456139 _70533)). Qed.
Lemma lem5456142 (_70535 : int) : (term781 _70535) = (term782 _70535).
Proof. exact (@lem1982763 (term360 _70535) (real_of_int _70535) term335). Qed.
Lemma lem5456143 (_70535 : int) : (term688 _70535) = (term689 _70535).
Proof. exact (@lem1982713 term335 (real_of_int _70535)). Qed.
Lemma lem5456145 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456146 : term272 = term369.
Proof. exact (@lem5456145 term120). Qed.
Lemma lem5456148 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5456149 : term335 = term336.
Proof. exact (@lem5456148 term120). Qed.
Lemma lem5456150 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456151 : term690 = term691.
Proof. exact (MK_COMB (@lem5456150) (@lem5456149)). Qed.
Lemma lem5456152 : term692 = term693.
Proof. exact (MK_COMB (@lem5456151) (@lem5456146)). Qed.
Lemma lem5456153 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5456155 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456156 : term444 = term445.
Proof. exact (@lem5456155 (NUMERAL 0) term120). Qed.
Lemma lem5456157 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456158 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456159 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456158 h1) (fun h1 : term445 = True => @lem5456157)). Qed.
Lemma lem5456160 : term445 = True.
Proof. exact (EQ_MP (@lem5456159) (@lem5456157)). Qed.
Lemma lem5456161 : term444 = True.
Proof. exact (TRANS (@lem5456156) (@lem5456160)). Qed.
Lemma lem5456162 : True = term444.
Proof. exact (SYM (@lem5456161)). Qed.
Lemma lem5456163 : term444.
Proof. exact (EQ_MP (@lem5456162) (@lem0)). Qed.
Lemma lem5456164 : term695.
Proof. exact (@lem5456153 (@lem5456163)). Qed.
Lemma lem5456166 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456167 : term444 = term445.
Proof. exact (@lem5456166 (NUMERAL 0) term120). Qed.
Lemma lem5456168 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456169 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456170 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456169 h1) (fun h1 : term445 = True => @lem5456168)). Qed.
Lemma lem5456171 : term445 = True.
Proof. exact (EQ_MP (@lem5456170) (@lem5456168)). Qed.
Lemma lem5456172 : term444 = True.
Proof. exact (TRANS (@lem5456167) (@lem5456171)). Qed.
Lemma lem5456173 : True = term444.
Proof. exact (SYM (@lem5456172)). Qed.
Lemma lem5456174 : term444.
Proof. exact (EQ_MP (@lem5456173) (@lem0)). Qed.
Lemma lem5456175 : term696.
Proof. exact (@lem5456164 (@lem5456174)). Qed.
Lemma lem5456177 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456178 : term444 = term445.
Proof. exact (@lem5456177 (NUMERAL 0) term120). Qed.
Lemma lem5456179 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456180 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456181 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456180 h1) (fun h1 : term445 = True => @lem5456179)). Qed.
Lemma lem5456182 : term445 = True.
Proof. exact (EQ_MP (@lem5456181) (@lem5456179)). Qed.
Lemma lem5456183 : term444 = True.
Proof. exact (TRANS (@lem5456178) (@lem5456182)). Qed.
Lemma lem5456184 : True = term444.
Proof. exact (SYM (@lem5456183)). Qed.
Lemma lem5456185 : term444.
Proof. exact (EQ_MP (@lem5456184) (@lem0)). Qed.
Lemma lem5456186 : term697.
Proof. exact (@lem5456175 (@lem5456185)). Qed.
Lemma lem5456188 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456189 : term344 = term345.
Proof. exact (@lem5456188 term120 term120). Qed.
Lemma lem5456190 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456191 : term347 = term120.
Proof. exact (EQ_MP (@lem5456190) (@lem940073)). Qed.
Lemma lem5456192 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456193 : term345 = term272.
Proof. exact (MK_COMB (@lem5456192) (@lem5456191)). Qed.
Lemma lem5456194 : term344 = term272.
Proof. exact (TRANS (@lem5456189) (@lem5456193)). Qed.
Lemma lem5456196 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5456197 : term370 = term375.
Proof. exact (@lem5456196 term120 term120). Qed.
Lemma lem5456198 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456199 : term347 = term120.
Proof. exact (EQ_MP (@lem5456198) (@lem940073)). Qed.
Lemma lem5456200 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456201 : term345 = term272.
Proof. exact (MK_COMB (@lem5456200) (@lem5456199)). Qed.
Lemma lem5456202 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5456203 : term375 = term335.
Proof. exact (MK_COMB (@lem5456202) (@lem5456201)). Qed.
Lemma lem5456204 : term370 = term335.
Proof. exact (TRANS (@lem5456197) (@lem5456203)). Qed.
Lemma lem5456205 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456206 : term698 = term690.
Proof. exact (MK_COMB (@lem5456205) (@lem5456204)). Qed.
Lemma lem5456207 : term699 = term692.
Proof. exact (MK_COMB (@lem5456206) (@lem5456194)). Qed.
Lemma lem5456209 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5456210 : term692 = term260.
Proof. exact (@lem5456209 term120). Qed.
Lemma lem5456211 : term699 = term260.
Proof. exact (TRANS (@lem5456207) (@lem5456210)). Qed.
Lemma lem5456212 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456213 : term701 = term454.
Proof. exact (MK_COMB (@lem5456212) (@lem5456211)). Qed.
Lemma lem5456214 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5456215 : term702 = term456.
Proof. exact (MK_COMB (@lem5456213) (@lem5456214)). Qed.
Lemma lem5456217 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456218 : term456 = term260.
Proof. exact (@lem5456217 term120). Qed.
Lemma lem5456219 : term702 = term260.
Proof. exact (TRANS (@lem5456215) (@lem5456218)). Qed.
Lemma lem5456221 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456222 : term344 = term345.
Proof. exact (@lem5456221 term120 term120). Qed.
Lemma lem5456223 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456224 : term347 = term120.
Proof. exact (EQ_MP (@lem5456223) (@lem940073)). Qed.
Lemma lem5456225 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456226 : term345 = term272.
Proof. exact (MK_COMB (@lem5456225) (@lem5456224)). Qed.
Lemma lem5456227 : term344 = term272.
Proof. exact (TRANS (@lem5456222) (@lem5456226)). Qed.
Lemma lem5456228 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5456229 : term458 = term456.
Proof. exact (MK_COMB (@lem5456228) (@lem5456227)). Qed.
Lemma lem5456231 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456232 : term456 = term260.
Proof. exact (@lem5456231 term120). Qed.
Lemma lem5456233 : term458 = term260.
Proof. exact (TRANS (@lem5456229) (@lem5456232)). Qed.
Lemma lem5456234 : term260 = term458.
Proof. exact (SYM (@lem5456233)). Qed.
Lemma lem5456235 : term702 = term458.
Proof. exact (TRANS (@lem5456219) (@lem5456234)). Qed.
Lemma lem5456236 : term693 = term332.
Proof. exact (@lem5456186 (@lem5456235)). Qed.
Lemma lem5456237 : term692 = term332.
Proof. exact (TRANS (@lem5456152) (@lem5456236)). Qed.
Lemma lem5456239 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5456240 : term332 = term260.
Proof. exact (@lem5456239 term260). Qed.
Lemma lem5456241 : term692 = term260.
Proof. exact (TRANS (@lem5456237) (@lem5456240)). Qed.
Lemma lem5456242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456243 : term703 = term454.
Proof. exact (MK_COMB (@lem5456242) (@lem5456241)). Qed.
Lemma lem5456244 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5456245 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5456243) (@lem5456244 _70535)). Qed.
Lemma lem5456246 (_70535 : int) : (term688 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5456143 _70535) (@lem5456245 _70535)). Qed.
Lemma lem5456247 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5456248 (_70535 : int) : (term688 _70535) = term260.
Proof. exact (TRANS (@lem5456246 _70535) (@lem5456247 _70535)). Qed.
Lemma lem5456249 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456250 (_70535 : int) : (term705 _70535) = term706.
Proof. exact (MK_COMB (@lem5456249) (@lem5456248 _70535)). Qed.
Lemma lem5456251 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5456252 (_70535 : int) : (term782 _70535) = term711.
Proof. exact (MK_COMB (@lem5456250 _70535) (@lem5456251)). Qed.
Lemma lem5456253 (_70535 : int) : (term781 _70535) = term711.
Proof. exact (TRANS (@lem5456142 _70535) (@lem5456252 _70535)). Qed.
Lemma lem5456254 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5456255 (_70535 : int) : (term781 _70535) = term335.
Proof. exact (TRANS (@lem5456253 _70535) (@lem5456254)). Qed.
Lemma lem5456256 (_70533 : int) (_70535 : int) : (term780 _70533 _70535) = term711.
Proof. exact (MK_COMB (@lem5456141 _70533) (@lem5456255 _70535)). Qed.
Lemma lem5456257 (_70533 : int) (_70535 : int) : (term779 _70533 _70535) = term711.
Proof. exact (TRANS (@lem5456033 _70533 _70535) (@lem5456256 _70533 _70535)). Qed.
Lemma lem5456258 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5456259 (_70533 : int) (_70535 : int) : (term779 _70533 _70535) = term335.
Proof. exact (TRANS (@lem5456257 _70533 _70535) (@lem5456258)). Qed.
Lemma lem5456260 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5456261 (_70533 : int) (_70535 : int) : (term783 _70533 _70535) = term713.
Proof. exact (MK_COMB (@lem5456260) (@lem5456259 _70533 _70535)). Qed.
Lemma lem5456262 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5456263 (_70533 : int) (_70535 : int) : (term778 _70533 _70535) = term714.
Proof. exact (MK_COMB (@lem5456261 _70533 _70535) (@lem5456262)). Qed.
Lemma lem5456264 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : term714.
Proof. exact (EQ_MP (@lem5456263 _70533 _70535) (@lem5456032 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456266 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5456267 : term714 = term715.
Proof. exact (@lem5456266 term260 term335). Qed.
Lemma lem5456269 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5456270 : term335 = term336.
Proof. exact (@lem5456269 term120). Qed.
Lemma lem5456272 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456273 : term260 = term332.
Proof. exact (@lem5456272 (NUMERAL 0)). Qed.
Lemma lem5456274 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5456275 : term262 = term716.
Proof. exact (MK_COMB (@lem5456274) (@lem5456273)). Qed.
Lemma lem5456276 : term715 = term717.
Proof. exact (MK_COMB (@lem5456275) (@lem5456270)). Qed.
Lemma lem5456277 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5456279 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456280 : term444 = term445.
Proof. exact (@lem5456279 (NUMERAL 0) term120). Qed.
Lemma lem5456281 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456282 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456283 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456282 h1) (fun h1 : term445 = True => @lem5456281)). Qed.
Lemma lem5456284 : term445 = True.
Proof. exact (EQ_MP (@lem5456283) (@lem5456281)). Qed.
Lemma lem5456285 : term444 = True.
Proof. exact (TRANS (@lem5456280) (@lem5456284)). Qed.
Lemma lem5456286 : True = term444.
Proof. exact (SYM (@lem5456285)). Qed.
Lemma lem5456287 : term444.
Proof. exact (EQ_MP (@lem5456286) (@lem0)). Qed.
Lemma lem5456288 : term719.
Proof. exact (@lem5456277 (@lem5456287)). Qed.
Lemma lem5456290 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456291 : term444 = term445.
Proof. exact (@lem5456290 (NUMERAL 0) term120). Qed.
Lemma lem5456292 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456293 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456294 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456293 h1) (fun h1 : term445 = True => @lem5456292)). Qed.
Lemma lem5456295 : term445 = True.
Proof. exact (EQ_MP (@lem5456294) (@lem5456292)). Qed.
Lemma lem5456296 : term444 = True.
Proof. exact (TRANS (@lem5456291) (@lem5456295)). Qed.
Lemma lem5456297 : True = term444.
Proof. exact (SYM (@lem5456296)). Qed.
Lemma lem5456298 : term444.
Proof. exact (EQ_MP (@lem5456297) (@lem0)). Qed.
Lemma lem5456299 : term717 = term720.
Proof. exact (@lem5456288 (@lem5456298)). Qed.
Lemma lem5456301 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5456302 : term370 = term375.
Proof. exact (@lem5456301 term120 term120). Qed.
Lemma lem5456303 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456304 : term347 = term120.
Proof. exact (EQ_MP (@lem5456303) (@lem940073)). Qed.
Lemma lem5456305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456306 : term345 = term272.
Proof. exact (MK_COMB (@lem5456305) (@lem5456304)). Qed.
Lemma lem5456307 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5456308 : term375 = term335.
Proof. exact (MK_COMB (@lem5456307) (@lem5456306)). Qed.
Lemma lem5456309 : term370 = term335.
Proof. exact (TRANS (@lem5456302) (@lem5456308)). Qed.
Lemma lem5456311 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456312 : term456 = term260.
Proof. exact (@lem5456311 term120). Qed.
Lemma lem5456313 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5456314 : term721 = term262.
Proof. exact (MK_COMB (@lem5456313) (@lem5456312)). Qed.
Lemma lem5456315 : term720 = term715.
Proof. exact (MK_COMB (@lem5456314) (@lem5456309)). Qed.
Lemma lem5456317 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5456318 : term715 = term724.
Proof. exact (@lem5456317 (NUMERAL 0) term120). Qed.
Lemma lem5456319 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456320 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5456321 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456320 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5456319)). Qed.
Lemma lem5456322 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5456321) (@lem5456319)). Qed.
Lemma lem5456323 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5456324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5456325 : term725 = (and True).
Proof. exact (MK_COMB (@lem5456324) (@lem5456323)). Qed.
Lemma lem5456326 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5456325) (@lem5456322)). Qed.
Lemma lem5456328 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5456329 : term724 = False.
Proof. exact (TRANS (@lem5456326) (@lem5456328)). Qed.
Lemma lem5456330 : term715 = False.
Proof. exact (TRANS (@lem5456318) (@lem5456329)). Qed.
Lemma lem5456331 : term720 = False.
Proof. exact (TRANS (@lem5456315) (@lem5456330)). Qed.
Lemma lem5456332 : term717 = False.
Proof. exact (TRANS (@lem5456299) (@lem5456331)). Qed.
Lemma lem5456333 : term715 = False.
Proof. exact (TRANS (@lem5456276) (@lem5456332)). Qed.
Lemma lem5456334 : term714 = False.
Proof. exact (TRANS (@lem5456267) (@lem5456333)). Qed.
Lemma lem5456335 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term763 _70532 _70533 _70534 _70535) : False.
Proof. exact (EQ_MP (@lem5456334) (@lem5456264 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456336 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term784 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5456337 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term651 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5456336 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456339 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term620 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5456337 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456341 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term589 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5456339 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456343 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term558 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5456341 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456345 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term527 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5456343 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456347 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term423 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5456345 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456348 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term399 _70533 _70534 _70535.
Proof. exact (proj1 (@lem5456345 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456349 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term421 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5456347 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456352 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5456353 : term663 = term444.
Proof. exact (@lem5456352 term260 term272). Qed.
Lemma lem5456355 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456356 : term272 = term369.
Proof. exact (@lem5456355 term120). Qed.
Lemma lem5456358 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456359 : term260 = term332.
Proof. exact (@lem5456358 (NUMERAL 0)). Qed.
Lemma lem5456360 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5456361 : term664 = term665.
Proof. exact (MK_COMB (@lem5456360) (@lem5456359)). Qed.
Lemma lem5456362 : term444 = term666.
Proof. exact (MK_COMB (@lem5456361) (@lem5456356)). Qed.
Lemma lem5456363 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5456365 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456366 : term444 = term445.
Proof. exact (@lem5456365 (NUMERAL 0) term120). Qed.
Lemma lem5456367 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456368 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456369 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456368 h1) (fun h1 : term445 = True => @lem5456367)). Qed.
Lemma lem5456370 : term445 = True.
Proof. exact (EQ_MP (@lem5456369) (@lem5456367)). Qed.
Lemma lem5456371 : term444 = True.
Proof. exact (TRANS (@lem5456366) (@lem5456370)). Qed.
Lemma lem5456372 : True = term444.
Proof. exact (SYM (@lem5456371)). Qed.
Lemma lem5456373 : term444.
Proof. exact (EQ_MP (@lem5456372) (@lem0)). Qed.
Lemma lem5456374 : term668.
Proof. exact (@lem5456363 (@lem5456373)). Qed.
Lemma lem5456376 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456377 : term444 = term445.
Proof. exact (@lem5456376 (NUMERAL 0) term120). Qed.
Lemma lem5456378 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456379 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456380 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456379 h1) (fun h1 : term445 = True => @lem5456378)). Qed.
Lemma lem5456381 : term445 = True.
Proof. exact (EQ_MP (@lem5456380) (@lem5456378)). Qed.
Lemma lem5456382 : term444 = True.
Proof. exact (TRANS (@lem5456377) (@lem5456381)). Qed.
Lemma lem5456383 : True = term444.
Proof. exact (SYM (@lem5456382)). Qed.
Lemma lem5456384 : term444.
Proof. exact (EQ_MP (@lem5456383) (@lem0)). Qed.
Lemma lem5456385 : term666 = term669.
Proof. exact (@lem5456374 (@lem5456384)). Qed.
Lemma lem5456387 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456388 : term344 = term345.
Proof. exact (@lem5456387 term120 term120). Qed.
Lemma lem5456389 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456390 : term347 = term120.
Proof. exact (EQ_MP (@lem5456389) (@lem940073)). Qed.
Lemma lem5456391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456392 : term345 = term272.
Proof. exact (MK_COMB (@lem5456391) (@lem5456390)). Qed.
Lemma lem5456393 : term344 = term272.
Proof. exact (TRANS (@lem5456388) (@lem5456392)). Qed.
Lemma lem5456395 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456396 : term456 = term260.
Proof. exact (@lem5456395 term120). Qed.
Lemma lem5456397 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5456398 : term670 = term664.
Proof. exact (MK_COMB (@lem5456397) (@lem5456396)). Qed.
Lemma lem5456399 : term669 = term444.
Proof. exact (MK_COMB (@lem5456398) (@lem5456393)). Qed.
Lemma lem5456401 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456402 : term444 = term445.
Proof. exact (@lem5456401 (NUMERAL 0) term120). Qed.
Lemma lem5456403 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456404 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456405 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456404 h1) (fun h1 : term445 = True => @lem5456403)). Qed.
Lemma lem5456406 : term445 = True.
Proof. exact (EQ_MP (@lem5456405) (@lem5456403)). Qed.
Lemma lem5456407 : term444 = True.
Proof. exact (TRANS (@lem5456402) (@lem5456406)). Qed.
Lemma lem5456408 : term669 = True.
Proof. exact (TRANS (@lem5456399) (@lem5456407)). Qed.
Lemma lem5456409 : term666 = True.
Proof. exact (TRANS (@lem5456385) (@lem5456408)). Qed.
Lemma lem5456410 : term444 = True.
Proof. exact (TRANS (@lem5456362) (@lem5456409)). Qed.
Lemma lem5456411 : term663 = True.
Proof. exact (TRANS (@lem5456353) (@lem5456410)). Qed.
Lemma lem5456412 : True = term663.
Proof. exact (SYM (@lem5456411)). Qed.
Lemma lem5456413 : term663.
Proof. exact (EQ_MP (@lem5456412) (@lem0)). Qed.
Lemma lem5456414 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term785 _70533 _70534 _70535.
Proof. exact (conj (@lem5456413) (@lem5456349 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456416 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5456417 (_70533 : int) (_70534 : int) (_70535 : int) : term786 _70533 _70534 _70535.
Proof. exact (@lem5456416 term272 (term418 _70533 _70534 _70535)). Qed.
Lemma lem5456418 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term787 _70533 _70534 _70535.
Proof. exact (@lem5456417 _70533 _70534 _70535 (@lem5456414 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456419 (_70533 : int) (_70534 : int) (_70535 : int) : (term788 _70533 _70534 _70535) = (term418 _70533 _70534 _70535).
Proof. exact (@lem1982733 (term418 _70533 _70534 _70535)). Qed.
Lemma lem5456420 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5456421 (_70533 : int) (_70534 : int) (_70535 : int) : (term789 _70533 _70534 _70535) = (term420 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5456420) (@lem5456419 _70533 _70534 _70535)). Qed.
Lemma lem5456422 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5456423 (_70533 : int) (_70534 : int) (_70535 : int) : (term787 _70533 _70534 _70535) = (term421 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5456421 _70533 _70534 _70535) (@lem5456422)). Qed.
Lemma lem5456424 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term421 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5456423 _70533 _70534 _70535) (@lem5456418 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456426 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5456427 : term663 = term444.
Proof. exact (@lem5456426 term260 term272). Qed.
Lemma lem5456429 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456430 : term272 = term369.
Proof. exact (@lem5456429 term120). Qed.
Lemma lem5456432 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456433 : term260 = term332.
Proof. exact (@lem5456432 (NUMERAL 0)). Qed.
Lemma lem5456434 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5456435 : term664 = term665.
Proof. exact (MK_COMB (@lem5456434) (@lem5456433)). Qed.
Lemma lem5456436 : term444 = term666.
Proof. exact (MK_COMB (@lem5456435) (@lem5456430)). Qed.
Lemma lem5456437 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5456439 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456440 : term444 = term445.
Proof. exact (@lem5456439 (NUMERAL 0) term120). Qed.
Lemma lem5456441 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456442 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456443 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456442 h1) (fun h1 : term445 = True => @lem5456441)). Qed.
Lemma lem5456444 : term445 = True.
Proof. exact (EQ_MP (@lem5456443) (@lem5456441)). Qed.
Lemma lem5456445 : term444 = True.
Proof. exact (TRANS (@lem5456440) (@lem5456444)). Qed.
Lemma lem5456446 : True = term444.
Proof. exact (SYM (@lem5456445)). Qed.
Lemma lem5456447 : term444.
Proof. exact (EQ_MP (@lem5456446) (@lem0)). Qed.
Lemma lem5456448 : term668.
Proof. exact (@lem5456437 (@lem5456447)). Qed.
Lemma lem5456450 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456451 : term444 = term445.
Proof. exact (@lem5456450 (NUMERAL 0) term120). Qed.
Lemma lem5456452 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456453 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456454 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456453 h1) (fun h1 : term445 = True => @lem5456452)). Qed.
Lemma lem5456455 : term445 = True.
Proof. exact (EQ_MP (@lem5456454) (@lem5456452)). Qed.
Lemma lem5456456 : term444 = True.
Proof. exact (TRANS (@lem5456451) (@lem5456455)). Qed.
Lemma lem5456457 : True = term444.
Proof. exact (SYM (@lem5456456)). Qed.
Lemma lem5456458 : term444.
Proof. exact (EQ_MP (@lem5456457) (@lem0)). Qed.
Lemma lem5456459 : term666 = term669.
Proof. exact (@lem5456448 (@lem5456458)). Qed.
Lemma lem5456461 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456462 : term344 = term345.
Proof. exact (@lem5456461 term120 term120). Qed.
Lemma lem5456463 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456464 : term347 = term120.
Proof. exact (EQ_MP (@lem5456463) (@lem940073)). Qed.
Lemma lem5456465 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456466 : term345 = term272.
Proof. exact (MK_COMB (@lem5456465) (@lem5456464)). Qed.
Lemma lem5456467 : term344 = term272.
Proof. exact (TRANS (@lem5456462) (@lem5456466)). Qed.
Lemma lem5456469 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456470 : term456 = term260.
Proof. exact (@lem5456469 term120). Qed.
Lemma lem5456471 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5456472 : term670 = term664.
Proof. exact (MK_COMB (@lem5456471) (@lem5456470)). Qed.
Lemma lem5456473 : term669 = term444.
Proof. exact (MK_COMB (@lem5456472) (@lem5456467)). Qed.
Lemma lem5456475 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456476 : term444 = term445.
Proof. exact (@lem5456475 (NUMERAL 0) term120). Qed.
Lemma lem5456477 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456478 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456479 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456478 h1) (fun h1 : term445 = True => @lem5456477)). Qed.
Lemma lem5456480 : term445 = True.
Proof. exact (EQ_MP (@lem5456479) (@lem5456477)). Qed.
Lemma lem5456481 : term444 = True.
Proof. exact (TRANS (@lem5456476) (@lem5456480)). Qed.
Lemma lem5456482 : term669 = True.
Proof. exact (TRANS (@lem5456473) (@lem5456481)). Qed.
Lemma lem5456483 : term666 = True.
Proof. exact (TRANS (@lem5456459) (@lem5456482)). Qed.
Lemma lem5456484 : term444 = True.
Proof. exact (TRANS (@lem5456436) (@lem5456483)). Qed.
Lemma lem5456485 : term663 = True.
Proof. exact (TRANS (@lem5456427) (@lem5456484)). Qed.
Lemma lem5456486 : True = term663.
Proof. exact (SYM (@lem5456485)). Qed.
Lemma lem5456487 : term663.
Proof. exact (EQ_MP (@lem5456486) (@lem0)). Qed.
Lemma lem5456488 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term737 _70533 _70534 _70535.
Proof. exact (conj (@lem5456487) (@lem5456348 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456490 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5456491 (_70533 : int) (_70534 : int) (_70535 : int) : term738 _70533 _70534 _70535.
Proof. exact (@lem5456490 term272 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5456492 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term739 _70533 _70534 _70535.
Proof. exact (@lem5456491 _70533 _70534 _70535 (@lem5456488 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456493 (_70533 : int) (_70534 : int) (_70535 : int) : (term740 _70533 _70534 _70535) = (term396 _70533 _70534 _70535).
Proof. exact (@lem1982733 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5456494 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5456495 (_70533 : int) (_70534 : int) (_70535 : int) : (term741 _70533 _70534 _70535) = (term398 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5456494) (@lem5456493 _70533 _70534 _70535)). Qed.
Lemma lem5456496 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5456497 (_70533 : int) (_70534 : int) (_70535 : int) : (term739 _70533 _70534 _70535) = (term399 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5456495 _70533 _70534 _70535) (@lem5456496)). Qed.
Lemma lem5456498 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term399 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5456497 _70533 _70534 _70535) (@lem5456492 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456499 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term790 _70533 _70534 _70535.
Proof. exact (conj (@lem5456498 _70532 _70533 _70534 _70535 h1) (@lem5456424 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456501 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5456502 (_70533 : int) (_70534 : int) (_70535 : int) : term791 _70533 _70534 _70535.
Proof. exact (@lem5456501 (term396 _70533 _70534 _70535) (term418 _70533 _70534 _70535)). Qed.
Lemma lem5456503 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term792 _70533 _70534 _70535.
Proof. exact (@lem5456502 _70533 _70534 _70535 (@lem5456499 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456504 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = (term794 _70533 _70534 _70535).
Proof. exact (@lem1982753 (term360 _70533) (real_of_int _70533) (term395 _70534 _70535) (term404 _70534 _70535)). Qed.
Lemma lem5456505 (_70533 : int) : (term688 _70533) = (term689 _70533).
Proof. exact (@lem1982713 term335 (real_of_int _70533)). Qed.
Lemma lem5456507 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456508 : term272 = term369.
Proof. exact (@lem5456507 term120). Qed.
Lemma lem5456510 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5456511 : term335 = term336.
Proof. exact (@lem5456510 term120). Qed.
Lemma lem5456512 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456513 : term690 = term691.
Proof. exact (MK_COMB (@lem5456512) (@lem5456511)). Qed.
Lemma lem5456514 : term692 = term693.
Proof. exact (MK_COMB (@lem5456513) (@lem5456508)). Qed.
Lemma lem5456515 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5456517 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456518 : term444 = term445.
Proof. exact (@lem5456517 (NUMERAL 0) term120). Qed.
Lemma lem5456519 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456520 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456521 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456520 h1) (fun h1 : term445 = True => @lem5456519)). Qed.
Lemma lem5456522 : term445 = True.
Proof. exact (EQ_MP (@lem5456521) (@lem5456519)). Qed.
Lemma lem5456523 : term444 = True.
Proof. exact (TRANS (@lem5456518) (@lem5456522)). Qed.
Lemma lem5456524 : True = term444.
Proof. exact (SYM (@lem5456523)). Qed.
Lemma lem5456525 : term444.
Proof. exact (EQ_MP (@lem5456524) (@lem0)). Qed.
Lemma lem5456526 : term695.
Proof. exact (@lem5456515 (@lem5456525)). Qed.
Lemma lem5456528 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456529 : term444 = term445.
Proof. exact (@lem5456528 (NUMERAL 0) term120). Qed.
Lemma lem5456530 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456531 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456532 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456531 h1) (fun h1 : term445 = True => @lem5456530)). Qed.
Lemma lem5456533 : term445 = True.
Proof. exact (EQ_MP (@lem5456532) (@lem5456530)). Qed.
Lemma lem5456534 : term444 = True.
Proof. exact (TRANS (@lem5456529) (@lem5456533)). Qed.
Lemma lem5456535 : True = term444.
Proof. exact (SYM (@lem5456534)). Qed.
Lemma lem5456536 : term444.
Proof. exact (EQ_MP (@lem5456535) (@lem0)). Qed.
Lemma lem5456537 : term696.
Proof. exact (@lem5456526 (@lem5456536)). Qed.
Lemma lem5456539 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456540 : term444 = term445.
Proof. exact (@lem5456539 (NUMERAL 0) term120). Qed.
Lemma lem5456541 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456542 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456543 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456542 h1) (fun h1 : term445 = True => @lem5456541)). Qed.
Lemma lem5456544 : term445 = True.
Proof. exact (EQ_MP (@lem5456543) (@lem5456541)). Qed.
Lemma lem5456545 : term444 = True.
Proof. exact (TRANS (@lem5456540) (@lem5456544)). Qed.
Lemma lem5456546 : True = term444.
Proof. exact (SYM (@lem5456545)). Qed.
Lemma lem5456547 : term444.
Proof. exact (EQ_MP (@lem5456546) (@lem0)). Qed.
Lemma lem5456548 : term697.
Proof. exact (@lem5456537 (@lem5456547)). Qed.
Lemma lem5456550 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456551 : term344 = term345.
Proof. exact (@lem5456550 term120 term120). Qed.
Lemma lem5456552 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456553 : term347 = term120.
Proof. exact (EQ_MP (@lem5456552) (@lem940073)). Qed.
Lemma lem5456554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456555 : term345 = term272.
Proof. exact (MK_COMB (@lem5456554) (@lem5456553)). Qed.
Lemma lem5456556 : term344 = term272.
Proof. exact (TRANS (@lem5456551) (@lem5456555)). Qed.
Lemma lem5456558 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5456559 : term370 = term375.
Proof. exact (@lem5456558 term120 term120). Qed.
Lemma lem5456560 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456561 : term347 = term120.
Proof. exact (EQ_MP (@lem5456560) (@lem940073)). Qed.
Lemma lem5456562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456563 : term345 = term272.
Proof. exact (MK_COMB (@lem5456562) (@lem5456561)). Qed.
Lemma lem5456564 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5456565 : term375 = term335.
Proof. exact (MK_COMB (@lem5456564) (@lem5456563)). Qed.
Lemma lem5456566 : term370 = term335.
Proof. exact (TRANS (@lem5456559) (@lem5456565)). Qed.
Lemma lem5456567 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456568 : term698 = term690.
Proof. exact (MK_COMB (@lem5456567) (@lem5456566)). Qed.
Lemma lem5456569 : term699 = term692.
Proof. exact (MK_COMB (@lem5456568) (@lem5456556)). Qed.
Lemma lem5456571 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5456572 : term692 = term260.
Proof. exact (@lem5456571 term120). Qed.
Lemma lem5456573 : term699 = term260.
Proof. exact (TRANS (@lem5456569) (@lem5456572)). Qed.
Lemma lem5456574 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456575 : term701 = term454.
Proof. exact (MK_COMB (@lem5456574) (@lem5456573)). Qed.
Lemma lem5456576 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5456577 : term702 = term456.
Proof. exact (MK_COMB (@lem5456575) (@lem5456576)). Qed.
Lemma lem5456579 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456580 : term456 = term260.
Proof. exact (@lem5456579 term120). Qed.
Lemma lem5456581 : term702 = term260.
Proof. exact (TRANS (@lem5456577) (@lem5456580)). Qed.
Lemma lem5456583 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456584 : term344 = term345.
Proof. exact (@lem5456583 term120 term120). Qed.
Lemma lem5456585 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456586 : term347 = term120.
Proof. exact (EQ_MP (@lem5456585) (@lem940073)). Qed.
Lemma lem5456587 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456588 : term345 = term272.
Proof. exact (MK_COMB (@lem5456587) (@lem5456586)). Qed.
Lemma lem5456589 : term344 = term272.
Proof. exact (TRANS (@lem5456584) (@lem5456588)). Qed.
Lemma lem5456590 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5456591 : term458 = term456.
Proof. exact (MK_COMB (@lem5456590) (@lem5456589)). Qed.
Lemma lem5456593 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456594 : term456 = term260.
Proof. exact (@lem5456593 term120). Qed.
Lemma lem5456595 : term458 = term260.
Proof. exact (TRANS (@lem5456591) (@lem5456594)). Qed.
Lemma lem5456596 : term260 = term458.
Proof. exact (SYM (@lem5456595)). Qed.
Lemma lem5456597 : term702 = term458.
Proof. exact (TRANS (@lem5456581) (@lem5456596)). Qed.
Lemma lem5456598 : term693 = term332.
Proof. exact (@lem5456548 (@lem5456597)). Qed.
Lemma lem5456599 : term692 = term332.
Proof. exact (TRANS (@lem5456514) (@lem5456598)). Qed.
Lemma lem5456601 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5456602 : term332 = term260.
Proof. exact (@lem5456601 term260). Qed.
Lemma lem5456603 : term692 = term260.
Proof. exact (TRANS (@lem5456599) (@lem5456602)). Qed.
Lemma lem5456604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456605 : term703 = term454.
Proof. exact (MK_COMB (@lem5456604) (@lem5456603)). Qed.
Lemma lem5456606 (_70533 : int) : (real_of_int _70533) = (real_of_int _70533).
Proof. exact (eq_refl (real_of_int _70533)). Qed.
Lemma lem5456607 (_70533 : int) : (term689 _70533) = (term704 _70533).
Proof. exact (MK_COMB (@lem5456605) (@lem5456606 _70533)). Qed.
Lemma lem5456608 (_70533 : int) : (term688 _70533) = (term704 _70533).
Proof. exact (TRANS (@lem5456505 _70533) (@lem5456607 _70533)). Qed.
Lemma lem5456609 (_70533 : int) : (term704 _70533) = term260.
Proof. exact (@lem1982719 (real_of_int _70533)). Qed.
Lemma lem5456610 (_70533 : int) : (term688 _70533) = term260.
Proof. exact (TRANS (@lem5456608 _70533) (@lem5456609 _70533)). Qed.
Lemma lem5456611 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456612 (_70533 : int) : (term705 _70533) = term706.
Proof. exact (MK_COMB (@lem5456611) (@lem5456610 _70533)). Qed.
Lemma lem5456613 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = (term760 _70534 _70535).
Proof. exact (@lem1982753 (term360 _70534) (real_of_int _70534) (term749 _70535) (term360 _70535)). Qed.
Lemma lem5456614 (_70534 : int) : (term688 _70534) = (term689 _70534).
Proof. exact (@lem1982713 term335 (real_of_int _70534)). Qed.
Lemma lem5456616 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456617 : term272 = term369.
Proof. exact (@lem5456616 term120). Qed.
Lemma lem5456619 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5456620 : term335 = term336.
Proof. exact (@lem5456619 term120). Qed.
Lemma lem5456621 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456622 : term690 = term691.
Proof. exact (MK_COMB (@lem5456621) (@lem5456620)). Qed.
Lemma lem5456623 : term692 = term693.
Proof. exact (MK_COMB (@lem5456622) (@lem5456617)). Qed.
Lemma lem5456624 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5456626 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456627 : term444 = term445.
Proof. exact (@lem5456626 (NUMERAL 0) term120). Qed.
Lemma lem5456628 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456629 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456630 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456629 h1) (fun h1 : term445 = True => @lem5456628)). Qed.
Lemma lem5456631 : term445 = True.
Proof. exact (EQ_MP (@lem5456630) (@lem5456628)). Qed.
Lemma lem5456632 : term444 = True.
Proof. exact (TRANS (@lem5456627) (@lem5456631)). Qed.
Lemma lem5456633 : True = term444.
Proof. exact (SYM (@lem5456632)). Qed.
Lemma lem5456634 : term444.
Proof. exact (EQ_MP (@lem5456633) (@lem0)). Qed.
Lemma lem5456635 : term695.
Proof. exact (@lem5456624 (@lem5456634)). Qed.
Lemma lem5456637 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456638 : term444 = term445.
Proof. exact (@lem5456637 (NUMERAL 0) term120). Qed.
Lemma lem5456639 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456640 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456641 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456640 h1) (fun h1 : term445 = True => @lem5456639)). Qed.
Lemma lem5456642 : term445 = True.
Proof. exact (EQ_MP (@lem5456641) (@lem5456639)). Qed.
Lemma lem5456643 : term444 = True.
Proof. exact (TRANS (@lem5456638) (@lem5456642)). Qed.
Lemma lem5456644 : True = term444.
Proof. exact (SYM (@lem5456643)). Qed.
Lemma lem5456645 : term444.
Proof. exact (EQ_MP (@lem5456644) (@lem0)). Qed.
Lemma lem5456646 : term696.
Proof. exact (@lem5456635 (@lem5456645)). Qed.
Lemma lem5456648 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456649 : term444 = term445.
Proof. exact (@lem5456648 (NUMERAL 0) term120). Qed.
Lemma lem5456650 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456651 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456652 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456651 h1) (fun h1 : term445 = True => @lem5456650)). Qed.
Lemma lem5456653 : term445 = True.
Proof. exact (EQ_MP (@lem5456652) (@lem5456650)). Qed.
Lemma lem5456654 : term444 = True.
Proof. exact (TRANS (@lem5456649) (@lem5456653)). Qed.
Lemma lem5456655 : True = term444.
Proof. exact (SYM (@lem5456654)). Qed.
Lemma lem5456656 : term444.
Proof. exact (EQ_MP (@lem5456655) (@lem0)). Qed.
Lemma lem5456657 : term697.
Proof. exact (@lem5456646 (@lem5456656)). Qed.
Lemma lem5456659 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456660 : term344 = term345.
Proof. exact (@lem5456659 term120 term120). Qed.
Lemma lem5456661 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456662 : term347 = term120.
Proof. exact (EQ_MP (@lem5456661) (@lem940073)). Qed.
Lemma lem5456663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456664 : term345 = term272.
Proof. exact (MK_COMB (@lem5456663) (@lem5456662)). Qed.
Lemma lem5456665 : term344 = term272.
Proof. exact (TRANS (@lem5456660) (@lem5456664)). Qed.
Lemma lem5456667 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5456668 : term370 = term375.
Proof. exact (@lem5456667 term120 term120). Qed.
Lemma lem5456669 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456670 : term347 = term120.
Proof. exact (EQ_MP (@lem5456669) (@lem940073)). Qed.
Lemma lem5456671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456672 : term345 = term272.
Proof. exact (MK_COMB (@lem5456671) (@lem5456670)). Qed.
Lemma lem5456673 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5456674 : term375 = term335.
Proof. exact (MK_COMB (@lem5456673) (@lem5456672)). Qed.
Lemma lem5456675 : term370 = term335.
Proof. exact (TRANS (@lem5456668) (@lem5456674)). Qed.
Lemma lem5456676 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456677 : term698 = term690.
Proof. exact (MK_COMB (@lem5456676) (@lem5456675)). Qed.
Lemma lem5456678 : term699 = term692.
Proof. exact (MK_COMB (@lem5456677) (@lem5456665)). Qed.
Lemma lem5456680 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5456681 : term692 = term260.
Proof. exact (@lem5456680 term120). Qed.
Lemma lem5456682 : term699 = term260.
Proof. exact (TRANS (@lem5456678) (@lem5456681)). Qed.
Lemma lem5456683 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456684 : term701 = term454.
Proof. exact (MK_COMB (@lem5456683) (@lem5456682)). Qed.
Lemma lem5456685 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5456686 : term702 = term456.
Proof. exact (MK_COMB (@lem5456684) (@lem5456685)). Qed.
Lemma lem5456688 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456689 : term456 = term260.
Proof. exact (@lem5456688 term120). Qed.
Lemma lem5456690 : term702 = term260.
Proof. exact (TRANS (@lem5456686) (@lem5456689)). Qed.
Lemma lem5456692 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456693 : term344 = term345.
Proof. exact (@lem5456692 term120 term120). Qed.
Lemma lem5456694 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456695 : term347 = term120.
Proof. exact (EQ_MP (@lem5456694) (@lem940073)). Qed.
Lemma lem5456696 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456697 : term345 = term272.
Proof. exact (MK_COMB (@lem5456696) (@lem5456695)). Qed.
Lemma lem5456698 : term344 = term272.
Proof. exact (TRANS (@lem5456693) (@lem5456697)). Qed.
Lemma lem5456699 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5456700 : term458 = term456.
Proof. exact (MK_COMB (@lem5456699) (@lem5456698)). Qed.
Lemma lem5456702 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456703 : term456 = term260.
Proof. exact (@lem5456702 term120). Qed.
Lemma lem5456704 : term458 = term260.
Proof. exact (TRANS (@lem5456700) (@lem5456703)). Qed.
Lemma lem5456705 : term260 = term458.
Proof. exact (SYM (@lem5456704)). Qed.
Lemma lem5456706 : term702 = term458.
Proof. exact (TRANS (@lem5456690) (@lem5456705)). Qed.
Lemma lem5456707 : term693 = term332.
Proof. exact (@lem5456657 (@lem5456706)). Qed.
Lemma lem5456708 : term692 = term332.
Proof. exact (TRANS (@lem5456623) (@lem5456707)). Qed.
Lemma lem5456710 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5456711 : term332 = term260.
Proof. exact (@lem5456710 term260). Qed.
Lemma lem5456712 : term692 = term260.
Proof. exact (TRANS (@lem5456708) (@lem5456711)). Qed.
Lemma lem5456713 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456714 : term703 = term454.
Proof. exact (MK_COMB (@lem5456713) (@lem5456712)). Qed.
Lemma lem5456715 (_70534 : int) : (real_of_int _70534) = (real_of_int _70534).
Proof. exact (eq_refl (real_of_int _70534)). Qed.
Lemma lem5456716 (_70534 : int) : (term689 _70534) = (term704 _70534).
Proof. exact (MK_COMB (@lem5456714) (@lem5456715 _70534)). Qed.
Lemma lem5456717 (_70534 : int) : (term688 _70534) = (term704 _70534).
Proof. exact (TRANS (@lem5456614 _70534) (@lem5456716 _70534)). Qed.
Lemma lem5456718 (_70534 : int) : (term704 _70534) = term260.
Proof. exact (@lem1982719 (real_of_int _70534)). Qed.
Lemma lem5456719 (_70534 : int) : (term688 _70534) = term260.
Proof. exact (TRANS (@lem5456717 _70534) (@lem5456718 _70534)). Qed.
Lemma lem5456720 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456721 (_70534 : int) : (term705 _70534) = term706.
Proof. exact (MK_COMB (@lem5456720) (@lem5456719 _70534)). Qed.
Lemma lem5456722 (_70535 : int) : (term761 _70535) = (term708 _70535).
Proof. exact (@lem1982759 (real_of_int _70535) (term360 _70535) term335). Qed.
Lemma lem5456723 (_70535 : int) : (term709 _70535) = (term689 _70535).
Proof. exact (@lem1982715 term335 (real_of_int _70535)). Qed.
Lemma lem5456725 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456726 : term272 = term369.
Proof. exact (@lem5456725 term120). Qed.
Lemma lem5456728 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5456729 : term335 = term336.
Proof. exact (@lem5456728 term120). Qed.
Lemma lem5456730 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456731 : term690 = term691.
Proof. exact (MK_COMB (@lem5456730) (@lem5456729)). Qed.
Lemma lem5456732 : term692 = term693.
Proof. exact (MK_COMB (@lem5456731) (@lem5456726)). Qed.
Lemma lem5456733 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5456735 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456736 : term444 = term445.
Proof. exact (@lem5456735 (NUMERAL 0) term120). Qed.
Lemma lem5456737 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456738 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456739 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456738 h1) (fun h1 : term445 = True => @lem5456737)). Qed.
Lemma lem5456740 : term445 = True.
Proof. exact (EQ_MP (@lem5456739) (@lem5456737)). Qed.
Lemma lem5456741 : term444 = True.
Proof. exact (TRANS (@lem5456736) (@lem5456740)). Qed.
Lemma lem5456742 : True = term444.
Proof. exact (SYM (@lem5456741)). Qed.
Lemma lem5456743 : term444.
Proof. exact (EQ_MP (@lem5456742) (@lem0)). Qed.
Lemma lem5456744 : term695.
Proof. exact (@lem5456733 (@lem5456743)). Qed.
Lemma lem5456746 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456747 : term444 = term445.
Proof. exact (@lem5456746 (NUMERAL 0) term120). Qed.
Lemma lem5456748 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456749 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456750 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456749 h1) (fun h1 : term445 = True => @lem5456748)). Qed.
Lemma lem5456751 : term445 = True.
Proof. exact (EQ_MP (@lem5456750) (@lem5456748)). Qed.
Lemma lem5456752 : term444 = True.
Proof. exact (TRANS (@lem5456747) (@lem5456751)). Qed.
Lemma lem5456753 : True = term444.
Proof. exact (SYM (@lem5456752)). Qed.
Lemma lem5456754 : term444.
Proof. exact (EQ_MP (@lem5456753) (@lem0)). Qed.
Lemma lem5456755 : term696.
Proof. exact (@lem5456744 (@lem5456754)). Qed.
Lemma lem5456757 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456758 : term444 = term445.
Proof. exact (@lem5456757 (NUMERAL 0) term120). Qed.
Lemma lem5456759 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456760 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456761 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456760 h1) (fun h1 : term445 = True => @lem5456759)). Qed.
Lemma lem5456762 : term445 = True.
Proof. exact (EQ_MP (@lem5456761) (@lem5456759)). Qed.
Lemma lem5456763 : term444 = True.
Proof. exact (TRANS (@lem5456758) (@lem5456762)). Qed.
Lemma lem5456764 : True = term444.
Proof. exact (SYM (@lem5456763)). Qed.
Lemma lem5456765 : term444.
Proof. exact (EQ_MP (@lem5456764) (@lem0)). Qed.
Lemma lem5456766 : term697.
Proof. exact (@lem5456755 (@lem5456765)). Qed.
Lemma lem5456768 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456769 : term344 = term345.
Proof. exact (@lem5456768 term120 term120). Qed.
Lemma lem5456770 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456771 : term347 = term120.
Proof. exact (EQ_MP (@lem5456770) (@lem940073)). Qed.
Lemma lem5456772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456773 : term345 = term272.
Proof. exact (MK_COMB (@lem5456772) (@lem5456771)). Qed.
Lemma lem5456774 : term344 = term272.
Proof. exact (TRANS (@lem5456769) (@lem5456773)). Qed.
Lemma lem5456776 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5456777 : term370 = term375.
Proof. exact (@lem5456776 term120 term120). Qed.
Lemma lem5456778 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456779 : term347 = term120.
Proof. exact (EQ_MP (@lem5456778) (@lem940073)). Qed.
Lemma lem5456780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456781 : term345 = term272.
Proof. exact (MK_COMB (@lem5456780) (@lem5456779)). Qed.
Lemma lem5456782 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5456783 : term375 = term335.
Proof. exact (MK_COMB (@lem5456782) (@lem5456781)). Qed.
Lemma lem5456784 : term370 = term335.
Proof. exact (TRANS (@lem5456777) (@lem5456783)). Qed.
Lemma lem5456785 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456786 : term698 = term690.
Proof. exact (MK_COMB (@lem5456785) (@lem5456784)). Qed.
Lemma lem5456787 : term699 = term692.
Proof. exact (MK_COMB (@lem5456786) (@lem5456774)). Qed.
Lemma lem5456789 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5456790 : term692 = term260.
Proof. exact (@lem5456789 term120). Qed.
Lemma lem5456791 : term699 = term260.
Proof. exact (TRANS (@lem5456787) (@lem5456790)). Qed.
Lemma lem5456792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456793 : term701 = term454.
Proof. exact (MK_COMB (@lem5456792) (@lem5456791)). Qed.
Lemma lem5456794 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5456795 : term702 = term456.
Proof. exact (MK_COMB (@lem5456793) (@lem5456794)). Qed.
Lemma lem5456797 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456798 : term456 = term260.
Proof. exact (@lem5456797 term120). Qed.
Lemma lem5456799 : term702 = term260.
Proof. exact (TRANS (@lem5456795) (@lem5456798)). Qed.
Lemma lem5456801 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456802 : term344 = term345.
Proof. exact (@lem5456801 term120 term120). Qed.
Lemma lem5456803 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456804 : term347 = term120.
Proof. exact (EQ_MP (@lem5456803) (@lem940073)). Qed.
Lemma lem5456805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456806 : term345 = term272.
Proof. exact (MK_COMB (@lem5456805) (@lem5456804)). Qed.
Lemma lem5456807 : term344 = term272.
Proof. exact (TRANS (@lem5456802) (@lem5456806)). Qed.
Lemma lem5456808 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5456809 : term458 = term456.
Proof. exact (MK_COMB (@lem5456808) (@lem5456807)). Qed.
Lemma lem5456811 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456812 : term456 = term260.
Proof. exact (@lem5456811 term120). Qed.
Lemma lem5456813 : term458 = term260.
Proof. exact (TRANS (@lem5456809) (@lem5456812)). Qed.
Lemma lem5456814 : term260 = term458.
Proof. exact (SYM (@lem5456813)). Qed.
Lemma lem5456815 : term702 = term458.
Proof. exact (TRANS (@lem5456799) (@lem5456814)). Qed.
Lemma lem5456816 : term693 = term332.
Proof. exact (@lem5456766 (@lem5456815)). Qed.
Lemma lem5456817 : term692 = term332.
Proof. exact (TRANS (@lem5456732) (@lem5456816)). Qed.
Lemma lem5456819 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5456820 : term332 = term260.
Proof. exact (@lem5456819 term260). Qed.
Lemma lem5456821 : term692 = term260.
Proof. exact (TRANS (@lem5456817) (@lem5456820)). Qed.
Lemma lem5456822 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5456823 : term703 = term454.
Proof. exact (MK_COMB (@lem5456822) (@lem5456821)). Qed.
Lemma lem5456824 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5456825 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5456823) (@lem5456824 _70535)). Qed.
Lemma lem5456826 (_70535 : int) : (term709 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5456723 _70535) (@lem5456825 _70535)). Qed.
Lemma lem5456827 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5456828 (_70535 : int) : (term709 _70535) = term260.
Proof. exact (TRANS (@lem5456826 _70535) (@lem5456827 _70535)). Qed.
Lemma lem5456829 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5456830 (_70535 : int) : (term710 _70535) = term706.
Proof. exact (MK_COMB (@lem5456829) (@lem5456828 _70535)). Qed.
Lemma lem5456831 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5456832 (_70535 : int) : (term708 _70535) = term711.
Proof. exact (MK_COMB (@lem5456830 _70535) (@lem5456831)). Qed.
Lemma lem5456833 (_70535 : int) : (term761 _70535) = term711.
Proof. exact (TRANS (@lem5456722 _70535) (@lem5456832 _70535)). Qed.
Lemma lem5456834 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5456835 (_70535 : int) : (term761 _70535) = term335.
Proof. exact (TRANS (@lem5456833 _70535) (@lem5456834)). Qed.
Lemma lem5456836 (_70534 : int) (_70535 : int) : (term760 _70534 _70535) = term711.
Proof. exact (MK_COMB (@lem5456721 _70534) (@lem5456835 _70535)). Qed.
Lemma lem5456837 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = term711.
Proof. exact (TRANS (@lem5456613 _70534 _70535) (@lem5456836 _70534 _70535)). Qed.
Lemma lem5456838 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5456839 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = term335.
Proof. exact (TRANS (@lem5456837 _70534 _70535) (@lem5456838)). Qed.
Lemma lem5456840 (_70533 : int) (_70534 : int) (_70535 : int) : (term794 _70533 _70534 _70535) = term711.
Proof. exact (MK_COMB (@lem5456612 _70533) (@lem5456839 _70534 _70535)). Qed.
Lemma lem5456841 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = term711.
Proof. exact (TRANS (@lem5456504 _70533 _70534 _70535) (@lem5456840 _70533 _70534 _70535)). Qed.
Lemma lem5456842 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5456843 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = term335.
Proof. exact (TRANS (@lem5456841 _70533 _70534 _70535) (@lem5456842)). Qed.
Lemma lem5456844 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5456845 (_70533 : int) (_70534 : int) (_70535 : int) : (term795 _70533 _70534 _70535) = term713.
Proof. exact (MK_COMB (@lem5456844) (@lem5456843 _70533 _70534 _70535)). Qed.
Lemma lem5456846 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5456847 (_70533 : int) (_70534 : int) (_70535 : int) : (term792 _70533 _70534 _70535) = term714.
Proof. exact (MK_COMB (@lem5456845 _70533 _70534 _70535) (@lem5456846)). Qed.
Lemma lem5456848 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : term714.
Proof. exact (EQ_MP (@lem5456847 _70533 _70534 _70535) (@lem5456503 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456850 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5456851 : term714 = term715.
Proof. exact (@lem5456850 term260 term335). Qed.
Lemma lem5456853 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5456854 : term335 = term336.
Proof. exact (@lem5456853 term120). Qed.
Lemma lem5456856 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456857 : term260 = term332.
Proof. exact (@lem5456856 (NUMERAL 0)). Qed.
Lemma lem5456858 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5456859 : term262 = term716.
Proof. exact (MK_COMB (@lem5456858) (@lem5456857)). Qed.
Lemma lem5456860 : term715 = term717.
Proof. exact (MK_COMB (@lem5456859) (@lem5456854)). Qed.
Lemma lem5456861 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5456863 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456864 : term444 = term445.
Proof. exact (@lem5456863 (NUMERAL 0) term120). Qed.
Lemma lem5456865 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456866 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456867 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456866 h1) (fun h1 : term445 = True => @lem5456865)). Qed.
Lemma lem5456868 : term445 = True.
Proof. exact (EQ_MP (@lem5456867) (@lem5456865)). Qed.
Lemma lem5456869 : term444 = True.
Proof. exact (TRANS (@lem5456864) (@lem5456868)). Qed.
Lemma lem5456870 : True = term444.
Proof. exact (SYM (@lem5456869)). Qed.
Lemma lem5456871 : term444.
Proof. exact (EQ_MP (@lem5456870) (@lem0)). Qed.
Lemma lem5456872 : term719.
Proof. exact (@lem5456861 (@lem5456871)). Qed.
Lemma lem5456874 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456875 : term444 = term445.
Proof. exact (@lem5456874 (NUMERAL 0) term120). Qed.
Lemma lem5456876 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456877 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456878 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456877 h1) (fun h1 : term445 = True => @lem5456876)). Qed.
Lemma lem5456879 : term445 = True.
Proof. exact (EQ_MP (@lem5456878) (@lem5456876)). Qed.
Lemma lem5456880 : term444 = True.
Proof. exact (TRANS (@lem5456875) (@lem5456879)). Qed.
Lemma lem5456881 : True = term444.
Proof. exact (SYM (@lem5456880)). Qed.
Lemma lem5456882 : term444.
Proof. exact (EQ_MP (@lem5456881) (@lem0)). Qed.
Lemma lem5456883 : term717 = term720.
Proof. exact (@lem5456872 (@lem5456882)). Qed.
Lemma lem5456885 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5456886 : term370 = term375.
Proof. exact (@lem5456885 term120 term120). Qed.
Lemma lem5456887 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456888 : term347 = term120.
Proof. exact (EQ_MP (@lem5456887) (@lem940073)). Qed.
Lemma lem5456889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456890 : term345 = term272.
Proof. exact (MK_COMB (@lem5456889) (@lem5456888)). Qed.
Lemma lem5456891 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5456892 : term375 = term335.
Proof. exact (MK_COMB (@lem5456891) (@lem5456890)). Qed.
Lemma lem5456893 : term370 = term335.
Proof. exact (TRANS (@lem5456886) (@lem5456892)). Qed.
Lemma lem5456895 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456896 : term456 = term260.
Proof. exact (@lem5456895 term120). Qed.
Lemma lem5456897 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5456898 : term721 = term262.
Proof. exact (MK_COMB (@lem5456897) (@lem5456896)). Qed.
Lemma lem5456899 : term720 = term715.
Proof. exact (MK_COMB (@lem5456898) (@lem5456893)). Qed.
Lemma lem5456901 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5456902 : term715 = term724.
Proof. exact (@lem5456901 (NUMERAL 0) term120). Qed.
Lemma lem5456903 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456904 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5456905 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456904 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5456903)). Qed.
Lemma lem5456906 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5456905) (@lem5456903)). Qed.
Lemma lem5456907 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5456908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5456909 : term725 = (and True).
Proof. exact (MK_COMB (@lem5456908) (@lem5456907)). Qed.
Lemma lem5456910 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5456909) (@lem5456906)). Qed.
Lemma lem5456912 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5456913 : term724 = False.
Proof. exact (TRANS (@lem5456910) (@lem5456912)). Qed.
Lemma lem5456914 : term715 = False.
Proof. exact (TRANS (@lem5456902) (@lem5456913)). Qed.
Lemma lem5456915 : term720 = False.
Proof. exact (TRANS (@lem5456899) (@lem5456914)). Qed.
Lemma lem5456916 : term717 = False.
Proof. exact (TRANS (@lem5456883) (@lem5456915)). Qed.
Lemma lem5456917 : term715 = False.
Proof. exact (TRANS (@lem5456860) (@lem5456916)). Qed.
Lemma lem5456918 : term714 = False.
Proof. exact (TRANS (@lem5456851) (@lem5456917)). Qed.
Lemma lem5456919 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term784 _70532 _70533 _70534 _70535) : False.
Proof. exact (EQ_MP (@lem5456918) (@lem5456848 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5456920 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term649 _70532 _70533 _70534 _70535) : False.
Proof. exact (or_elim (@lem5455485 _70532 _70533 _70534 _70535 h1) (fun h0 : term763 _70532 _70533 _70534 _70535 => @lem5456335 _70532 _70533 _70534 _70535 h0) (fun h0 : term784 _70532 _70533 _70534 _70535 => @lem5456919 _70532 _70533 _70534 _70535 h0)). Qed.
Lemma lem5456921 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term658 _70532 _70533 _70534 _70535) : False.
Proof. exact (or_elim (@lem5454264 _70532 _70533 _70534 _70535 h1) (fun h0 : term653 _70534 _70532 _70533 _70535 => @lem5455484 _70534 _70532 _70533 _70535 h0) (fun h0 : term649 _70532 _70533 _70534 _70535 => @lem5456920 _70532 _70533 _70534 _70535 h0)). Qed.
Lemma lem5456922 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term645 _70532 _70533 _70534 _70535) : term645 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5456923 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term640 _70532 _70534 _70533 _70535) : term640 _70532 _70534 _70533 _70535.
Proof. exact (h1). Qed.
Lemma lem5456924 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term796 _70534 _70532 _70533 _70535.
Proof. exact (h1). Qed.
Lemma lem5456925 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term641 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5456924 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456927 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term610 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5456925 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456929 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term579 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5456927 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456931 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term548 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5456929 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456933 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term517 _70534 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5456931 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456935 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term492 _70532 _70533 _70535.
Proof. exact (proj2 (@lem5456933 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456936 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term428 _70532 _70533 _70534 _70535.
Proof. exact (proj1 (@lem5456933 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456938 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term408 _70532 _70535.
Proof. exact (proj1 (@lem5456936 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456940 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term383 _70532 _70535.
Proof. exact (proj1 (@lem5456935 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5456942 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5456943 : term663 = term444.
Proof. exact (@lem5456942 term260 term272). Qed.
Lemma lem5456945 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456946 : term272 = term369.
Proof. exact (@lem5456945 term120). Qed.
Lemma lem5456948 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5456949 : term260 = term332.
Proof. exact (@lem5456948 (NUMERAL 0)). Qed.
Lemma lem5456950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5456951 : term664 = term665.
Proof. exact (MK_COMB (@lem5456950) (@lem5456949)). Qed.
Lemma lem5456952 : term444 = term666.
Proof. exact (MK_COMB (@lem5456951) (@lem5456946)). Qed.
Lemma lem5456953 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5456955 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456956 : term444 = term445.
Proof. exact (@lem5456955 (NUMERAL 0) term120). Qed.
Lemma lem5456957 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456958 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456959 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456958 h1) (fun h1 : term445 = True => @lem5456957)). Qed.
Lemma lem5456960 : term445 = True.
Proof. exact (EQ_MP (@lem5456959) (@lem5456957)). Qed.
Lemma lem5456961 : term444 = True.
Proof. exact (TRANS (@lem5456956) (@lem5456960)). Qed.
Lemma lem5456962 : True = term444.
Proof. exact (SYM (@lem5456961)). Qed.
Lemma lem5456963 : term444.
Proof. exact (EQ_MP (@lem5456962) (@lem0)). Qed.
Lemma lem5456964 : term668.
Proof. exact (@lem5456953 (@lem5456963)). Qed.
Lemma lem5456966 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456967 : term444 = term445.
Proof. exact (@lem5456966 (NUMERAL 0) term120). Qed.
Lemma lem5456968 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456969 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456970 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456969 h1) (fun h1 : term445 = True => @lem5456968)). Qed.
Lemma lem5456971 : term445 = True.
Proof. exact (EQ_MP (@lem5456970) (@lem5456968)). Qed.
Lemma lem5456972 : term444 = True.
Proof. exact (TRANS (@lem5456967) (@lem5456971)). Qed.
Lemma lem5456973 : True = term444.
Proof. exact (SYM (@lem5456972)). Qed.
Lemma lem5456974 : term444.
Proof. exact (EQ_MP (@lem5456973) (@lem0)). Qed.
Lemma lem5456975 : term666 = term669.
Proof. exact (@lem5456964 (@lem5456974)). Qed.
Lemma lem5456977 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5456978 : term344 = term345.
Proof. exact (@lem5456977 term120 term120). Qed.
Lemma lem5456979 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5456980 : term347 = term120.
Proof. exact (EQ_MP (@lem5456979) (@lem940073)). Qed.
Lemma lem5456981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5456982 : term345 = term272.
Proof. exact (MK_COMB (@lem5456981) (@lem5456980)). Qed.
Lemma lem5456983 : term344 = term272.
Proof. exact (TRANS (@lem5456978) (@lem5456982)). Qed.
Lemma lem5456985 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5456986 : term456 = term260.
Proof. exact (@lem5456985 term120). Qed.
Lemma lem5456987 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5456988 : term670 = term664.
Proof. exact (MK_COMB (@lem5456987) (@lem5456986)). Qed.
Lemma lem5456989 : term669 = term444.
Proof. exact (MK_COMB (@lem5456988) (@lem5456983)). Qed.
Lemma lem5456991 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5456992 : term444 = term445.
Proof. exact (@lem5456991 (NUMERAL 0) term120). Qed.
Lemma lem5456993 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5456994 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5456995 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5456994 h1) (fun h1 : term445 = True => @lem5456993)). Qed.
Lemma lem5456996 : term445 = True.
Proof. exact (EQ_MP (@lem5456995) (@lem5456993)). Qed.
Lemma lem5456997 : term444 = True.
Proof. exact (TRANS (@lem5456992) (@lem5456996)). Qed.
Lemma lem5456998 : term669 = True.
Proof. exact (TRANS (@lem5456989) (@lem5456997)). Qed.
Lemma lem5456999 : term666 = True.
Proof. exact (TRANS (@lem5456975) (@lem5456998)). Qed.
Lemma lem5457000 : term444 = True.
Proof. exact (TRANS (@lem5456952) (@lem5456999)). Qed.
Lemma lem5457001 : term663 = True.
Proof. exact (TRANS (@lem5456943) (@lem5457000)). Qed.
Lemma lem5457002 : True = term663.
Proof. exact (SYM (@lem5457001)). Qed.
Lemma lem5457003 : term663.
Proof. exact (EQ_MP (@lem5457002) (@lem0)). Qed.
Lemma lem5457004 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term671 _70532 _70535.
Proof. exact (conj (@lem5457003) (@lem5456940 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457006 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5457007 (_70532 : int) (_70535 : int) : term673 _70532 _70535.
Proof. exact (@lem5457006 term272 (term380 _70532 _70535)). Qed.
Lemma lem5457008 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term674 _70532 _70535.
Proof. exact (@lem5457007 _70532 _70535 (@lem5457004 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457009 (_70532 : int) (_70535 : int) : (term675 _70532 _70535) = (term380 _70532 _70535).
Proof. exact (@lem1982733 (term380 _70532 _70535)). Qed.
Lemma lem5457010 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5457011 (_70532 : int) (_70535 : int) : (term676 _70532 _70535) = (term382 _70532 _70535).
Proof. exact (MK_COMB (@lem5457010) (@lem5457009 _70532 _70535)). Qed.
Lemma lem5457012 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5457013 (_70532 : int) (_70535 : int) : (term674 _70532 _70535) = (term383 _70532 _70535).
Proof. exact (MK_COMB (@lem5457011 _70532 _70535) (@lem5457012)). Qed.
Lemma lem5457014 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term383 _70532 _70535.
Proof. exact (EQ_MP (@lem5457013 _70532 _70535) (@lem5457008 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457016 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5457017 : term663 = term444.
Proof. exact (@lem5457016 term260 term272). Qed.
Lemma lem5457019 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457020 : term272 = term369.
Proof. exact (@lem5457019 term120). Qed.
Lemma lem5457022 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457023 : term260 = term332.
Proof. exact (@lem5457022 (NUMERAL 0)). Qed.
Lemma lem5457024 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457025 : term664 = term665.
Proof. exact (MK_COMB (@lem5457024) (@lem5457023)). Qed.
Lemma lem5457026 : term444 = term666.
Proof. exact (MK_COMB (@lem5457025) (@lem5457020)). Qed.
Lemma lem5457027 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5457029 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457030 : term444 = term445.
Proof. exact (@lem5457029 (NUMERAL 0) term120). Qed.
Lemma lem5457031 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457032 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457033 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457032 h1) (fun h1 : term445 = True => @lem5457031)). Qed.
Lemma lem5457034 : term445 = True.
Proof. exact (EQ_MP (@lem5457033) (@lem5457031)). Qed.
Lemma lem5457035 : term444 = True.
Proof. exact (TRANS (@lem5457030) (@lem5457034)). Qed.
Lemma lem5457036 : True = term444.
Proof. exact (SYM (@lem5457035)). Qed.
Lemma lem5457037 : term444.
Proof. exact (EQ_MP (@lem5457036) (@lem0)). Qed.
Lemma lem5457038 : term668.
Proof. exact (@lem5457027 (@lem5457037)). Qed.
Lemma lem5457040 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457041 : term444 = term445.
Proof. exact (@lem5457040 (NUMERAL 0) term120). Qed.
Lemma lem5457042 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457043 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457044 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457043 h1) (fun h1 : term445 = True => @lem5457042)). Qed.
Lemma lem5457045 : term445 = True.
Proof. exact (EQ_MP (@lem5457044) (@lem5457042)). Qed.
Lemma lem5457046 : term444 = True.
Proof. exact (TRANS (@lem5457041) (@lem5457045)). Qed.
Lemma lem5457047 : True = term444.
Proof. exact (SYM (@lem5457046)). Qed.
Lemma lem5457048 : term444.
Proof. exact (EQ_MP (@lem5457047) (@lem0)). Qed.
Lemma lem5457049 : term666 = term669.
Proof. exact (@lem5457038 (@lem5457048)). Qed.
Lemma lem5457051 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457052 : term344 = term345.
Proof. exact (@lem5457051 term120 term120). Qed.
Lemma lem5457053 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457054 : term347 = term120.
Proof. exact (EQ_MP (@lem5457053) (@lem940073)). Qed.
Lemma lem5457055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457056 : term345 = term272.
Proof. exact (MK_COMB (@lem5457055) (@lem5457054)). Qed.
Lemma lem5457057 : term344 = term272.
Proof. exact (TRANS (@lem5457052) (@lem5457056)). Qed.
Lemma lem5457059 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457060 : term456 = term260.
Proof. exact (@lem5457059 term120). Qed.
Lemma lem5457061 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457062 : term670 = term664.
Proof. exact (MK_COMB (@lem5457061) (@lem5457060)). Qed.
Lemma lem5457063 : term669 = term444.
Proof. exact (MK_COMB (@lem5457062) (@lem5457057)). Qed.
Lemma lem5457065 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457066 : term444 = term445.
Proof. exact (@lem5457065 (NUMERAL 0) term120). Qed.
Lemma lem5457067 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457068 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457069 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457068 h1) (fun h1 : term445 = True => @lem5457067)). Qed.
Lemma lem5457070 : term445 = True.
Proof. exact (EQ_MP (@lem5457069) (@lem5457067)). Qed.
Lemma lem5457071 : term444 = True.
Proof. exact (TRANS (@lem5457066) (@lem5457070)). Qed.
Lemma lem5457072 : term669 = True.
Proof. exact (TRANS (@lem5457063) (@lem5457071)). Qed.
Lemma lem5457073 : term666 = True.
Proof. exact (TRANS (@lem5457049) (@lem5457072)). Qed.
Lemma lem5457074 : term444 = True.
Proof. exact (TRANS (@lem5457026) (@lem5457073)). Qed.
Lemma lem5457075 : term663 = True.
Proof. exact (TRANS (@lem5457017) (@lem5457074)). Qed.
Lemma lem5457076 : True = term663.
Proof. exact (SYM (@lem5457075)). Qed.
Lemma lem5457077 : term663.
Proof. exact (EQ_MP (@lem5457076) (@lem0)). Qed.
Lemma lem5457078 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term677 _70532 _70535.
Proof. exact (conj (@lem5457077) (@lem5456938 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457080 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5457081 (_70532 : int) (_70535 : int) : term678 _70532 _70535.
Proof. exact (@lem5457080 term272 (term405 _70532 _70535)). Qed.
Lemma lem5457082 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term679 _70532 _70535.
Proof. exact (@lem5457081 _70532 _70535 (@lem5457078 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457083 (_70532 : int) (_70535 : int) : (term680 _70532 _70535) = (term405 _70532 _70535).
Proof. exact (@lem1982733 (term405 _70532 _70535)). Qed.
Lemma lem5457084 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5457085 (_70532 : int) (_70535 : int) : (term681 _70532 _70535) = (term407 _70532 _70535).
Proof. exact (MK_COMB (@lem5457084) (@lem5457083 _70532 _70535)). Qed.
Lemma lem5457086 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5457087 (_70532 : int) (_70535 : int) : (term679 _70532 _70535) = (term408 _70532 _70535).
Proof. exact (MK_COMB (@lem5457085 _70532 _70535) (@lem5457086)). Qed.
Lemma lem5457088 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term408 _70532 _70535.
Proof. exact (EQ_MP (@lem5457087 _70532 _70535) (@lem5457082 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457089 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term682 _70532 _70535.
Proof. exact (conj (@lem5457088 _70534 _70532 _70533 _70535 h1) (@lem5457014 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457091 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5457092 (_70532 : int) (_70535 : int) : term684 _70532 _70535.
Proof. exact (@lem5457091 (term405 _70532 _70535) (term380 _70532 _70535)). Qed.
Lemma lem5457093 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term685 _70532 _70535.
Proof. exact (@lem5457092 _70532 _70535 (@lem5457089 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457094 (_70532 : int) (_70535 : int) : (term686 _70532 _70535) = (term687 _70532 _70535).
Proof. exact (@lem1982753 (term360 _70532) (real_of_int _70532) (real_of_int _70535) (term379 _70535)). Qed.
Lemma lem5457095 (_70532 : int) : (term688 _70532) = (term689 _70532).
Proof. exact (@lem1982713 term335 (real_of_int _70532)). Qed.
Lemma lem5457097 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457098 : term272 = term369.
Proof. exact (@lem5457097 term120). Qed.
Lemma lem5457100 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5457101 : term335 = term336.
Proof. exact (@lem5457100 term120). Qed.
Lemma lem5457102 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457103 : term690 = term691.
Proof. exact (MK_COMB (@lem5457102) (@lem5457101)). Qed.
Lemma lem5457104 : term692 = term693.
Proof. exact (MK_COMB (@lem5457103) (@lem5457098)). Qed.
Lemma lem5457105 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5457107 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457108 : term444 = term445.
Proof. exact (@lem5457107 (NUMERAL 0) term120). Qed.
Lemma lem5457109 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457110 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457111 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457110 h1) (fun h1 : term445 = True => @lem5457109)). Qed.
Lemma lem5457112 : term445 = True.
Proof. exact (EQ_MP (@lem5457111) (@lem5457109)). Qed.
Lemma lem5457113 : term444 = True.
Proof. exact (TRANS (@lem5457108) (@lem5457112)). Qed.
Lemma lem5457114 : True = term444.
Proof. exact (SYM (@lem5457113)). Qed.
Lemma lem5457115 : term444.
Proof. exact (EQ_MP (@lem5457114) (@lem0)). Qed.
Lemma lem5457116 : term695.
Proof. exact (@lem5457105 (@lem5457115)). Qed.
Lemma lem5457118 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457119 : term444 = term445.
Proof. exact (@lem5457118 (NUMERAL 0) term120). Qed.
Lemma lem5457120 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457121 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457122 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457121 h1) (fun h1 : term445 = True => @lem5457120)). Qed.
Lemma lem5457123 : term445 = True.
Proof. exact (EQ_MP (@lem5457122) (@lem5457120)). Qed.
Lemma lem5457124 : term444 = True.
Proof. exact (TRANS (@lem5457119) (@lem5457123)). Qed.
Lemma lem5457125 : True = term444.
Proof. exact (SYM (@lem5457124)). Qed.
Lemma lem5457126 : term444.
Proof. exact (EQ_MP (@lem5457125) (@lem0)). Qed.
Lemma lem5457127 : term696.
Proof. exact (@lem5457116 (@lem5457126)). Qed.
Lemma lem5457129 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457130 : term444 = term445.
Proof. exact (@lem5457129 (NUMERAL 0) term120). Qed.
Lemma lem5457131 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457132 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457133 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457132 h1) (fun h1 : term445 = True => @lem5457131)). Qed.
Lemma lem5457134 : term445 = True.
Proof. exact (EQ_MP (@lem5457133) (@lem5457131)). Qed.
Lemma lem5457135 : term444 = True.
Proof. exact (TRANS (@lem5457130) (@lem5457134)). Qed.
Lemma lem5457136 : True = term444.
Proof. exact (SYM (@lem5457135)). Qed.
Lemma lem5457137 : term444.
Proof. exact (EQ_MP (@lem5457136) (@lem0)). Qed.
Lemma lem5457138 : term697.
Proof. exact (@lem5457127 (@lem5457137)). Qed.
Lemma lem5457140 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457141 : term344 = term345.
Proof. exact (@lem5457140 term120 term120). Qed.
Lemma lem5457142 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457143 : term347 = term120.
Proof. exact (EQ_MP (@lem5457142) (@lem940073)). Qed.
Lemma lem5457144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457145 : term345 = term272.
Proof. exact (MK_COMB (@lem5457144) (@lem5457143)). Qed.
Lemma lem5457146 : term344 = term272.
Proof. exact (TRANS (@lem5457141) (@lem5457145)). Qed.
Lemma lem5457148 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5457149 : term370 = term375.
Proof. exact (@lem5457148 term120 term120). Qed.
Lemma lem5457150 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457151 : term347 = term120.
Proof. exact (EQ_MP (@lem5457150) (@lem940073)). Qed.
Lemma lem5457152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457153 : term345 = term272.
Proof. exact (MK_COMB (@lem5457152) (@lem5457151)). Qed.
Lemma lem5457154 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5457155 : term375 = term335.
Proof. exact (MK_COMB (@lem5457154) (@lem5457153)). Qed.
Lemma lem5457156 : term370 = term335.
Proof. exact (TRANS (@lem5457149) (@lem5457155)). Qed.
Lemma lem5457157 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457158 : term698 = term690.
Proof. exact (MK_COMB (@lem5457157) (@lem5457156)). Qed.
Lemma lem5457159 : term699 = term692.
Proof. exact (MK_COMB (@lem5457158) (@lem5457146)). Qed.
Lemma lem5457161 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5457162 : term692 = term260.
Proof. exact (@lem5457161 term120). Qed.
Lemma lem5457163 : term699 = term260.
Proof. exact (TRANS (@lem5457159) (@lem5457162)). Qed.
Lemma lem5457164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457165 : term701 = term454.
Proof. exact (MK_COMB (@lem5457164) (@lem5457163)). Qed.
Lemma lem5457166 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5457167 : term702 = term456.
Proof. exact (MK_COMB (@lem5457165) (@lem5457166)). Qed.
Lemma lem5457169 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457170 : term456 = term260.
Proof. exact (@lem5457169 term120). Qed.
Lemma lem5457171 : term702 = term260.
Proof. exact (TRANS (@lem5457167) (@lem5457170)). Qed.
Lemma lem5457173 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457174 : term344 = term345.
Proof. exact (@lem5457173 term120 term120). Qed.
Lemma lem5457175 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457176 : term347 = term120.
Proof. exact (EQ_MP (@lem5457175) (@lem940073)). Qed.
Lemma lem5457177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457178 : term345 = term272.
Proof. exact (MK_COMB (@lem5457177) (@lem5457176)). Qed.
Lemma lem5457179 : term344 = term272.
Proof. exact (TRANS (@lem5457174) (@lem5457178)). Qed.
Lemma lem5457180 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5457181 : term458 = term456.
Proof. exact (MK_COMB (@lem5457180) (@lem5457179)). Qed.
Lemma lem5457183 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457184 : term456 = term260.
Proof. exact (@lem5457183 term120). Qed.
Lemma lem5457185 : term458 = term260.
Proof. exact (TRANS (@lem5457181) (@lem5457184)). Qed.
Lemma lem5457186 : term260 = term458.
Proof. exact (SYM (@lem5457185)). Qed.
Lemma lem5457187 : term702 = term458.
Proof. exact (TRANS (@lem5457171) (@lem5457186)). Qed.
Lemma lem5457188 : term693 = term332.
Proof. exact (@lem5457138 (@lem5457187)). Qed.
Lemma lem5457189 : term692 = term332.
Proof. exact (TRANS (@lem5457104) (@lem5457188)). Qed.
Lemma lem5457191 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5457192 : term332 = term260.
Proof. exact (@lem5457191 term260). Qed.
Lemma lem5457193 : term692 = term260.
Proof. exact (TRANS (@lem5457189) (@lem5457192)). Qed.
Lemma lem5457194 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457195 : term703 = term454.
Proof. exact (MK_COMB (@lem5457194) (@lem5457193)). Qed.
Lemma lem5457196 (_70532 : int) : (real_of_int _70532) = (real_of_int _70532).
Proof. exact (eq_refl (real_of_int _70532)). Qed.
Lemma lem5457197 (_70532 : int) : (term689 _70532) = (term704 _70532).
Proof. exact (MK_COMB (@lem5457195) (@lem5457196 _70532)). Qed.
Lemma lem5457198 (_70532 : int) : (term688 _70532) = (term704 _70532).
Proof. exact (TRANS (@lem5457095 _70532) (@lem5457197 _70532)). Qed.
Lemma lem5457199 (_70532 : int) : (term704 _70532) = term260.
Proof. exact (@lem1982719 (real_of_int _70532)). Qed.
Lemma lem5457200 (_70532 : int) : (term688 _70532) = term260.
Proof. exact (TRANS (@lem5457198 _70532) (@lem5457199 _70532)). Qed.
Lemma lem5457201 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457202 (_70532 : int) : (term705 _70532) = term706.
Proof. exact (MK_COMB (@lem5457201) (@lem5457200 _70532)). Qed.
Lemma lem5457203 (_70535 : int) : (term707 _70535) = (term708 _70535).
Proof. exact (@lem1982763 (real_of_int _70535) (term360 _70535) term335). Qed.
Lemma lem5457204 (_70535 : int) : (term709 _70535) = (term689 _70535).
Proof. exact (@lem1982715 term335 (real_of_int _70535)). Qed.
Lemma lem5457206 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457207 : term272 = term369.
Proof. exact (@lem5457206 term120). Qed.
Lemma lem5457209 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5457210 : term335 = term336.
Proof. exact (@lem5457209 term120). Qed.
Lemma lem5457211 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457212 : term690 = term691.
Proof. exact (MK_COMB (@lem5457211) (@lem5457210)). Qed.
Lemma lem5457213 : term692 = term693.
Proof. exact (MK_COMB (@lem5457212) (@lem5457207)). Qed.
Lemma lem5457214 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5457216 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457217 : term444 = term445.
Proof. exact (@lem5457216 (NUMERAL 0) term120). Qed.
Lemma lem5457218 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457219 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457220 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457219 h1) (fun h1 : term445 = True => @lem5457218)). Qed.
Lemma lem5457221 : term445 = True.
Proof. exact (EQ_MP (@lem5457220) (@lem5457218)). Qed.
Lemma lem5457222 : term444 = True.
Proof. exact (TRANS (@lem5457217) (@lem5457221)). Qed.
Lemma lem5457223 : True = term444.
Proof. exact (SYM (@lem5457222)). Qed.
Lemma lem5457224 : term444.
Proof. exact (EQ_MP (@lem5457223) (@lem0)). Qed.
Lemma lem5457225 : term695.
Proof. exact (@lem5457214 (@lem5457224)). Qed.
Lemma lem5457227 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457228 : term444 = term445.
Proof. exact (@lem5457227 (NUMERAL 0) term120). Qed.
Lemma lem5457229 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457230 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457231 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457230 h1) (fun h1 : term445 = True => @lem5457229)). Qed.
Lemma lem5457232 : term445 = True.
Proof. exact (EQ_MP (@lem5457231) (@lem5457229)). Qed.
Lemma lem5457233 : term444 = True.
Proof. exact (TRANS (@lem5457228) (@lem5457232)). Qed.
Lemma lem5457234 : True = term444.
Proof. exact (SYM (@lem5457233)). Qed.
Lemma lem5457235 : term444.
Proof. exact (EQ_MP (@lem5457234) (@lem0)). Qed.
Lemma lem5457236 : term696.
Proof. exact (@lem5457225 (@lem5457235)). Qed.
Lemma lem5457238 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457239 : term444 = term445.
Proof. exact (@lem5457238 (NUMERAL 0) term120). Qed.
Lemma lem5457240 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457241 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457242 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457241 h1) (fun h1 : term445 = True => @lem5457240)). Qed.
Lemma lem5457243 : term445 = True.
Proof. exact (EQ_MP (@lem5457242) (@lem5457240)). Qed.
Lemma lem5457244 : term444 = True.
Proof. exact (TRANS (@lem5457239) (@lem5457243)). Qed.
Lemma lem5457245 : True = term444.
Proof. exact (SYM (@lem5457244)). Qed.
Lemma lem5457246 : term444.
Proof. exact (EQ_MP (@lem5457245) (@lem0)). Qed.
Lemma lem5457247 : term697.
Proof. exact (@lem5457236 (@lem5457246)). Qed.
Lemma lem5457249 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457250 : term344 = term345.
Proof. exact (@lem5457249 term120 term120). Qed.
Lemma lem5457251 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457252 : term347 = term120.
Proof. exact (EQ_MP (@lem5457251) (@lem940073)). Qed.
Lemma lem5457253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457254 : term345 = term272.
Proof. exact (MK_COMB (@lem5457253) (@lem5457252)). Qed.
Lemma lem5457255 : term344 = term272.
Proof. exact (TRANS (@lem5457250) (@lem5457254)). Qed.
Lemma lem5457257 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5457258 : term370 = term375.
Proof. exact (@lem5457257 term120 term120). Qed.
Lemma lem5457259 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457260 : term347 = term120.
Proof. exact (EQ_MP (@lem5457259) (@lem940073)). Qed.
Lemma lem5457261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457262 : term345 = term272.
Proof. exact (MK_COMB (@lem5457261) (@lem5457260)). Qed.
Lemma lem5457263 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5457264 : term375 = term335.
Proof. exact (MK_COMB (@lem5457263) (@lem5457262)). Qed.
Lemma lem5457265 : term370 = term335.
Proof. exact (TRANS (@lem5457258) (@lem5457264)). Qed.
Lemma lem5457266 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457267 : term698 = term690.
Proof. exact (MK_COMB (@lem5457266) (@lem5457265)). Qed.
Lemma lem5457268 : term699 = term692.
Proof. exact (MK_COMB (@lem5457267) (@lem5457255)). Qed.
Lemma lem5457270 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5457271 : term692 = term260.
Proof. exact (@lem5457270 term120). Qed.
Lemma lem5457272 : term699 = term260.
Proof. exact (TRANS (@lem5457268) (@lem5457271)). Qed.
Lemma lem5457273 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457274 : term701 = term454.
Proof. exact (MK_COMB (@lem5457273) (@lem5457272)). Qed.
Lemma lem5457275 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5457276 : term702 = term456.
Proof. exact (MK_COMB (@lem5457274) (@lem5457275)). Qed.
Lemma lem5457278 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457279 : term456 = term260.
Proof. exact (@lem5457278 term120). Qed.
Lemma lem5457280 : term702 = term260.
Proof. exact (TRANS (@lem5457276) (@lem5457279)). Qed.
Lemma lem5457282 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457283 : term344 = term345.
Proof. exact (@lem5457282 term120 term120). Qed.
Lemma lem5457284 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457285 : term347 = term120.
Proof. exact (EQ_MP (@lem5457284) (@lem940073)). Qed.
Lemma lem5457286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457287 : term345 = term272.
Proof. exact (MK_COMB (@lem5457286) (@lem5457285)). Qed.
Lemma lem5457288 : term344 = term272.
Proof. exact (TRANS (@lem5457283) (@lem5457287)). Qed.
Lemma lem5457289 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5457290 : term458 = term456.
Proof. exact (MK_COMB (@lem5457289) (@lem5457288)). Qed.
Lemma lem5457292 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457293 : term456 = term260.
Proof. exact (@lem5457292 term120). Qed.
Lemma lem5457294 : term458 = term260.
Proof. exact (TRANS (@lem5457290) (@lem5457293)). Qed.
Lemma lem5457295 : term260 = term458.
Proof. exact (SYM (@lem5457294)). Qed.
Lemma lem5457296 : term702 = term458.
Proof. exact (TRANS (@lem5457280) (@lem5457295)). Qed.
Lemma lem5457297 : term693 = term332.
Proof. exact (@lem5457247 (@lem5457296)). Qed.
Lemma lem5457298 : term692 = term332.
Proof. exact (TRANS (@lem5457213) (@lem5457297)). Qed.
Lemma lem5457300 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5457301 : term332 = term260.
Proof. exact (@lem5457300 term260). Qed.
Lemma lem5457302 : term692 = term260.
Proof. exact (TRANS (@lem5457298) (@lem5457301)). Qed.
Lemma lem5457303 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457304 : term703 = term454.
Proof. exact (MK_COMB (@lem5457303) (@lem5457302)). Qed.
Lemma lem5457305 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5457306 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5457304) (@lem5457305 _70535)). Qed.
Lemma lem5457307 (_70535 : int) : (term709 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5457204 _70535) (@lem5457306 _70535)). Qed.
Lemma lem5457308 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5457309 (_70535 : int) : (term709 _70535) = term260.
Proof. exact (TRANS (@lem5457307 _70535) (@lem5457308 _70535)). Qed.
Lemma lem5457310 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457311 (_70535 : int) : (term710 _70535) = term706.
Proof. exact (MK_COMB (@lem5457310) (@lem5457309 _70535)). Qed.
Lemma lem5457312 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5457313 (_70535 : int) : (term708 _70535) = term711.
Proof. exact (MK_COMB (@lem5457311 _70535) (@lem5457312)). Qed.
Lemma lem5457314 (_70535 : int) : (term707 _70535) = term711.
Proof. exact (TRANS (@lem5457203 _70535) (@lem5457313 _70535)). Qed.
Lemma lem5457315 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5457316 (_70535 : int) : (term707 _70535) = term335.
Proof. exact (TRANS (@lem5457314 _70535) (@lem5457315)). Qed.
Lemma lem5457317 (_70532 : int) (_70535 : int) : (term687 _70532 _70535) = term711.
Proof. exact (MK_COMB (@lem5457202 _70532) (@lem5457316 _70535)). Qed.
Lemma lem5457318 (_70532 : int) (_70535 : int) : (term686 _70532 _70535) = term711.
Proof. exact (TRANS (@lem5457094 _70532 _70535) (@lem5457317 _70532 _70535)). Qed.
Lemma lem5457319 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5457320 (_70532 : int) (_70535 : int) : (term686 _70532 _70535) = term335.
Proof. exact (TRANS (@lem5457318 _70532 _70535) (@lem5457319)). Qed.
Lemma lem5457321 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5457322 (_70532 : int) (_70535 : int) : (term712 _70532 _70535) = term713.
Proof. exact (MK_COMB (@lem5457321) (@lem5457320 _70532 _70535)). Qed.
Lemma lem5457323 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5457324 (_70532 : int) (_70535 : int) : (term685 _70532 _70535) = term714.
Proof. exact (MK_COMB (@lem5457322 _70532 _70535) (@lem5457323)). Qed.
Lemma lem5457325 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : term714.
Proof. exact (EQ_MP (@lem5457324 _70532 _70535) (@lem5457093 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457327 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5457328 : term714 = term715.
Proof. exact (@lem5457327 term260 term335). Qed.
Lemma lem5457330 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5457331 : term335 = term336.
Proof. exact (@lem5457330 term120). Qed.
Lemma lem5457333 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457334 : term260 = term332.
Proof. exact (@lem5457333 (NUMERAL 0)). Qed.
Lemma lem5457335 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5457336 : term262 = term716.
Proof. exact (MK_COMB (@lem5457335) (@lem5457334)). Qed.
Lemma lem5457337 : term715 = term717.
Proof. exact (MK_COMB (@lem5457336) (@lem5457331)). Qed.
Lemma lem5457338 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5457340 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457341 : term444 = term445.
Proof. exact (@lem5457340 (NUMERAL 0) term120). Qed.
Lemma lem5457342 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457343 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457344 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457343 h1) (fun h1 : term445 = True => @lem5457342)). Qed.
Lemma lem5457345 : term445 = True.
Proof. exact (EQ_MP (@lem5457344) (@lem5457342)). Qed.
Lemma lem5457346 : term444 = True.
Proof. exact (TRANS (@lem5457341) (@lem5457345)). Qed.
Lemma lem5457347 : True = term444.
Proof. exact (SYM (@lem5457346)). Qed.
Lemma lem5457348 : term444.
Proof. exact (EQ_MP (@lem5457347) (@lem0)). Qed.
Lemma lem5457349 : term719.
Proof. exact (@lem5457338 (@lem5457348)). Qed.
Lemma lem5457351 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457352 : term444 = term445.
Proof. exact (@lem5457351 (NUMERAL 0) term120). Qed.
Lemma lem5457353 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457354 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457355 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457354 h1) (fun h1 : term445 = True => @lem5457353)). Qed.
Lemma lem5457356 : term445 = True.
Proof. exact (EQ_MP (@lem5457355) (@lem5457353)). Qed.
Lemma lem5457357 : term444 = True.
Proof. exact (TRANS (@lem5457352) (@lem5457356)). Qed.
Lemma lem5457358 : True = term444.
Proof. exact (SYM (@lem5457357)). Qed.
Lemma lem5457359 : term444.
Proof. exact (EQ_MP (@lem5457358) (@lem0)). Qed.
Lemma lem5457360 : term717 = term720.
Proof. exact (@lem5457349 (@lem5457359)). Qed.
Lemma lem5457362 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5457363 : term370 = term375.
Proof. exact (@lem5457362 term120 term120). Qed.
Lemma lem5457364 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457365 : term347 = term120.
Proof. exact (EQ_MP (@lem5457364) (@lem940073)). Qed.
Lemma lem5457366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457367 : term345 = term272.
Proof. exact (MK_COMB (@lem5457366) (@lem5457365)). Qed.
Lemma lem5457368 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5457369 : term375 = term335.
Proof. exact (MK_COMB (@lem5457368) (@lem5457367)). Qed.
Lemma lem5457370 : term370 = term335.
Proof. exact (TRANS (@lem5457363) (@lem5457369)). Qed.
Lemma lem5457372 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457373 : term456 = term260.
Proof. exact (@lem5457372 term120). Qed.
Lemma lem5457374 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5457375 : term721 = term262.
Proof. exact (MK_COMB (@lem5457374) (@lem5457373)). Qed.
Lemma lem5457376 : term720 = term715.
Proof. exact (MK_COMB (@lem5457375) (@lem5457370)). Qed.
Lemma lem5457378 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5457379 : term715 = term724.
Proof. exact (@lem5457378 (NUMERAL 0) term120). Qed.
Lemma lem5457380 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457381 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5457382 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457381 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5457380)). Qed.
Lemma lem5457383 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5457382) (@lem5457380)). Qed.
Lemma lem5457384 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5457385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5457386 : term725 = (and True).
Proof. exact (MK_COMB (@lem5457385) (@lem5457384)). Qed.
Lemma lem5457387 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5457386) (@lem5457383)). Qed.
Lemma lem5457389 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5457390 : term724 = False.
Proof. exact (TRANS (@lem5457387) (@lem5457389)). Qed.
Lemma lem5457391 : term715 = False.
Proof. exact (TRANS (@lem5457379) (@lem5457390)). Qed.
Lemma lem5457392 : term720 = False.
Proof. exact (TRANS (@lem5457376) (@lem5457391)). Qed.
Lemma lem5457393 : term717 = False.
Proof. exact (TRANS (@lem5457360) (@lem5457392)). Qed.
Lemma lem5457394 : term715 = False.
Proof. exact (TRANS (@lem5457337) (@lem5457393)). Qed.
Lemma lem5457395 : term714 = False.
Proof. exact (TRANS (@lem5457328) (@lem5457394)). Qed.
Lemma lem5457396 (_70534 : int) (_70532 : int) (_70533 : int) (_70535 : int) (h1 : term796 _70534 _70532 _70533 _70535) : False.
Proof. exact (EQ_MP (@lem5457395) (@lem5457325 _70534 _70532 _70533 _70535 h1)). Qed.
Lemma lem5457397 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term797 _70532 _70534 _70533 _70535.
Proof. exact (h1). Qed.
Lemma lem5457398 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term642 _70532 _70534 _70533 _70535.
Proof. exact (proj2 (@lem5457397 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457400 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term611 _70532 _70534 _70533 _70535.
Proof. exact (proj2 (@lem5457398 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457402 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term580 _70532 _70534 _70533 _70535.
Proof. exact (proj2 (@lem5457400 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457404 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term549 _70532 _70534 _70533 _70535.
Proof. exact (proj2 (@lem5457402 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457406 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term518 _70532 _70534 _70533 _70535.
Proof. exact (proj2 (@lem5457404 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457408 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term493 _70533 _70535.
Proof. exact (proj2 (@lem5457406 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457412 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term410 _70533 _70535.
Proof. exact (proj2 (@lem5457408 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457413 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term414 _70533 _70535.
Proof. exact (proj1 (@lem5457408 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457415 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5457416 : term663 = term444.
Proof. exact (@lem5457415 term260 term272). Qed.
Lemma lem5457418 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457419 : term272 = term369.
Proof. exact (@lem5457418 term120). Qed.
Lemma lem5457421 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457422 : term260 = term332.
Proof. exact (@lem5457421 (NUMERAL 0)). Qed.
Lemma lem5457423 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457424 : term664 = term665.
Proof. exact (MK_COMB (@lem5457423) (@lem5457422)). Qed.
Lemma lem5457425 : term444 = term666.
Proof. exact (MK_COMB (@lem5457424) (@lem5457419)). Qed.
Lemma lem5457426 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5457428 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457429 : term444 = term445.
Proof. exact (@lem5457428 (NUMERAL 0) term120). Qed.
Lemma lem5457430 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457431 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457432 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457431 h1) (fun h1 : term445 = True => @lem5457430)). Qed.
Lemma lem5457433 : term445 = True.
Proof. exact (EQ_MP (@lem5457432) (@lem5457430)). Qed.
Lemma lem5457434 : term444 = True.
Proof. exact (TRANS (@lem5457429) (@lem5457433)). Qed.
Lemma lem5457435 : True = term444.
Proof. exact (SYM (@lem5457434)). Qed.
Lemma lem5457436 : term444.
Proof. exact (EQ_MP (@lem5457435) (@lem0)). Qed.
Lemma lem5457437 : term668.
Proof. exact (@lem5457426 (@lem5457436)). Qed.
Lemma lem5457439 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457440 : term444 = term445.
Proof. exact (@lem5457439 (NUMERAL 0) term120). Qed.
Lemma lem5457441 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457442 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457443 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457442 h1) (fun h1 : term445 = True => @lem5457441)). Qed.
Lemma lem5457444 : term445 = True.
Proof. exact (EQ_MP (@lem5457443) (@lem5457441)). Qed.
Lemma lem5457445 : term444 = True.
Proof. exact (TRANS (@lem5457440) (@lem5457444)). Qed.
Lemma lem5457446 : True = term444.
Proof. exact (SYM (@lem5457445)). Qed.
Lemma lem5457447 : term444.
Proof. exact (EQ_MP (@lem5457446) (@lem0)). Qed.
Lemma lem5457448 : term666 = term669.
Proof. exact (@lem5457437 (@lem5457447)). Qed.
Lemma lem5457450 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457451 : term344 = term345.
Proof. exact (@lem5457450 term120 term120). Qed.
Lemma lem5457452 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457453 : term347 = term120.
Proof. exact (EQ_MP (@lem5457452) (@lem940073)). Qed.
Lemma lem5457454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457455 : term345 = term272.
Proof. exact (MK_COMB (@lem5457454) (@lem5457453)). Qed.
Lemma lem5457456 : term344 = term272.
Proof. exact (TRANS (@lem5457451) (@lem5457455)). Qed.
Lemma lem5457458 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457459 : term456 = term260.
Proof. exact (@lem5457458 term120). Qed.
Lemma lem5457460 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457461 : term670 = term664.
Proof. exact (MK_COMB (@lem5457460) (@lem5457459)). Qed.
Lemma lem5457462 : term669 = term444.
Proof. exact (MK_COMB (@lem5457461) (@lem5457456)). Qed.
Lemma lem5457464 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457465 : term444 = term445.
Proof. exact (@lem5457464 (NUMERAL 0) term120). Qed.
Lemma lem5457466 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457467 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457468 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457467 h1) (fun h1 : term445 = True => @lem5457466)). Qed.
Lemma lem5457469 : term445 = True.
Proof. exact (EQ_MP (@lem5457468) (@lem5457466)). Qed.
Lemma lem5457470 : term444 = True.
Proof. exact (TRANS (@lem5457465) (@lem5457469)). Qed.
Lemma lem5457471 : term669 = True.
Proof. exact (TRANS (@lem5457462) (@lem5457470)). Qed.
Lemma lem5457472 : term666 = True.
Proof. exact (TRANS (@lem5457448) (@lem5457471)). Qed.
Lemma lem5457473 : term444 = True.
Proof. exact (TRANS (@lem5457425) (@lem5457472)). Qed.
Lemma lem5457474 : term663 = True.
Proof. exact (TRANS (@lem5457416) (@lem5457473)). Qed.
Lemma lem5457475 : True = term663.
Proof. exact (SYM (@lem5457474)). Qed.
Lemma lem5457476 : term663.
Proof. exact (EQ_MP (@lem5457475) (@lem0)). Qed.
Lemma lem5457477 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term727 _70533 _70535.
Proof. exact (conj (@lem5457476) (@lem5457412 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457479 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5457480 (_70533 : int) (_70535 : int) : term728 _70533 _70535.
Proof. exact (@lem5457479 term272 (term404 _70533 _70535)). Qed.
Lemma lem5457481 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term729 _70533 _70535.
Proof. exact (@lem5457480 _70533 _70535 (@lem5457477 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457482 (_70533 : int) (_70535 : int) : (term730 _70533 _70535) = (term404 _70533 _70535).
Proof. exact (@lem1982733 (term404 _70533 _70535)). Qed.
Lemma lem5457483 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5457484 (_70533 : int) (_70535 : int) : (term731 _70533 _70535) = (term409 _70533 _70535).
Proof. exact (MK_COMB (@lem5457483) (@lem5457482 _70533 _70535)). Qed.
Lemma lem5457485 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5457486 (_70533 : int) (_70535 : int) : (term729 _70533 _70535) = (term410 _70533 _70535).
Proof. exact (MK_COMB (@lem5457484 _70533 _70535) (@lem5457485)). Qed.
Lemma lem5457487 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term410 _70533 _70535.
Proof. exact (EQ_MP (@lem5457486 _70533 _70535) (@lem5457481 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457489 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5457490 : term663 = term444.
Proof. exact (@lem5457489 term260 term272). Qed.
Lemma lem5457492 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457493 : term272 = term369.
Proof. exact (@lem5457492 term120). Qed.
Lemma lem5457495 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457496 : term260 = term332.
Proof. exact (@lem5457495 (NUMERAL 0)). Qed.
Lemma lem5457497 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457498 : term664 = term665.
Proof. exact (MK_COMB (@lem5457497) (@lem5457496)). Qed.
Lemma lem5457499 : term444 = term666.
Proof. exact (MK_COMB (@lem5457498) (@lem5457493)). Qed.
Lemma lem5457500 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5457502 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457503 : term444 = term445.
Proof. exact (@lem5457502 (NUMERAL 0) term120). Qed.
Lemma lem5457504 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457505 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457506 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457505 h1) (fun h1 : term445 = True => @lem5457504)). Qed.
Lemma lem5457507 : term445 = True.
Proof. exact (EQ_MP (@lem5457506) (@lem5457504)). Qed.
Lemma lem5457508 : term444 = True.
Proof. exact (TRANS (@lem5457503) (@lem5457507)). Qed.
Lemma lem5457509 : True = term444.
Proof. exact (SYM (@lem5457508)). Qed.
Lemma lem5457510 : term444.
Proof. exact (EQ_MP (@lem5457509) (@lem0)). Qed.
Lemma lem5457511 : term668.
Proof. exact (@lem5457500 (@lem5457510)). Qed.
Lemma lem5457513 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457514 : term444 = term445.
Proof. exact (@lem5457513 (NUMERAL 0) term120). Qed.
Lemma lem5457515 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457516 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457517 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457516 h1) (fun h1 : term445 = True => @lem5457515)). Qed.
Lemma lem5457518 : term445 = True.
Proof. exact (EQ_MP (@lem5457517) (@lem5457515)). Qed.
Lemma lem5457519 : term444 = True.
Proof. exact (TRANS (@lem5457514) (@lem5457518)). Qed.
Lemma lem5457520 : True = term444.
Proof. exact (SYM (@lem5457519)). Qed.
Lemma lem5457521 : term444.
Proof. exact (EQ_MP (@lem5457520) (@lem0)). Qed.
Lemma lem5457522 : term666 = term669.
Proof. exact (@lem5457511 (@lem5457521)). Qed.
Lemma lem5457524 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457525 : term344 = term345.
Proof. exact (@lem5457524 term120 term120). Qed.
Lemma lem5457526 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457527 : term347 = term120.
Proof. exact (EQ_MP (@lem5457526) (@lem940073)). Qed.
Lemma lem5457528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457529 : term345 = term272.
Proof. exact (MK_COMB (@lem5457528) (@lem5457527)). Qed.
Lemma lem5457530 : term344 = term272.
Proof. exact (TRANS (@lem5457525) (@lem5457529)). Qed.
Lemma lem5457532 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457533 : term456 = term260.
Proof. exact (@lem5457532 term120). Qed.
Lemma lem5457534 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457535 : term670 = term664.
Proof. exact (MK_COMB (@lem5457534) (@lem5457533)). Qed.
Lemma lem5457536 : term669 = term444.
Proof. exact (MK_COMB (@lem5457535) (@lem5457530)). Qed.
Lemma lem5457538 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457539 : term444 = term445.
Proof. exact (@lem5457538 (NUMERAL 0) term120). Qed.
Lemma lem5457540 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457541 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457542 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457541 h1) (fun h1 : term445 = True => @lem5457540)). Qed.
Lemma lem5457543 : term445 = True.
Proof. exact (EQ_MP (@lem5457542) (@lem5457540)). Qed.
Lemma lem5457544 : term444 = True.
Proof. exact (TRANS (@lem5457539) (@lem5457543)). Qed.
Lemma lem5457545 : term669 = True.
Proof. exact (TRANS (@lem5457536) (@lem5457544)). Qed.
Lemma lem5457546 : term666 = True.
Proof. exact (TRANS (@lem5457522) (@lem5457545)). Qed.
Lemma lem5457547 : term444 = True.
Proof. exact (TRANS (@lem5457499) (@lem5457546)). Qed.
Lemma lem5457548 : term663 = True.
Proof. exact (TRANS (@lem5457490) (@lem5457547)). Qed.
Lemma lem5457549 : True = term663.
Proof. exact (SYM (@lem5457548)). Qed.
Lemma lem5457550 : term663.
Proof. exact (EQ_MP (@lem5457549) (@lem0)). Qed.
Lemma lem5457551 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term752 _70533 _70535.
Proof. exact (conj (@lem5457550) (@lem5457413 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457553 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5457554 (_70533 : int) (_70535 : int) : term753 _70533 _70535.
Proof. exact (@lem5457553 term272 (term395 _70533 _70535)). Qed.
Lemma lem5457555 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term754 _70533 _70535.
Proof. exact (@lem5457554 _70533 _70535 (@lem5457551 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457556 (_70533 : int) (_70535 : int) : (term755 _70533 _70535) = (term395 _70533 _70535).
Proof. exact (@lem1982733 (term395 _70533 _70535)). Qed.
Lemma lem5457557 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5457558 (_70533 : int) (_70535 : int) : (term756 _70533 _70535) = (term413 _70533 _70535).
Proof. exact (MK_COMB (@lem5457557) (@lem5457556 _70533 _70535)). Qed.
Lemma lem5457559 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5457560 (_70533 : int) (_70535 : int) : (term754 _70533 _70535) = (term414 _70533 _70535).
Proof. exact (MK_COMB (@lem5457558 _70533 _70535) (@lem5457559)). Qed.
Lemma lem5457561 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term414 _70533 _70535.
Proof. exact (EQ_MP (@lem5457560 _70533 _70535) (@lem5457555 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457562 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term493 _70533 _70535.
Proof. exact (conj (@lem5457561 _70532 _70534 _70533 _70535 h1) (@lem5457487 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457564 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5457565 (_70533 : int) (_70535 : int) : term757 _70533 _70535.
Proof. exact (@lem5457564 (term395 _70533 _70535) (term404 _70533 _70535)). Qed.
Lemma lem5457566 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term758 _70533 _70535.
Proof. exact (@lem5457565 _70533 _70535 (@lem5457562 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457567 (_70533 : int) (_70535 : int) : (term759 _70533 _70535) = (term760 _70533 _70535).
Proof. exact (@lem1982753 (term360 _70533) (real_of_int _70533) (term749 _70535) (term360 _70535)). Qed.
Lemma lem5457568 (_70533 : int) : (term688 _70533) = (term689 _70533).
Proof. exact (@lem1982713 term335 (real_of_int _70533)). Qed.
Lemma lem5457570 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457571 : term272 = term369.
Proof. exact (@lem5457570 term120). Qed.
Lemma lem5457573 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5457574 : term335 = term336.
Proof. exact (@lem5457573 term120). Qed.
Lemma lem5457575 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457576 : term690 = term691.
Proof. exact (MK_COMB (@lem5457575) (@lem5457574)). Qed.
Lemma lem5457577 : term692 = term693.
Proof. exact (MK_COMB (@lem5457576) (@lem5457571)). Qed.
Lemma lem5457578 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5457580 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457581 : term444 = term445.
Proof. exact (@lem5457580 (NUMERAL 0) term120). Qed.
Lemma lem5457582 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457583 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457584 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457583 h1) (fun h1 : term445 = True => @lem5457582)). Qed.
Lemma lem5457585 : term445 = True.
Proof. exact (EQ_MP (@lem5457584) (@lem5457582)). Qed.
Lemma lem5457586 : term444 = True.
Proof. exact (TRANS (@lem5457581) (@lem5457585)). Qed.
Lemma lem5457587 : True = term444.
Proof. exact (SYM (@lem5457586)). Qed.
Lemma lem5457588 : term444.
Proof. exact (EQ_MP (@lem5457587) (@lem0)). Qed.
Lemma lem5457589 : term695.
Proof. exact (@lem5457578 (@lem5457588)). Qed.
Lemma lem5457591 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457592 : term444 = term445.
Proof. exact (@lem5457591 (NUMERAL 0) term120). Qed.
Lemma lem5457593 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457594 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457595 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457594 h1) (fun h1 : term445 = True => @lem5457593)). Qed.
Lemma lem5457596 : term445 = True.
Proof. exact (EQ_MP (@lem5457595) (@lem5457593)). Qed.
Lemma lem5457597 : term444 = True.
Proof. exact (TRANS (@lem5457592) (@lem5457596)). Qed.
Lemma lem5457598 : True = term444.
Proof. exact (SYM (@lem5457597)). Qed.
Lemma lem5457599 : term444.
Proof. exact (EQ_MP (@lem5457598) (@lem0)). Qed.
Lemma lem5457600 : term696.
Proof. exact (@lem5457589 (@lem5457599)). Qed.
Lemma lem5457602 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457603 : term444 = term445.
Proof. exact (@lem5457602 (NUMERAL 0) term120). Qed.
Lemma lem5457604 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457605 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457606 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457605 h1) (fun h1 : term445 = True => @lem5457604)). Qed.
Lemma lem5457607 : term445 = True.
Proof. exact (EQ_MP (@lem5457606) (@lem5457604)). Qed.
Lemma lem5457608 : term444 = True.
Proof. exact (TRANS (@lem5457603) (@lem5457607)). Qed.
Lemma lem5457609 : True = term444.
Proof. exact (SYM (@lem5457608)). Qed.
Lemma lem5457610 : term444.
Proof. exact (EQ_MP (@lem5457609) (@lem0)). Qed.
Lemma lem5457611 : term697.
Proof. exact (@lem5457600 (@lem5457610)). Qed.
Lemma lem5457613 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457614 : term344 = term345.
Proof. exact (@lem5457613 term120 term120). Qed.
Lemma lem5457615 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457616 : term347 = term120.
Proof. exact (EQ_MP (@lem5457615) (@lem940073)). Qed.
Lemma lem5457617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457618 : term345 = term272.
Proof. exact (MK_COMB (@lem5457617) (@lem5457616)). Qed.
Lemma lem5457619 : term344 = term272.
Proof. exact (TRANS (@lem5457614) (@lem5457618)). Qed.
Lemma lem5457621 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5457622 : term370 = term375.
Proof. exact (@lem5457621 term120 term120). Qed.
Lemma lem5457623 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457624 : term347 = term120.
Proof. exact (EQ_MP (@lem5457623) (@lem940073)). Qed.
Lemma lem5457625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457626 : term345 = term272.
Proof. exact (MK_COMB (@lem5457625) (@lem5457624)). Qed.
Lemma lem5457627 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5457628 : term375 = term335.
Proof. exact (MK_COMB (@lem5457627) (@lem5457626)). Qed.
Lemma lem5457629 : term370 = term335.
Proof. exact (TRANS (@lem5457622) (@lem5457628)). Qed.
Lemma lem5457630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457631 : term698 = term690.
Proof. exact (MK_COMB (@lem5457630) (@lem5457629)). Qed.
Lemma lem5457632 : term699 = term692.
Proof. exact (MK_COMB (@lem5457631) (@lem5457619)). Qed.
Lemma lem5457634 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5457635 : term692 = term260.
Proof. exact (@lem5457634 term120). Qed.
Lemma lem5457636 : term699 = term260.
Proof. exact (TRANS (@lem5457632) (@lem5457635)). Qed.
Lemma lem5457637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457638 : term701 = term454.
Proof. exact (MK_COMB (@lem5457637) (@lem5457636)). Qed.
Lemma lem5457639 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5457640 : term702 = term456.
Proof. exact (MK_COMB (@lem5457638) (@lem5457639)). Qed.
Lemma lem5457642 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457643 : term456 = term260.
Proof. exact (@lem5457642 term120). Qed.
Lemma lem5457644 : term702 = term260.
Proof. exact (TRANS (@lem5457640) (@lem5457643)). Qed.
Lemma lem5457646 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457647 : term344 = term345.
Proof. exact (@lem5457646 term120 term120). Qed.
Lemma lem5457648 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457649 : term347 = term120.
Proof. exact (EQ_MP (@lem5457648) (@lem940073)). Qed.
Lemma lem5457650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457651 : term345 = term272.
Proof. exact (MK_COMB (@lem5457650) (@lem5457649)). Qed.
Lemma lem5457652 : term344 = term272.
Proof. exact (TRANS (@lem5457647) (@lem5457651)). Qed.
Lemma lem5457653 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5457654 : term458 = term456.
Proof. exact (MK_COMB (@lem5457653) (@lem5457652)). Qed.
Lemma lem5457656 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457657 : term456 = term260.
Proof. exact (@lem5457656 term120). Qed.
Lemma lem5457658 : term458 = term260.
Proof. exact (TRANS (@lem5457654) (@lem5457657)). Qed.
Lemma lem5457659 : term260 = term458.
Proof. exact (SYM (@lem5457658)). Qed.
Lemma lem5457660 : term702 = term458.
Proof. exact (TRANS (@lem5457644) (@lem5457659)). Qed.
Lemma lem5457661 : term693 = term332.
Proof. exact (@lem5457611 (@lem5457660)). Qed.
Lemma lem5457662 : term692 = term332.
Proof. exact (TRANS (@lem5457577) (@lem5457661)). Qed.
Lemma lem5457664 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5457665 : term332 = term260.
Proof. exact (@lem5457664 term260). Qed.
Lemma lem5457666 : term692 = term260.
Proof. exact (TRANS (@lem5457662) (@lem5457665)). Qed.
Lemma lem5457667 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457668 : term703 = term454.
Proof. exact (MK_COMB (@lem5457667) (@lem5457666)). Qed.
Lemma lem5457669 (_70533 : int) : (real_of_int _70533) = (real_of_int _70533).
Proof. exact (eq_refl (real_of_int _70533)). Qed.
Lemma lem5457670 (_70533 : int) : (term689 _70533) = (term704 _70533).
Proof. exact (MK_COMB (@lem5457668) (@lem5457669 _70533)). Qed.
Lemma lem5457671 (_70533 : int) : (term688 _70533) = (term704 _70533).
Proof. exact (TRANS (@lem5457568 _70533) (@lem5457670 _70533)). Qed.
Lemma lem5457672 (_70533 : int) : (term704 _70533) = term260.
Proof. exact (@lem1982719 (real_of_int _70533)). Qed.
Lemma lem5457673 (_70533 : int) : (term688 _70533) = term260.
Proof. exact (TRANS (@lem5457671 _70533) (@lem5457672 _70533)). Qed.
Lemma lem5457674 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457675 (_70533 : int) : (term705 _70533) = term706.
Proof. exact (MK_COMB (@lem5457674) (@lem5457673 _70533)). Qed.
Lemma lem5457676 (_70535 : int) : (term761 _70535) = (term708 _70535).
Proof. exact (@lem1982759 (real_of_int _70535) (term360 _70535) term335). Qed.
Lemma lem5457677 (_70535 : int) : (term709 _70535) = (term689 _70535).
Proof. exact (@lem1982715 term335 (real_of_int _70535)). Qed.
Lemma lem5457679 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457680 : term272 = term369.
Proof. exact (@lem5457679 term120). Qed.
Lemma lem5457682 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5457683 : term335 = term336.
Proof. exact (@lem5457682 term120). Qed.
Lemma lem5457684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457685 : term690 = term691.
Proof. exact (MK_COMB (@lem5457684) (@lem5457683)). Qed.
Lemma lem5457686 : term692 = term693.
Proof. exact (MK_COMB (@lem5457685) (@lem5457680)). Qed.
Lemma lem5457687 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5457689 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457690 : term444 = term445.
Proof. exact (@lem5457689 (NUMERAL 0) term120). Qed.
Lemma lem5457691 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457692 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457693 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457692 h1) (fun h1 : term445 = True => @lem5457691)). Qed.
Lemma lem5457694 : term445 = True.
Proof. exact (EQ_MP (@lem5457693) (@lem5457691)). Qed.
Lemma lem5457695 : term444 = True.
Proof. exact (TRANS (@lem5457690) (@lem5457694)). Qed.
Lemma lem5457696 : True = term444.
Proof. exact (SYM (@lem5457695)). Qed.
Lemma lem5457697 : term444.
Proof. exact (EQ_MP (@lem5457696) (@lem0)). Qed.
Lemma lem5457698 : term695.
Proof. exact (@lem5457687 (@lem5457697)). Qed.
Lemma lem5457700 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457701 : term444 = term445.
Proof. exact (@lem5457700 (NUMERAL 0) term120). Qed.
Lemma lem5457702 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457703 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457704 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457703 h1) (fun h1 : term445 = True => @lem5457702)). Qed.
Lemma lem5457705 : term445 = True.
Proof. exact (EQ_MP (@lem5457704) (@lem5457702)). Qed.
Lemma lem5457706 : term444 = True.
Proof. exact (TRANS (@lem5457701) (@lem5457705)). Qed.
Lemma lem5457707 : True = term444.
Proof. exact (SYM (@lem5457706)). Qed.
Lemma lem5457708 : term444.
Proof. exact (EQ_MP (@lem5457707) (@lem0)). Qed.
Lemma lem5457709 : term696.
Proof. exact (@lem5457698 (@lem5457708)). Qed.
Lemma lem5457711 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457712 : term444 = term445.
Proof. exact (@lem5457711 (NUMERAL 0) term120). Qed.
Lemma lem5457713 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457714 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457715 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457714 h1) (fun h1 : term445 = True => @lem5457713)). Qed.
Lemma lem5457716 : term445 = True.
Proof. exact (EQ_MP (@lem5457715) (@lem5457713)). Qed.
Lemma lem5457717 : term444 = True.
Proof. exact (TRANS (@lem5457712) (@lem5457716)). Qed.
Lemma lem5457718 : True = term444.
Proof. exact (SYM (@lem5457717)). Qed.
Lemma lem5457719 : term444.
Proof. exact (EQ_MP (@lem5457718) (@lem0)). Qed.
Lemma lem5457720 : term697.
Proof. exact (@lem5457709 (@lem5457719)). Qed.
Lemma lem5457722 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457723 : term344 = term345.
Proof. exact (@lem5457722 term120 term120). Qed.
Lemma lem5457724 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457725 : term347 = term120.
Proof. exact (EQ_MP (@lem5457724) (@lem940073)). Qed.
Lemma lem5457726 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457727 : term345 = term272.
Proof. exact (MK_COMB (@lem5457726) (@lem5457725)). Qed.
Lemma lem5457728 : term344 = term272.
Proof. exact (TRANS (@lem5457723) (@lem5457727)). Qed.
Lemma lem5457730 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5457731 : term370 = term375.
Proof. exact (@lem5457730 term120 term120). Qed.
Lemma lem5457732 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457733 : term347 = term120.
Proof. exact (EQ_MP (@lem5457732) (@lem940073)). Qed.
Lemma lem5457734 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457735 : term345 = term272.
Proof. exact (MK_COMB (@lem5457734) (@lem5457733)). Qed.
Lemma lem5457736 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5457737 : term375 = term335.
Proof. exact (MK_COMB (@lem5457736) (@lem5457735)). Qed.
Lemma lem5457738 : term370 = term335.
Proof. exact (TRANS (@lem5457731) (@lem5457737)). Qed.
Lemma lem5457739 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457740 : term698 = term690.
Proof. exact (MK_COMB (@lem5457739) (@lem5457738)). Qed.
Lemma lem5457741 : term699 = term692.
Proof. exact (MK_COMB (@lem5457740) (@lem5457728)). Qed.
Lemma lem5457743 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5457744 : term692 = term260.
Proof. exact (@lem5457743 term120). Qed.
Lemma lem5457745 : term699 = term260.
Proof. exact (TRANS (@lem5457741) (@lem5457744)). Qed.
Lemma lem5457746 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457747 : term701 = term454.
Proof. exact (MK_COMB (@lem5457746) (@lem5457745)). Qed.
Lemma lem5457748 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5457749 : term702 = term456.
Proof. exact (MK_COMB (@lem5457747) (@lem5457748)). Qed.
Lemma lem5457751 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457752 : term456 = term260.
Proof. exact (@lem5457751 term120). Qed.
Lemma lem5457753 : term702 = term260.
Proof. exact (TRANS (@lem5457749) (@lem5457752)). Qed.
Lemma lem5457755 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457756 : term344 = term345.
Proof. exact (@lem5457755 term120 term120). Qed.
Lemma lem5457757 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457758 : term347 = term120.
Proof. exact (EQ_MP (@lem5457757) (@lem940073)). Qed.
Lemma lem5457759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457760 : term345 = term272.
Proof. exact (MK_COMB (@lem5457759) (@lem5457758)). Qed.
Lemma lem5457761 : term344 = term272.
Proof. exact (TRANS (@lem5457756) (@lem5457760)). Qed.
Lemma lem5457762 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5457763 : term458 = term456.
Proof. exact (MK_COMB (@lem5457762) (@lem5457761)). Qed.
Lemma lem5457765 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457766 : term456 = term260.
Proof. exact (@lem5457765 term120). Qed.
Lemma lem5457767 : term458 = term260.
Proof. exact (TRANS (@lem5457763) (@lem5457766)). Qed.
Lemma lem5457768 : term260 = term458.
Proof. exact (SYM (@lem5457767)). Qed.
Lemma lem5457769 : term702 = term458.
Proof. exact (TRANS (@lem5457753) (@lem5457768)). Qed.
Lemma lem5457770 : term693 = term332.
Proof. exact (@lem5457720 (@lem5457769)). Qed.
Lemma lem5457771 : term692 = term332.
Proof. exact (TRANS (@lem5457686) (@lem5457770)). Qed.
Lemma lem5457773 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5457774 : term332 = term260.
Proof. exact (@lem5457773 term260). Qed.
Lemma lem5457775 : term692 = term260.
Proof. exact (TRANS (@lem5457771) (@lem5457774)). Qed.
Lemma lem5457776 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5457777 : term703 = term454.
Proof. exact (MK_COMB (@lem5457776) (@lem5457775)). Qed.
Lemma lem5457778 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5457779 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5457777) (@lem5457778 _70535)). Qed.
Lemma lem5457780 (_70535 : int) : (term709 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5457677 _70535) (@lem5457779 _70535)). Qed.
Lemma lem5457781 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5457782 (_70535 : int) : (term709 _70535) = term260.
Proof. exact (TRANS (@lem5457780 _70535) (@lem5457781 _70535)). Qed.
Lemma lem5457783 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5457784 (_70535 : int) : (term710 _70535) = term706.
Proof. exact (MK_COMB (@lem5457783) (@lem5457782 _70535)). Qed.
Lemma lem5457785 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5457786 (_70535 : int) : (term708 _70535) = term711.
Proof. exact (MK_COMB (@lem5457784 _70535) (@lem5457785)). Qed.
Lemma lem5457787 (_70535 : int) : (term761 _70535) = term711.
Proof. exact (TRANS (@lem5457676 _70535) (@lem5457786 _70535)). Qed.
Lemma lem5457788 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5457789 (_70535 : int) : (term761 _70535) = term335.
Proof. exact (TRANS (@lem5457787 _70535) (@lem5457788)). Qed.
Lemma lem5457790 (_70533 : int) (_70535 : int) : (term760 _70533 _70535) = term711.
Proof. exact (MK_COMB (@lem5457675 _70533) (@lem5457789 _70535)). Qed.
Lemma lem5457791 (_70533 : int) (_70535 : int) : (term759 _70533 _70535) = term711.
Proof. exact (TRANS (@lem5457567 _70533 _70535) (@lem5457790 _70533 _70535)). Qed.
Lemma lem5457792 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5457793 (_70533 : int) (_70535 : int) : (term759 _70533 _70535) = term335.
Proof. exact (TRANS (@lem5457791 _70533 _70535) (@lem5457792)). Qed.
Lemma lem5457794 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5457795 (_70533 : int) (_70535 : int) : (term762 _70533 _70535) = term713.
Proof. exact (MK_COMB (@lem5457794) (@lem5457793 _70533 _70535)). Qed.
Lemma lem5457796 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5457797 (_70533 : int) (_70535 : int) : (term758 _70533 _70535) = term714.
Proof. exact (MK_COMB (@lem5457795 _70533 _70535) (@lem5457796)). Qed.
Lemma lem5457798 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : term714.
Proof. exact (EQ_MP (@lem5457797 _70533 _70535) (@lem5457566 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457800 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5457801 : term714 = term715.
Proof. exact (@lem5457800 term260 term335). Qed.
Lemma lem5457803 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5457804 : term335 = term336.
Proof. exact (@lem5457803 term120). Qed.
Lemma lem5457806 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457807 : term260 = term332.
Proof. exact (@lem5457806 (NUMERAL 0)). Qed.
Lemma lem5457808 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5457809 : term262 = term716.
Proof. exact (MK_COMB (@lem5457808) (@lem5457807)). Qed.
Lemma lem5457810 : term715 = term717.
Proof. exact (MK_COMB (@lem5457809) (@lem5457804)). Qed.
Lemma lem5457811 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5457813 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457814 : term444 = term445.
Proof. exact (@lem5457813 (NUMERAL 0) term120). Qed.
Lemma lem5457815 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457816 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457817 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457816 h1) (fun h1 : term445 = True => @lem5457815)). Qed.
Lemma lem5457818 : term445 = True.
Proof. exact (EQ_MP (@lem5457817) (@lem5457815)). Qed.
Lemma lem5457819 : term444 = True.
Proof. exact (TRANS (@lem5457814) (@lem5457818)). Qed.
Lemma lem5457820 : True = term444.
Proof. exact (SYM (@lem5457819)). Qed.
Lemma lem5457821 : term444.
Proof. exact (EQ_MP (@lem5457820) (@lem0)). Qed.
Lemma lem5457822 : term719.
Proof. exact (@lem5457811 (@lem5457821)). Qed.
Lemma lem5457824 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457825 : term444 = term445.
Proof. exact (@lem5457824 (NUMERAL 0) term120). Qed.
Lemma lem5457826 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457827 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457828 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457827 h1) (fun h1 : term445 = True => @lem5457826)). Qed.
Lemma lem5457829 : term445 = True.
Proof. exact (EQ_MP (@lem5457828) (@lem5457826)). Qed.
Lemma lem5457830 : term444 = True.
Proof. exact (TRANS (@lem5457825) (@lem5457829)). Qed.
Lemma lem5457831 : True = term444.
Proof. exact (SYM (@lem5457830)). Qed.
Lemma lem5457832 : term444.
Proof. exact (EQ_MP (@lem5457831) (@lem0)). Qed.
Lemma lem5457833 : term717 = term720.
Proof. exact (@lem5457822 (@lem5457832)). Qed.
Lemma lem5457835 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5457836 : term370 = term375.
Proof. exact (@lem5457835 term120 term120). Qed.
Lemma lem5457837 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457838 : term347 = term120.
Proof. exact (EQ_MP (@lem5457837) (@lem940073)). Qed.
Lemma lem5457839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457840 : term345 = term272.
Proof. exact (MK_COMB (@lem5457839) (@lem5457838)). Qed.
Lemma lem5457841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5457842 : term375 = term335.
Proof. exact (MK_COMB (@lem5457841) (@lem5457840)). Qed.
Lemma lem5457843 : term370 = term335.
Proof. exact (TRANS (@lem5457836) (@lem5457842)). Qed.
Lemma lem5457845 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457846 : term456 = term260.
Proof. exact (@lem5457845 term120). Qed.
Lemma lem5457847 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5457848 : term721 = term262.
Proof. exact (MK_COMB (@lem5457847) (@lem5457846)). Qed.
Lemma lem5457849 : term720 = term715.
Proof. exact (MK_COMB (@lem5457848) (@lem5457843)). Qed.
Lemma lem5457851 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5457852 : term715 = term724.
Proof. exact (@lem5457851 (NUMERAL 0) term120). Qed.
Lemma lem5457853 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457854 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5457855 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457854 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5457853)). Qed.
Lemma lem5457856 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5457855) (@lem5457853)). Qed.
Lemma lem5457857 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5457858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5457859 : term725 = (and True).
Proof. exact (MK_COMB (@lem5457858) (@lem5457857)). Qed.
Lemma lem5457860 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5457859) (@lem5457856)). Qed.
Lemma lem5457862 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5457863 : term724 = False.
Proof. exact (TRANS (@lem5457860) (@lem5457862)). Qed.
Lemma lem5457864 : term715 = False.
Proof. exact (TRANS (@lem5457852) (@lem5457863)). Qed.
Lemma lem5457865 : term720 = False.
Proof. exact (TRANS (@lem5457849) (@lem5457864)). Qed.
Lemma lem5457866 : term717 = False.
Proof. exact (TRANS (@lem5457833) (@lem5457865)). Qed.
Lemma lem5457867 : term715 = False.
Proof. exact (TRANS (@lem5457810) (@lem5457866)). Qed.
Lemma lem5457868 : term714 = False.
Proof. exact (TRANS (@lem5457801) (@lem5457867)). Qed.
Lemma lem5457869 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term797 _70532 _70534 _70533 _70535) : False.
Proof. exact (EQ_MP (@lem5457868) (@lem5457798 _70532 _70534 _70533 _70535 h1)). Qed.
Lemma lem5457870 (_70532 : int) (_70534 : int) (_70533 : int) (_70535 : int) (h1 : term640 _70532 _70534 _70533 _70535) : False.
Proof. exact (or_elim (@lem5456923 _70532 _70534 _70533 _70535 h1) (fun h0 : term796 _70534 _70532 _70533 _70535 => @lem5457396 _70534 _70532 _70533 _70535 h0) (fun h0 : term797 _70532 _70534 _70533 _70535 => @lem5457869 _70532 _70534 _70533 _70535 h0)). Qed.
Lemma lem5457871 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term636 _70532 _70533 _70534 _70535) : term636 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5457872 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term798 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5457873 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term637 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457872 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457875 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term606 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457873 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457877 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term575 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457875 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457879 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term544 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457877 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457881 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term513 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457879 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457883 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term488 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457881 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457884 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term428 _70532 _70533 _70534 _70535.
Proof. exact (proj1 (@lem5457881 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457885 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term421 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457884 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457887 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term399 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5457883 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457890 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5457891 : term663 = term444.
Proof. exact (@lem5457890 term260 term272). Qed.
Lemma lem5457893 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457894 : term272 = term369.
Proof. exact (@lem5457893 term120). Qed.
Lemma lem5457896 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457897 : term260 = term332.
Proof. exact (@lem5457896 (NUMERAL 0)). Qed.
Lemma lem5457898 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457899 : term664 = term665.
Proof. exact (MK_COMB (@lem5457898) (@lem5457897)). Qed.
Lemma lem5457900 : term444 = term666.
Proof. exact (MK_COMB (@lem5457899) (@lem5457894)). Qed.
Lemma lem5457901 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5457903 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457904 : term444 = term445.
Proof. exact (@lem5457903 (NUMERAL 0) term120). Qed.
Lemma lem5457905 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457906 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457907 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457906 h1) (fun h1 : term445 = True => @lem5457905)). Qed.
Lemma lem5457908 : term445 = True.
Proof. exact (EQ_MP (@lem5457907) (@lem5457905)). Qed.
Lemma lem5457909 : term444 = True.
Proof. exact (TRANS (@lem5457904) (@lem5457908)). Qed.
Lemma lem5457910 : True = term444.
Proof. exact (SYM (@lem5457909)). Qed.
Lemma lem5457911 : term444.
Proof. exact (EQ_MP (@lem5457910) (@lem0)). Qed.
Lemma lem5457912 : term668.
Proof. exact (@lem5457901 (@lem5457911)). Qed.
Lemma lem5457914 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457915 : term444 = term445.
Proof. exact (@lem5457914 (NUMERAL 0) term120). Qed.
Lemma lem5457916 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457917 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457918 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457917 h1) (fun h1 : term445 = True => @lem5457916)). Qed.
Lemma lem5457919 : term445 = True.
Proof. exact (EQ_MP (@lem5457918) (@lem5457916)). Qed.
Lemma lem5457920 : term444 = True.
Proof. exact (TRANS (@lem5457915) (@lem5457919)). Qed.
Lemma lem5457921 : True = term444.
Proof. exact (SYM (@lem5457920)). Qed.
Lemma lem5457922 : term444.
Proof. exact (EQ_MP (@lem5457921) (@lem0)). Qed.
Lemma lem5457923 : term666 = term669.
Proof. exact (@lem5457912 (@lem5457922)). Qed.
Lemma lem5457925 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5457926 : term344 = term345.
Proof. exact (@lem5457925 term120 term120). Qed.
Lemma lem5457927 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5457928 : term347 = term120.
Proof. exact (EQ_MP (@lem5457927) (@lem940073)). Qed.
Lemma lem5457929 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5457930 : term345 = term272.
Proof. exact (MK_COMB (@lem5457929) (@lem5457928)). Qed.
Lemma lem5457931 : term344 = term272.
Proof. exact (TRANS (@lem5457926) (@lem5457930)). Qed.
Lemma lem5457933 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5457934 : term456 = term260.
Proof. exact (@lem5457933 term120). Qed.
Lemma lem5457935 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457936 : term670 = term664.
Proof. exact (MK_COMB (@lem5457935) (@lem5457934)). Qed.
Lemma lem5457937 : term669 = term444.
Proof. exact (MK_COMB (@lem5457936) (@lem5457931)). Qed.
Lemma lem5457939 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457940 : term444 = term445.
Proof. exact (@lem5457939 (NUMERAL 0) term120). Qed.
Lemma lem5457941 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457942 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457943 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457942 h1) (fun h1 : term445 = True => @lem5457941)). Qed.
Lemma lem5457944 : term445 = True.
Proof. exact (EQ_MP (@lem5457943) (@lem5457941)). Qed.
Lemma lem5457945 : term444 = True.
Proof. exact (TRANS (@lem5457940) (@lem5457944)). Qed.
Lemma lem5457946 : term669 = True.
Proof. exact (TRANS (@lem5457937) (@lem5457945)). Qed.
Lemma lem5457947 : term666 = True.
Proof. exact (TRANS (@lem5457923) (@lem5457946)). Qed.
Lemma lem5457948 : term444 = True.
Proof. exact (TRANS (@lem5457900) (@lem5457947)). Qed.
Lemma lem5457949 : term663 = True.
Proof. exact (TRANS (@lem5457891) (@lem5457948)). Qed.
Lemma lem5457950 : True = term663.
Proof. exact (SYM (@lem5457949)). Qed.
Lemma lem5457951 : term663.
Proof. exact (EQ_MP (@lem5457950) (@lem0)). Qed.
Lemma lem5457952 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term785 _70533 _70534 _70535.
Proof. exact (conj (@lem5457951) (@lem5457885 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457954 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5457955 (_70533 : int) (_70534 : int) (_70535 : int) : term786 _70533 _70534 _70535.
Proof. exact (@lem5457954 term272 (term418 _70533 _70534 _70535)). Qed.
Lemma lem5457956 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term787 _70533 _70534 _70535.
Proof. exact (@lem5457955 _70533 _70534 _70535 (@lem5457952 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457957 (_70533 : int) (_70534 : int) (_70535 : int) : (term788 _70533 _70534 _70535) = (term418 _70533 _70534 _70535).
Proof. exact (@lem1982733 (term418 _70533 _70534 _70535)). Qed.
Lemma lem5457958 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5457959 (_70533 : int) (_70534 : int) (_70535 : int) : (term789 _70533 _70534 _70535) = (term420 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5457958) (@lem5457957 _70533 _70534 _70535)). Qed.
Lemma lem5457960 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5457961 (_70533 : int) (_70534 : int) (_70535 : int) : (term787 _70533 _70534 _70535) = (term421 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5457959 _70533 _70534 _70535) (@lem5457960)). Qed.
Lemma lem5457962 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term421 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5457961 _70533 _70534 _70535) (@lem5457956 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5457964 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5457965 : term663 = term444.
Proof. exact (@lem5457964 term260 term272). Qed.
Lemma lem5457967 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457968 : term272 = term369.
Proof. exact (@lem5457967 term120). Qed.
Lemma lem5457970 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5457971 : term260 = term332.
Proof. exact (@lem5457970 (NUMERAL 0)). Qed.
Lemma lem5457972 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5457973 : term664 = term665.
Proof. exact (MK_COMB (@lem5457972) (@lem5457971)). Qed.
Lemma lem5457974 : term444 = term666.
Proof. exact (MK_COMB (@lem5457973) (@lem5457968)). Qed.
Lemma lem5457975 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5457977 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457978 : term444 = term445.
Proof. exact (@lem5457977 (NUMERAL 0) term120). Qed.
Lemma lem5457979 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457980 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457981 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457980 h1) (fun h1 : term445 = True => @lem5457979)). Qed.
Lemma lem5457982 : term445 = True.
Proof. exact (EQ_MP (@lem5457981) (@lem5457979)). Qed.
Lemma lem5457983 : term444 = True.
Proof. exact (TRANS (@lem5457978) (@lem5457982)). Qed.
Lemma lem5457984 : True = term444.
Proof. exact (SYM (@lem5457983)). Qed.
Lemma lem5457985 : term444.
Proof. exact (EQ_MP (@lem5457984) (@lem0)). Qed.
Lemma lem5457986 : term668.
Proof. exact (@lem5457975 (@lem5457985)). Qed.
Lemma lem5457988 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5457989 : term444 = term445.
Proof. exact (@lem5457988 (NUMERAL 0) term120). Qed.
Lemma lem5457990 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5457991 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5457992 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5457991 h1) (fun h1 : term445 = True => @lem5457990)). Qed.
Lemma lem5457993 : term445 = True.
Proof. exact (EQ_MP (@lem5457992) (@lem5457990)). Qed.
Lemma lem5457994 : term444 = True.
Proof. exact (TRANS (@lem5457989) (@lem5457993)). Qed.
Lemma lem5457995 : True = term444.
Proof. exact (SYM (@lem5457994)). Qed.
Lemma lem5457996 : term444.
Proof. exact (EQ_MP (@lem5457995) (@lem0)). Qed.
Lemma lem5457997 : term666 = term669.
Proof. exact (@lem5457986 (@lem5457996)). Qed.
Lemma lem5457999 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458000 : term344 = term345.
Proof. exact (@lem5457999 term120 term120). Qed.
Lemma lem5458001 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458002 : term347 = term120.
Proof. exact (EQ_MP (@lem5458001) (@lem940073)). Qed.
Lemma lem5458003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458004 : term345 = term272.
Proof. exact (MK_COMB (@lem5458003) (@lem5458002)). Qed.
Lemma lem5458005 : term344 = term272.
Proof. exact (TRANS (@lem5458000) (@lem5458004)). Qed.
Lemma lem5458007 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458008 : term456 = term260.
Proof. exact (@lem5458007 term120). Qed.
Lemma lem5458009 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5458010 : term670 = term664.
Proof. exact (MK_COMB (@lem5458009) (@lem5458008)). Qed.
Lemma lem5458011 : term669 = term444.
Proof. exact (MK_COMB (@lem5458010) (@lem5458005)). Qed.
Lemma lem5458013 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458014 : term444 = term445.
Proof. exact (@lem5458013 (NUMERAL 0) term120). Qed.
Lemma lem5458015 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458016 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458017 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458016 h1) (fun h1 : term445 = True => @lem5458015)). Qed.
Lemma lem5458018 : term445 = True.
Proof. exact (EQ_MP (@lem5458017) (@lem5458015)). Qed.
Lemma lem5458019 : term444 = True.
Proof. exact (TRANS (@lem5458014) (@lem5458018)). Qed.
Lemma lem5458020 : term669 = True.
Proof. exact (TRANS (@lem5458011) (@lem5458019)). Qed.
Lemma lem5458021 : term666 = True.
Proof. exact (TRANS (@lem5457997) (@lem5458020)). Qed.
Lemma lem5458022 : term444 = True.
Proof. exact (TRANS (@lem5457974) (@lem5458021)). Qed.
Lemma lem5458023 : term663 = True.
Proof. exact (TRANS (@lem5457965) (@lem5458022)). Qed.
Lemma lem5458024 : True = term663.
Proof. exact (SYM (@lem5458023)). Qed.
Lemma lem5458025 : term663.
Proof. exact (EQ_MP (@lem5458024) (@lem0)). Qed.
Lemma lem5458026 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term737 _70533 _70534 _70535.
Proof. exact (conj (@lem5458025) (@lem5457887 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458028 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5458029 (_70533 : int) (_70534 : int) (_70535 : int) : term738 _70533 _70534 _70535.
Proof. exact (@lem5458028 term272 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5458030 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term739 _70533 _70534 _70535.
Proof. exact (@lem5458029 _70533 _70534 _70535 (@lem5458026 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458031 (_70533 : int) (_70534 : int) (_70535 : int) : (term740 _70533 _70534 _70535) = (term396 _70533 _70534 _70535).
Proof. exact (@lem1982733 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5458032 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5458033 (_70533 : int) (_70534 : int) (_70535 : int) : (term741 _70533 _70534 _70535) = (term398 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5458032) (@lem5458031 _70533 _70534 _70535)). Qed.
Lemma lem5458034 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5458035 (_70533 : int) (_70534 : int) (_70535 : int) : (term739 _70533 _70534 _70535) = (term399 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5458033 _70533 _70534 _70535) (@lem5458034)). Qed.
Lemma lem5458036 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term399 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5458035 _70533 _70534 _70535) (@lem5458030 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458037 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term790 _70533 _70534 _70535.
Proof. exact (conj (@lem5458036 _70532 _70533 _70534 _70535 h1) (@lem5457962 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458039 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5458040 (_70533 : int) (_70534 : int) (_70535 : int) : term791 _70533 _70534 _70535.
Proof. exact (@lem5458039 (term396 _70533 _70534 _70535) (term418 _70533 _70534 _70535)). Qed.
Lemma lem5458041 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term792 _70533 _70534 _70535.
Proof. exact (@lem5458040 _70533 _70534 _70535 (@lem5458037 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458042 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = (term794 _70533 _70534 _70535).
Proof. exact (@lem1982753 (term360 _70533) (real_of_int _70533) (term395 _70534 _70535) (term404 _70534 _70535)). Qed.
Lemma lem5458043 (_70533 : int) : (term688 _70533) = (term689 _70533).
Proof. exact (@lem1982713 term335 (real_of_int _70533)). Qed.
Lemma lem5458045 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458046 : term272 = term369.
Proof. exact (@lem5458045 term120). Qed.
Lemma lem5458048 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458049 : term335 = term336.
Proof. exact (@lem5458048 term120). Qed.
Lemma lem5458050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458051 : term690 = term691.
Proof. exact (MK_COMB (@lem5458050) (@lem5458049)). Qed.
Lemma lem5458052 : term692 = term693.
Proof. exact (MK_COMB (@lem5458051) (@lem5458046)). Qed.
Lemma lem5458053 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5458055 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458056 : term444 = term445.
Proof. exact (@lem5458055 (NUMERAL 0) term120). Qed.
Lemma lem5458057 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458058 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458059 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458058 h1) (fun h1 : term445 = True => @lem5458057)). Qed.
Lemma lem5458060 : term445 = True.
Proof. exact (EQ_MP (@lem5458059) (@lem5458057)). Qed.
Lemma lem5458061 : term444 = True.
Proof. exact (TRANS (@lem5458056) (@lem5458060)). Qed.
Lemma lem5458062 : True = term444.
Proof. exact (SYM (@lem5458061)). Qed.
Lemma lem5458063 : term444.
Proof. exact (EQ_MP (@lem5458062) (@lem0)). Qed.
Lemma lem5458064 : term695.
Proof. exact (@lem5458053 (@lem5458063)). Qed.
Lemma lem5458066 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458067 : term444 = term445.
Proof. exact (@lem5458066 (NUMERAL 0) term120). Qed.
Lemma lem5458068 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458069 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458070 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458069 h1) (fun h1 : term445 = True => @lem5458068)). Qed.
Lemma lem5458071 : term445 = True.
Proof. exact (EQ_MP (@lem5458070) (@lem5458068)). Qed.
Lemma lem5458072 : term444 = True.
Proof. exact (TRANS (@lem5458067) (@lem5458071)). Qed.
Lemma lem5458073 : True = term444.
Proof. exact (SYM (@lem5458072)). Qed.
Lemma lem5458074 : term444.
Proof. exact (EQ_MP (@lem5458073) (@lem0)). Qed.
Lemma lem5458075 : term696.
Proof. exact (@lem5458064 (@lem5458074)). Qed.
Lemma lem5458077 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458078 : term444 = term445.
Proof. exact (@lem5458077 (NUMERAL 0) term120). Qed.
Lemma lem5458079 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458080 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458081 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458080 h1) (fun h1 : term445 = True => @lem5458079)). Qed.
Lemma lem5458082 : term445 = True.
Proof. exact (EQ_MP (@lem5458081) (@lem5458079)). Qed.
Lemma lem5458083 : term444 = True.
Proof. exact (TRANS (@lem5458078) (@lem5458082)). Qed.
Lemma lem5458084 : True = term444.
Proof. exact (SYM (@lem5458083)). Qed.
Lemma lem5458085 : term444.
Proof. exact (EQ_MP (@lem5458084) (@lem0)). Qed.
Lemma lem5458086 : term697.
Proof. exact (@lem5458075 (@lem5458085)). Qed.
Lemma lem5458088 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458089 : term344 = term345.
Proof. exact (@lem5458088 term120 term120). Qed.
Lemma lem5458090 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458091 : term347 = term120.
Proof. exact (EQ_MP (@lem5458090) (@lem940073)). Qed.
Lemma lem5458092 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458093 : term345 = term272.
Proof. exact (MK_COMB (@lem5458092) (@lem5458091)). Qed.
Lemma lem5458094 : term344 = term272.
Proof. exact (TRANS (@lem5458089) (@lem5458093)). Qed.
Lemma lem5458096 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5458097 : term370 = term375.
Proof. exact (@lem5458096 term120 term120). Qed.
Lemma lem5458098 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458099 : term347 = term120.
Proof. exact (EQ_MP (@lem5458098) (@lem940073)). Qed.
Lemma lem5458100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458101 : term345 = term272.
Proof. exact (MK_COMB (@lem5458100) (@lem5458099)). Qed.
Lemma lem5458102 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5458103 : term375 = term335.
Proof. exact (MK_COMB (@lem5458102) (@lem5458101)). Qed.
Lemma lem5458104 : term370 = term335.
Proof. exact (TRANS (@lem5458097) (@lem5458103)). Qed.
Lemma lem5458105 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458106 : term698 = term690.
Proof. exact (MK_COMB (@lem5458105) (@lem5458104)). Qed.
Lemma lem5458107 : term699 = term692.
Proof. exact (MK_COMB (@lem5458106) (@lem5458094)). Qed.
Lemma lem5458109 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5458110 : term692 = term260.
Proof. exact (@lem5458109 term120). Qed.
Lemma lem5458111 : term699 = term260.
Proof. exact (TRANS (@lem5458107) (@lem5458110)). Qed.
Lemma lem5458112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458113 : term701 = term454.
Proof. exact (MK_COMB (@lem5458112) (@lem5458111)). Qed.
Lemma lem5458114 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5458115 : term702 = term456.
Proof. exact (MK_COMB (@lem5458113) (@lem5458114)). Qed.
Lemma lem5458117 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458118 : term456 = term260.
Proof. exact (@lem5458117 term120). Qed.
Lemma lem5458119 : term702 = term260.
Proof. exact (TRANS (@lem5458115) (@lem5458118)). Qed.
Lemma lem5458121 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458122 : term344 = term345.
Proof. exact (@lem5458121 term120 term120). Qed.
Lemma lem5458123 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458124 : term347 = term120.
Proof. exact (EQ_MP (@lem5458123) (@lem940073)). Qed.
Lemma lem5458125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458126 : term345 = term272.
Proof. exact (MK_COMB (@lem5458125) (@lem5458124)). Qed.
Lemma lem5458127 : term344 = term272.
Proof. exact (TRANS (@lem5458122) (@lem5458126)). Qed.
Lemma lem5458128 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5458129 : term458 = term456.
Proof. exact (MK_COMB (@lem5458128) (@lem5458127)). Qed.
Lemma lem5458131 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458132 : term456 = term260.
Proof. exact (@lem5458131 term120). Qed.
Lemma lem5458133 : term458 = term260.
Proof. exact (TRANS (@lem5458129) (@lem5458132)). Qed.
Lemma lem5458134 : term260 = term458.
Proof. exact (SYM (@lem5458133)). Qed.
Lemma lem5458135 : term702 = term458.
Proof. exact (TRANS (@lem5458119) (@lem5458134)). Qed.
Lemma lem5458136 : term693 = term332.
Proof. exact (@lem5458086 (@lem5458135)). Qed.
Lemma lem5458137 : term692 = term332.
Proof. exact (TRANS (@lem5458052) (@lem5458136)). Qed.
Lemma lem5458139 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5458140 : term332 = term260.
Proof. exact (@lem5458139 term260). Qed.
Lemma lem5458141 : term692 = term260.
Proof. exact (TRANS (@lem5458137) (@lem5458140)). Qed.
Lemma lem5458142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458143 : term703 = term454.
Proof. exact (MK_COMB (@lem5458142) (@lem5458141)). Qed.
Lemma lem5458144 (_70533 : int) : (real_of_int _70533) = (real_of_int _70533).
Proof. exact (eq_refl (real_of_int _70533)). Qed.
Lemma lem5458145 (_70533 : int) : (term689 _70533) = (term704 _70533).
Proof. exact (MK_COMB (@lem5458143) (@lem5458144 _70533)). Qed.
Lemma lem5458146 (_70533 : int) : (term688 _70533) = (term704 _70533).
Proof. exact (TRANS (@lem5458043 _70533) (@lem5458145 _70533)). Qed.
Lemma lem5458147 (_70533 : int) : (term704 _70533) = term260.
Proof. exact (@lem1982719 (real_of_int _70533)). Qed.
Lemma lem5458148 (_70533 : int) : (term688 _70533) = term260.
Proof. exact (TRANS (@lem5458146 _70533) (@lem5458147 _70533)). Qed.
Lemma lem5458149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458150 (_70533 : int) : (term705 _70533) = term706.
Proof. exact (MK_COMB (@lem5458149) (@lem5458148 _70533)). Qed.
Lemma lem5458151 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = (term760 _70534 _70535).
Proof. exact (@lem1982753 (term360 _70534) (real_of_int _70534) (term749 _70535) (term360 _70535)). Qed.
Lemma lem5458152 (_70534 : int) : (term688 _70534) = (term689 _70534).
Proof. exact (@lem1982713 term335 (real_of_int _70534)). Qed.
Lemma lem5458154 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458155 : term272 = term369.
Proof. exact (@lem5458154 term120). Qed.
Lemma lem5458157 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458158 : term335 = term336.
Proof. exact (@lem5458157 term120). Qed.
Lemma lem5458159 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458160 : term690 = term691.
Proof. exact (MK_COMB (@lem5458159) (@lem5458158)). Qed.
Lemma lem5458161 : term692 = term693.
Proof. exact (MK_COMB (@lem5458160) (@lem5458155)). Qed.
Lemma lem5458162 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5458164 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458165 : term444 = term445.
Proof. exact (@lem5458164 (NUMERAL 0) term120). Qed.
Lemma lem5458166 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458167 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458168 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458167 h1) (fun h1 : term445 = True => @lem5458166)). Qed.
Lemma lem5458169 : term445 = True.
Proof. exact (EQ_MP (@lem5458168) (@lem5458166)). Qed.
Lemma lem5458170 : term444 = True.
Proof. exact (TRANS (@lem5458165) (@lem5458169)). Qed.
Lemma lem5458171 : True = term444.
Proof. exact (SYM (@lem5458170)). Qed.
Lemma lem5458172 : term444.
Proof. exact (EQ_MP (@lem5458171) (@lem0)). Qed.
Lemma lem5458173 : term695.
Proof. exact (@lem5458162 (@lem5458172)). Qed.
Lemma lem5458175 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458176 : term444 = term445.
Proof. exact (@lem5458175 (NUMERAL 0) term120). Qed.
Lemma lem5458177 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458178 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458179 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458178 h1) (fun h1 : term445 = True => @lem5458177)). Qed.
Lemma lem5458180 : term445 = True.
Proof. exact (EQ_MP (@lem5458179) (@lem5458177)). Qed.
Lemma lem5458181 : term444 = True.
Proof. exact (TRANS (@lem5458176) (@lem5458180)). Qed.
Lemma lem5458182 : True = term444.
Proof. exact (SYM (@lem5458181)). Qed.
Lemma lem5458183 : term444.
Proof. exact (EQ_MP (@lem5458182) (@lem0)). Qed.
Lemma lem5458184 : term696.
Proof. exact (@lem5458173 (@lem5458183)). Qed.
Lemma lem5458186 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458187 : term444 = term445.
Proof. exact (@lem5458186 (NUMERAL 0) term120). Qed.
Lemma lem5458188 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458189 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458190 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458189 h1) (fun h1 : term445 = True => @lem5458188)). Qed.
Lemma lem5458191 : term445 = True.
Proof. exact (EQ_MP (@lem5458190) (@lem5458188)). Qed.
Lemma lem5458192 : term444 = True.
Proof. exact (TRANS (@lem5458187) (@lem5458191)). Qed.
Lemma lem5458193 : True = term444.
Proof. exact (SYM (@lem5458192)). Qed.
Lemma lem5458194 : term444.
Proof. exact (EQ_MP (@lem5458193) (@lem0)). Qed.
Lemma lem5458195 : term697.
Proof. exact (@lem5458184 (@lem5458194)). Qed.
Lemma lem5458197 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458198 : term344 = term345.
Proof. exact (@lem5458197 term120 term120). Qed.
Lemma lem5458199 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458200 : term347 = term120.
Proof. exact (EQ_MP (@lem5458199) (@lem940073)). Qed.
Lemma lem5458201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458202 : term345 = term272.
Proof. exact (MK_COMB (@lem5458201) (@lem5458200)). Qed.
Lemma lem5458203 : term344 = term272.
Proof. exact (TRANS (@lem5458198) (@lem5458202)). Qed.
Lemma lem5458205 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5458206 : term370 = term375.
Proof. exact (@lem5458205 term120 term120). Qed.
Lemma lem5458207 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458208 : term347 = term120.
Proof. exact (EQ_MP (@lem5458207) (@lem940073)). Qed.
Lemma lem5458209 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458210 : term345 = term272.
Proof. exact (MK_COMB (@lem5458209) (@lem5458208)). Qed.
Lemma lem5458211 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5458212 : term375 = term335.
Proof. exact (MK_COMB (@lem5458211) (@lem5458210)). Qed.
Lemma lem5458213 : term370 = term335.
Proof. exact (TRANS (@lem5458206) (@lem5458212)). Qed.
Lemma lem5458214 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458215 : term698 = term690.
Proof. exact (MK_COMB (@lem5458214) (@lem5458213)). Qed.
Lemma lem5458216 : term699 = term692.
Proof. exact (MK_COMB (@lem5458215) (@lem5458203)). Qed.
Lemma lem5458218 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5458219 : term692 = term260.
Proof. exact (@lem5458218 term120). Qed.
Lemma lem5458220 : term699 = term260.
Proof. exact (TRANS (@lem5458216) (@lem5458219)). Qed.
Lemma lem5458221 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458222 : term701 = term454.
Proof. exact (MK_COMB (@lem5458221) (@lem5458220)). Qed.
Lemma lem5458223 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5458224 : term702 = term456.
Proof. exact (MK_COMB (@lem5458222) (@lem5458223)). Qed.
Lemma lem5458226 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458227 : term456 = term260.
Proof. exact (@lem5458226 term120). Qed.
Lemma lem5458228 : term702 = term260.
Proof. exact (TRANS (@lem5458224) (@lem5458227)). Qed.
Lemma lem5458230 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458231 : term344 = term345.
Proof. exact (@lem5458230 term120 term120). Qed.
Lemma lem5458232 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458233 : term347 = term120.
Proof. exact (EQ_MP (@lem5458232) (@lem940073)). Qed.
Lemma lem5458234 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458235 : term345 = term272.
Proof. exact (MK_COMB (@lem5458234) (@lem5458233)). Qed.
Lemma lem5458236 : term344 = term272.
Proof. exact (TRANS (@lem5458231) (@lem5458235)). Qed.
Lemma lem5458237 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5458238 : term458 = term456.
Proof. exact (MK_COMB (@lem5458237) (@lem5458236)). Qed.
Lemma lem5458240 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458241 : term456 = term260.
Proof. exact (@lem5458240 term120). Qed.
Lemma lem5458242 : term458 = term260.
Proof. exact (TRANS (@lem5458238) (@lem5458241)). Qed.
Lemma lem5458243 : term260 = term458.
Proof. exact (SYM (@lem5458242)). Qed.
Lemma lem5458244 : term702 = term458.
Proof. exact (TRANS (@lem5458228) (@lem5458243)). Qed.
Lemma lem5458245 : term693 = term332.
Proof. exact (@lem5458195 (@lem5458244)). Qed.
Lemma lem5458246 : term692 = term332.
Proof. exact (TRANS (@lem5458161) (@lem5458245)). Qed.
Lemma lem5458248 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5458249 : term332 = term260.
Proof. exact (@lem5458248 term260). Qed.
Lemma lem5458250 : term692 = term260.
Proof. exact (TRANS (@lem5458246) (@lem5458249)). Qed.
Lemma lem5458251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458252 : term703 = term454.
Proof. exact (MK_COMB (@lem5458251) (@lem5458250)). Qed.
Lemma lem5458253 (_70534 : int) : (real_of_int _70534) = (real_of_int _70534).
Proof. exact (eq_refl (real_of_int _70534)). Qed.
Lemma lem5458254 (_70534 : int) : (term689 _70534) = (term704 _70534).
Proof. exact (MK_COMB (@lem5458252) (@lem5458253 _70534)). Qed.
Lemma lem5458255 (_70534 : int) : (term688 _70534) = (term704 _70534).
Proof. exact (TRANS (@lem5458152 _70534) (@lem5458254 _70534)). Qed.
Lemma lem5458256 (_70534 : int) : (term704 _70534) = term260.
Proof. exact (@lem1982719 (real_of_int _70534)). Qed.
Lemma lem5458257 (_70534 : int) : (term688 _70534) = term260.
Proof. exact (TRANS (@lem5458255 _70534) (@lem5458256 _70534)). Qed.
Lemma lem5458258 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458259 (_70534 : int) : (term705 _70534) = term706.
Proof. exact (MK_COMB (@lem5458258) (@lem5458257 _70534)). Qed.
Lemma lem5458260 (_70535 : int) : (term761 _70535) = (term708 _70535).
Proof. exact (@lem1982759 (real_of_int _70535) (term360 _70535) term335). Qed.
Lemma lem5458261 (_70535 : int) : (term709 _70535) = (term689 _70535).
Proof. exact (@lem1982715 term335 (real_of_int _70535)). Qed.
Lemma lem5458263 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458264 : term272 = term369.
Proof. exact (@lem5458263 term120). Qed.
Lemma lem5458266 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458267 : term335 = term336.
Proof. exact (@lem5458266 term120). Qed.
Lemma lem5458268 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458269 : term690 = term691.
Proof. exact (MK_COMB (@lem5458268) (@lem5458267)). Qed.
Lemma lem5458270 : term692 = term693.
Proof. exact (MK_COMB (@lem5458269) (@lem5458264)). Qed.
Lemma lem5458271 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5458273 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458274 : term444 = term445.
Proof. exact (@lem5458273 (NUMERAL 0) term120). Qed.
Lemma lem5458275 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458276 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458277 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458276 h1) (fun h1 : term445 = True => @lem5458275)). Qed.
Lemma lem5458278 : term445 = True.
Proof. exact (EQ_MP (@lem5458277) (@lem5458275)). Qed.
Lemma lem5458279 : term444 = True.
Proof. exact (TRANS (@lem5458274) (@lem5458278)). Qed.
Lemma lem5458280 : True = term444.
Proof. exact (SYM (@lem5458279)). Qed.
Lemma lem5458281 : term444.
Proof. exact (EQ_MP (@lem5458280) (@lem0)). Qed.
Lemma lem5458282 : term695.
Proof. exact (@lem5458271 (@lem5458281)). Qed.
Lemma lem5458284 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458285 : term444 = term445.
Proof. exact (@lem5458284 (NUMERAL 0) term120). Qed.
Lemma lem5458286 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458287 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458288 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458287 h1) (fun h1 : term445 = True => @lem5458286)). Qed.
Lemma lem5458289 : term445 = True.
Proof. exact (EQ_MP (@lem5458288) (@lem5458286)). Qed.
Lemma lem5458290 : term444 = True.
Proof. exact (TRANS (@lem5458285) (@lem5458289)). Qed.
Lemma lem5458291 : True = term444.
Proof. exact (SYM (@lem5458290)). Qed.
Lemma lem5458292 : term444.
Proof. exact (EQ_MP (@lem5458291) (@lem0)). Qed.
Lemma lem5458293 : term696.
Proof. exact (@lem5458282 (@lem5458292)). Qed.
Lemma lem5458295 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458296 : term444 = term445.
Proof. exact (@lem5458295 (NUMERAL 0) term120). Qed.
Lemma lem5458297 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458298 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458299 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458298 h1) (fun h1 : term445 = True => @lem5458297)). Qed.
Lemma lem5458300 : term445 = True.
Proof. exact (EQ_MP (@lem5458299) (@lem5458297)). Qed.
Lemma lem5458301 : term444 = True.
Proof. exact (TRANS (@lem5458296) (@lem5458300)). Qed.
Lemma lem5458302 : True = term444.
Proof. exact (SYM (@lem5458301)). Qed.
Lemma lem5458303 : term444.
Proof. exact (EQ_MP (@lem5458302) (@lem0)). Qed.
Lemma lem5458304 : term697.
Proof. exact (@lem5458293 (@lem5458303)). Qed.
Lemma lem5458306 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458307 : term344 = term345.
Proof. exact (@lem5458306 term120 term120). Qed.
Lemma lem5458308 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458309 : term347 = term120.
Proof. exact (EQ_MP (@lem5458308) (@lem940073)). Qed.
Lemma lem5458310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458311 : term345 = term272.
Proof. exact (MK_COMB (@lem5458310) (@lem5458309)). Qed.
Lemma lem5458312 : term344 = term272.
Proof. exact (TRANS (@lem5458307) (@lem5458311)). Qed.
Lemma lem5458314 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5458315 : term370 = term375.
Proof. exact (@lem5458314 term120 term120). Qed.
Lemma lem5458316 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458317 : term347 = term120.
Proof. exact (EQ_MP (@lem5458316) (@lem940073)). Qed.
Lemma lem5458318 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458319 : term345 = term272.
Proof. exact (MK_COMB (@lem5458318) (@lem5458317)). Qed.
Lemma lem5458320 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5458321 : term375 = term335.
Proof. exact (MK_COMB (@lem5458320) (@lem5458319)). Qed.
Lemma lem5458322 : term370 = term335.
Proof. exact (TRANS (@lem5458315) (@lem5458321)). Qed.
Lemma lem5458323 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458324 : term698 = term690.
Proof. exact (MK_COMB (@lem5458323) (@lem5458322)). Qed.
Lemma lem5458325 : term699 = term692.
Proof. exact (MK_COMB (@lem5458324) (@lem5458312)). Qed.
Lemma lem5458327 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5458328 : term692 = term260.
Proof. exact (@lem5458327 term120). Qed.
Lemma lem5458329 : term699 = term260.
Proof. exact (TRANS (@lem5458325) (@lem5458328)). Qed.
Lemma lem5458330 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458331 : term701 = term454.
Proof. exact (MK_COMB (@lem5458330) (@lem5458329)). Qed.
Lemma lem5458332 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5458333 : term702 = term456.
Proof. exact (MK_COMB (@lem5458331) (@lem5458332)). Qed.
Lemma lem5458335 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458336 : term456 = term260.
Proof. exact (@lem5458335 term120). Qed.
Lemma lem5458337 : term702 = term260.
Proof. exact (TRANS (@lem5458333) (@lem5458336)). Qed.
Lemma lem5458339 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458340 : term344 = term345.
Proof. exact (@lem5458339 term120 term120). Qed.
Lemma lem5458341 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458342 : term347 = term120.
Proof. exact (EQ_MP (@lem5458341) (@lem940073)). Qed.
Lemma lem5458343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458344 : term345 = term272.
Proof. exact (MK_COMB (@lem5458343) (@lem5458342)). Qed.
Lemma lem5458345 : term344 = term272.
Proof. exact (TRANS (@lem5458340) (@lem5458344)). Qed.
Lemma lem5458346 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5458347 : term458 = term456.
Proof. exact (MK_COMB (@lem5458346) (@lem5458345)). Qed.
Lemma lem5458349 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458350 : term456 = term260.
Proof. exact (@lem5458349 term120). Qed.
Lemma lem5458351 : term458 = term260.
Proof. exact (TRANS (@lem5458347) (@lem5458350)). Qed.
Lemma lem5458352 : term260 = term458.
Proof. exact (SYM (@lem5458351)). Qed.
Lemma lem5458353 : term702 = term458.
Proof. exact (TRANS (@lem5458337) (@lem5458352)). Qed.
Lemma lem5458354 : term693 = term332.
Proof. exact (@lem5458304 (@lem5458353)). Qed.
Lemma lem5458355 : term692 = term332.
Proof. exact (TRANS (@lem5458270) (@lem5458354)). Qed.
Lemma lem5458357 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5458358 : term332 = term260.
Proof. exact (@lem5458357 term260). Qed.
Lemma lem5458359 : term692 = term260.
Proof. exact (TRANS (@lem5458355) (@lem5458358)). Qed.
Lemma lem5458360 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458361 : term703 = term454.
Proof. exact (MK_COMB (@lem5458360) (@lem5458359)). Qed.
Lemma lem5458362 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5458363 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5458361) (@lem5458362 _70535)). Qed.
Lemma lem5458364 (_70535 : int) : (term709 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5458261 _70535) (@lem5458363 _70535)). Qed.
Lemma lem5458365 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5458366 (_70535 : int) : (term709 _70535) = term260.
Proof. exact (TRANS (@lem5458364 _70535) (@lem5458365 _70535)). Qed.
Lemma lem5458367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458368 (_70535 : int) : (term710 _70535) = term706.
Proof. exact (MK_COMB (@lem5458367) (@lem5458366 _70535)). Qed.
Lemma lem5458369 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5458370 (_70535 : int) : (term708 _70535) = term711.
Proof. exact (MK_COMB (@lem5458368 _70535) (@lem5458369)). Qed.
Lemma lem5458371 (_70535 : int) : (term761 _70535) = term711.
Proof. exact (TRANS (@lem5458260 _70535) (@lem5458370 _70535)). Qed.
Lemma lem5458372 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5458373 (_70535 : int) : (term761 _70535) = term335.
Proof. exact (TRANS (@lem5458371 _70535) (@lem5458372)). Qed.
Lemma lem5458374 (_70534 : int) (_70535 : int) : (term760 _70534 _70535) = term711.
Proof. exact (MK_COMB (@lem5458259 _70534) (@lem5458373 _70535)). Qed.
Lemma lem5458375 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = term711.
Proof. exact (TRANS (@lem5458151 _70534 _70535) (@lem5458374 _70534 _70535)). Qed.
Lemma lem5458376 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5458377 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = term335.
Proof. exact (TRANS (@lem5458375 _70534 _70535) (@lem5458376)). Qed.
Lemma lem5458378 (_70533 : int) (_70534 : int) (_70535 : int) : (term794 _70533 _70534 _70535) = term711.
Proof. exact (MK_COMB (@lem5458150 _70533) (@lem5458377 _70534 _70535)). Qed.
Lemma lem5458379 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = term711.
Proof. exact (TRANS (@lem5458042 _70533 _70534 _70535) (@lem5458378 _70533 _70534 _70535)). Qed.
Lemma lem5458380 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5458381 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = term335.
Proof. exact (TRANS (@lem5458379 _70533 _70534 _70535) (@lem5458380)). Qed.
Lemma lem5458382 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5458383 (_70533 : int) (_70534 : int) (_70535 : int) : (term795 _70533 _70534 _70535) = term713.
Proof. exact (MK_COMB (@lem5458382) (@lem5458381 _70533 _70534 _70535)). Qed.
Lemma lem5458384 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5458385 (_70533 : int) (_70534 : int) (_70535 : int) : (term792 _70533 _70534 _70535) = term714.
Proof. exact (MK_COMB (@lem5458383 _70533 _70534 _70535) (@lem5458384)). Qed.
Lemma lem5458386 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : term714.
Proof. exact (EQ_MP (@lem5458385 _70533 _70534 _70535) (@lem5458041 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458388 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5458389 : term714 = term715.
Proof. exact (@lem5458388 term260 term335). Qed.
Lemma lem5458391 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458392 : term335 = term336.
Proof. exact (@lem5458391 term120). Qed.
Lemma lem5458394 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458395 : term260 = term332.
Proof. exact (@lem5458394 (NUMERAL 0)). Qed.
Lemma lem5458396 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5458397 : term262 = term716.
Proof. exact (MK_COMB (@lem5458396) (@lem5458395)). Qed.
Lemma lem5458398 : term715 = term717.
Proof. exact (MK_COMB (@lem5458397) (@lem5458392)). Qed.
Lemma lem5458399 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5458401 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458402 : term444 = term445.
Proof. exact (@lem5458401 (NUMERAL 0) term120). Qed.
Lemma lem5458403 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458404 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458405 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458404 h1) (fun h1 : term445 = True => @lem5458403)). Qed.
Lemma lem5458406 : term445 = True.
Proof. exact (EQ_MP (@lem5458405) (@lem5458403)). Qed.
Lemma lem5458407 : term444 = True.
Proof. exact (TRANS (@lem5458402) (@lem5458406)). Qed.
Lemma lem5458408 : True = term444.
Proof. exact (SYM (@lem5458407)). Qed.
Lemma lem5458409 : term444.
Proof. exact (EQ_MP (@lem5458408) (@lem0)). Qed.
Lemma lem5458410 : term719.
Proof. exact (@lem5458399 (@lem5458409)). Qed.
Lemma lem5458412 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458413 : term444 = term445.
Proof. exact (@lem5458412 (NUMERAL 0) term120). Qed.
Lemma lem5458414 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458415 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458416 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458415 h1) (fun h1 : term445 = True => @lem5458414)). Qed.
Lemma lem5458417 : term445 = True.
Proof. exact (EQ_MP (@lem5458416) (@lem5458414)). Qed.
Lemma lem5458418 : term444 = True.
Proof. exact (TRANS (@lem5458413) (@lem5458417)). Qed.
Lemma lem5458419 : True = term444.
Proof. exact (SYM (@lem5458418)). Qed.
Lemma lem5458420 : term444.
Proof. exact (EQ_MP (@lem5458419) (@lem0)). Qed.
Lemma lem5458421 : term717 = term720.
Proof. exact (@lem5458410 (@lem5458420)). Qed.
Lemma lem5458423 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5458424 : term370 = term375.
Proof. exact (@lem5458423 term120 term120). Qed.
Lemma lem5458425 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458426 : term347 = term120.
Proof. exact (EQ_MP (@lem5458425) (@lem940073)). Qed.
Lemma lem5458427 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458428 : term345 = term272.
Proof. exact (MK_COMB (@lem5458427) (@lem5458426)). Qed.
Lemma lem5458429 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5458430 : term375 = term335.
Proof. exact (MK_COMB (@lem5458429) (@lem5458428)). Qed.
Lemma lem5458431 : term370 = term335.
Proof. exact (TRANS (@lem5458424) (@lem5458430)). Qed.
Lemma lem5458433 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458434 : term456 = term260.
Proof. exact (@lem5458433 term120). Qed.
Lemma lem5458435 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5458436 : term721 = term262.
Proof. exact (MK_COMB (@lem5458435) (@lem5458434)). Qed.
Lemma lem5458437 : term720 = term715.
Proof. exact (MK_COMB (@lem5458436) (@lem5458431)). Qed.
Lemma lem5458439 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5458440 : term715 = term724.
Proof. exact (@lem5458439 (NUMERAL 0) term120). Qed.
Lemma lem5458441 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458442 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5458443 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458442 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5458441)). Qed.
Lemma lem5458444 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5458443) (@lem5458441)). Qed.
Lemma lem5458445 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5458446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5458447 : term725 = (and True).
Proof. exact (MK_COMB (@lem5458446) (@lem5458445)). Qed.
Lemma lem5458448 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5458447) (@lem5458444)). Qed.
Lemma lem5458450 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5458451 : term724 = False.
Proof. exact (TRANS (@lem5458448) (@lem5458450)). Qed.
Lemma lem5458452 : term715 = False.
Proof. exact (TRANS (@lem5458440) (@lem5458451)). Qed.
Lemma lem5458453 : term720 = False.
Proof. exact (TRANS (@lem5458437) (@lem5458452)). Qed.
Lemma lem5458454 : term717 = False.
Proof. exact (TRANS (@lem5458421) (@lem5458453)). Qed.
Lemma lem5458455 : term715 = False.
Proof. exact (TRANS (@lem5458398) (@lem5458454)). Qed.
Lemma lem5458456 : term714 = False.
Proof. exact (TRANS (@lem5458389) (@lem5458455)). Qed.
Lemma lem5458457 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term798 _70532 _70533 _70534 _70535) : False.
Proof. exact (EQ_MP (@lem5458456) (@lem5458386 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458458 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term799 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5458459 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term638 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458458 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458461 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term607 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458459 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458463 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term576 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458461 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458465 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term545 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458463 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458467 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term514 _70532 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458465 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458469 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term489 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458467 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458470 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term428 _70532 _70533 _70534 _70535.
Proof. exact (proj1 (@lem5458467 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458471 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term421 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458470 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458473 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term399 _70533 _70534 _70535.
Proof. exact (proj2 (@lem5458469 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458476 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5458477 : term663 = term444.
Proof. exact (@lem5458476 term260 term272). Qed.
Lemma lem5458479 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458480 : term272 = term369.
Proof. exact (@lem5458479 term120). Qed.
Lemma lem5458482 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458483 : term260 = term332.
Proof. exact (@lem5458482 (NUMERAL 0)). Qed.
Lemma lem5458484 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5458485 : term664 = term665.
Proof. exact (MK_COMB (@lem5458484) (@lem5458483)). Qed.
Lemma lem5458486 : term444 = term666.
Proof. exact (MK_COMB (@lem5458485) (@lem5458480)). Qed.
Lemma lem5458487 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5458489 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458490 : term444 = term445.
Proof. exact (@lem5458489 (NUMERAL 0) term120). Qed.
Lemma lem5458491 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458492 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458493 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458492 h1) (fun h1 : term445 = True => @lem5458491)). Qed.
Lemma lem5458494 : term445 = True.
Proof. exact (EQ_MP (@lem5458493) (@lem5458491)). Qed.
Lemma lem5458495 : term444 = True.
Proof. exact (TRANS (@lem5458490) (@lem5458494)). Qed.
Lemma lem5458496 : True = term444.
Proof. exact (SYM (@lem5458495)). Qed.
Lemma lem5458497 : term444.
Proof. exact (EQ_MP (@lem5458496) (@lem0)). Qed.
Lemma lem5458498 : term668.
Proof. exact (@lem5458487 (@lem5458497)). Qed.
Lemma lem5458500 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458501 : term444 = term445.
Proof. exact (@lem5458500 (NUMERAL 0) term120). Qed.
Lemma lem5458502 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458503 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458504 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458503 h1) (fun h1 : term445 = True => @lem5458502)). Qed.
Lemma lem5458505 : term445 = True.
Proof. exact (EQ_MP (@lem5458504) (@lem5458502)). Qed.
Lemma lem5458506 : term444 = True.
Proof. exact (TRANS (@lem5458501) (@lem5458505)). Qed.
Lemma lem5458507 : True = term444.
Proof. exact (SYM (@lem5458506)). Qed.
Lemma lem5458508 : term444.
Proof. exact (EQ_MP (@lem5458507) (@lem0)). Qed.
Lemma lem5458509 : term666 = term669.
Proof. exact (@lem5458498 (@lem5458508)). Qed.
Lemma lem5458511 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458512 : term344 = term345.
Proof. exact (@lem5458511 term120 term120). Qed.
Lemma lem5458513 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458514 : term347 = term120.
Proof. exact (EQ_MP (@lem5458513) (@lem940073)). Qed.
Lemma lem5458515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458516 : term345 = term272.
Proof. exact (MK_COMB (@lem5458515) (@lem5458514)). Qed.
Lemma lem5458517 : term344 = term272.
Proof. exact (TRANS (@lem5458512) (@lem5458516)). Qed.
Lemma lem5458519 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458520 : term456 = term260.
Proof. exact (@lem5458519 term120). Qed.
Lemma lem5458521 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5458522 : term670 = term664.
Proof. exact (MK_COMB (@lem5458521) (@lem5458520)). Qed.
Lemma lem5458523 : term669 = term444.
Proof. exact (MK_COMB (@lem5458522) (@lem5458517)). Qed.
Lemma lem5458525 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458526 : term444 = term445.
Proof. exact (@lem5458525 (NUMERAL 0) term120). Qed.
Lemma lem5458527 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458528 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458529 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458528 h1) (fun h1 : term445 = True => @lem5458527)). Qed.
Lemma lem5458530 : term445 = True.
Proof. exact (EQ_MP (@lem5458529) (@lem5458527)). Qed.
Lemma lem5458531 : term444 = True.
Proof. exact (TRANS (@lem5458526) (@lem5458530)). Qed.
Lemma lem5458532 : term669 = True.
Proof. exact (TRANS (@lem5458523) (@lem5458531)). Qed.
Lemma lem5458533 : term666 = True.
Proof. exact (TRANS (@lem5458509) (@lem5458532)). Qed.
Lemma lem5458534 : term444 = True.
Proof. exact (TRANS (@lem5458486) (@lem5458533)). Qed.
Lemma lem5458535 : term663 = True.
Proof. exact (TRANS (@lem5458477) (@lem5458534)). Qed.
Lemma lem5458536 : True = term663.
Proof. exact (SYM (@lem5458535)). Qed.
Lemma lem5458537 : term663.
Proof. exact (EQ_MP (@lem5458536) (@lem0)). Qed.
Lemma lem5458538 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term785 _70533 _70534 _70535.
Proof. exact (conj (@lem5458537) (@lem5458471 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458540 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5458541 (_70533 : int) (_70534 : int) (_70535 : int) : term786 _70533 _70534 _70535.
Proof. exact (@lem5458540 term272 (term418 _70533 _70534 _70535)). Qed.
Lemma lem5458542 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term787 _70533 _70534 _70535.
Proof. exact (@lem5458541 _70533 _70534 _70535 (@lem5458538 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458543 (_70533 : int) (_70534 : int) (_70535 : int) : (term788 _70533 _70534 _70535) = (term418 _70533 _70534 _70535).
Proof. exact (@lem1982733 (term418 _70533 _70534 _70535)). Qed.
Lemma lem5458544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5458545 (_70533 : int) (_70534 : int) (_70535 : int) : (term789 _70533 _70534 _70535) = (term420 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5458544) (@lem5458543 _70533 _70534 _70535)). Qed.
Lemma lem5458546 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5458547 (_70533 : int) (_70534 : int) (_70535 : int) : (term787 _70533 _70534 _70535) = (term421 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5458545 _70533 _70534 _70535) (@lem5458546)). Qed.
Lemma lem5458548 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term421 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5458547 _70533 _70534 _70535) (@lem5458542 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458550 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5458551 : term663 = term444.
Proof. exact (@lem5458550 term260 term272). Qed.
Lemma lem5458553 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458554 : term272 = term369.
Proof. exact (@lem5458553 term120). Qed.
Lemma lem5458556 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458557 : term260 = term332.
Proof. exact (@lem5458556 (NUMERAL 0)). Qed.
Lemma lem5458558 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5458559 : term664 = term665.
Proof. exact (MK_COMB (@lem5458558) (@lem5458557)). Qed.
Lemma lem5458560 : term444 = term666.
Proof. exact (MK_COMB (@lem5458559) (@lem5458554)). Qed.
Lemma lem5458561 : term667.
Proof. exact (@lem1980255 term260 term272 term272 term272). Qed.
Lemma lem5458563 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458564 : term444 = term445.
Proof. exact (@lem5458563 (NUMERAL 0) term120). Qed.
Lemma lem5458565 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458566 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458567 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458566 h1) (fun h1 : term445 = True => @lem5458565)). Qed.
Lemma lem5458568 : term445 = True.
Proof. exact (EQ_MP (@lem5458567) (@lem5458565)). Qed.
Lemma lem5458569 : term444 = True.
Proof. exact (TRANS (@lem5458564) (@lem5458568)). Qed.
Lemma lem5458570 : True = term444.
Proof. exact (SYM (@lem5458569)). Qed.
Lemma lem5458571 : term444.
Proof. exact (EQ_MP (@lem5458570) (@lem0)). Qed.
Lemma lem5458572 : term668.
Proof. exact (@lem5458561 (@lem5458571)). Qed.
Lemma lem5458574 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458575 : term444 = term445.
Proof. exact (@lem5458574 (NUMERAL 0) term120). Qed.
Lemma lem5458576 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458577 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458578 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458577 h1) (fun h1 : term445 = True => @lem5458576)). Qed.
Lemma lem5458579 : term445 = True.
Proof. exact (EQ_MP (@lem5458578) (@lem5458576)). Qed.
Lemma lem5458580 : term444 = True.
Proof. exact (TRANS (@lem5458575) (@lem5458579)). Qed.
Lemma lem5458581 : True = term444.
Proof. exact (SYM (@lem5458580)). Qed.
Lemma lem5458582 : term444.
Proof. exact (EQ_MP (@lem5458581) (@lem0)). Qed.
Lemma lem5458583 : term666 = term669.
Proof. exact (@lem5458572 (@lem5458582)). Qed.
Lemma lem5458585 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458586 : term344 = term345.
Proof. exact (@lem5458585 term120 term120). Qed.
Lemma lem5458587 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458588 : term347 = term120.
Proof. exact (EQ_MP (@lem5458587) (@lem940073)). Qed.
Lemma lem5458589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458590 : term345 = term272.
Proof. exact (MK_COMB (@lem5458589) (@lem5458588)). Qed.
Lemma lem5458591 : term344 = term272.
Proof. exact (TRANS (@lem5458586) (@lem5458590)). Qed.
Lemma lem5458593 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458594 : term456 = term260.
Proof. exact (@lem5458593 term120). Qed.
Lemma lem5458595 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5458596 : term670 = term664.
Proof. exact (MK_COMB (@lem5458595) (@lem5458594)). Qed.
Lemma lem5458597 : term669 = term444.
Proof. exact (MK_COMB (@lem5458596) (@lem5458591)). Qed.
Lemma lem5458599 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458600 : term444 = term445.
Proof. exact (@lem5458599 (NUMERAL 0) term120). Qed.
Lemma lem5458601 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458602 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458603 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458602 h1) (fun h1 : term445 = True => @lem5458601)). Qed.
Lemma lem5458604 : term445 = True.
Proof. exact (EQ_MP (@lem5458603) (@lem5458601)). Qed.
Lemma lem5458605 : term444 = True.
Proof. exact (TRANS (@lem5458600) (@lem5458604)). Qed.
Lemma lem5458606 : term669 = True.
Proof. exact (TRANS (@lem5458597) (@lem5458605)). Qed.
Lemma lem5458607 : term666 = True.
Proof. exact (TRANS (@lem5458583) (@lem5458606)). Qed.
Lemma lem5458608 : term444 = True.
Proof. exact (TRANS (@lem5458560) (@lem5458607)). Qed.
Lemma lem5458609 : term663 = True.
Proof. exact (TRANS (@lem5458551) (@lem5458608)). Qed.
Lemma lem5458610 : True = term663.
Proof. exact (SYM (@lem5458609)). Qed.
Lemma lem5458611 : term663.
Proof. exact (EQ_MP (@lem5458610) (@lem0)). Qed.
Lemma lem5458612 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term737 _70533 _70534 _70535.
Proof. exact (conj (@lem5458611) (@lem5458473 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458614 (x : real) (y : real) : term672 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5458615 (_70533 : int) (_70534 : int) (_70535 : int) : term738 _70533 _70534 _70535.
Proof. exact (@lem5458614 term272 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5458616 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term739 _70533 _70534 _70535.
Proof. exact (@lem5458615 _70533 _70534 _70535 (@lem5458612 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458617 (_70533 : int) (_70534 : int) (_70535 : int) : (term740 _70533 _70534 _70535) = (term396 _70533 _70534 _70535).
Proof. exact (@lem1982733 (term396 _70533 _70534 _70535)). Qed.
Lemma lem5458618 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5458619 (_70533 : int) (_70534 : int) (_70535 : int) : (term741 _70533 _70534 _70535) = (term398 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5458618) (@lem5458617 _70533 _70534 _70535)). Qed.
Lemma lem5458620 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5458621 (_70533 : int) (_70534 : int) (_70535 : int) : (term739 _70533 _70534 _70535) = (term399 _70533 _70534 _70535).
Proof. exact (MK_COMB (@lem5458619 _70533 _70534 _70535) (@lem5458620)). Qed.
Lemma lem5458622 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term399 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5458621 _70533 _70534 _70535) (@lem5458616 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458623 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term790 _70533 _70534 _70535.
Proof. exact (conj (@lem5458622 _70532 _70533 _70534 _70535 h1) (@lem5458548 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458625 (x : real) (y : real) : term683 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5458626 (_70533 : int) (_70534 : int) (_70535 : int) : term791 _70533 _70534 _70535.
Proof. exact (@lem5458625 (term396 _70533 _70534 _70535) (term418 _70533 _70534 _70535)). Qed.
Lemma lem5458627 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term792 _70533 _70534 _70535.
Proof. exact (@lem5458626 _70533 _70534 _70535 (@lem5458623 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458628 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = (term794 _70533 _70534 _70535).
Proof. exact (@lem1982753 (term360 _70533) (real_of_int _70533) (term395 _70534 _70535) (term404 _70534 _70535)). Qed.
Lemma lem5458629 (_70533 : int) : (term688 _70533) = (term689 _70533).
Proof. exact (@lem1982713 term335 (real_of_int _70533)). Qed.
Lemma lem5458631 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458632 : term272 = term369.
Proof. exact (@lem5458631 term120). Qed.
Lemma lem5458634 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458635 : term335 = term336.
Proof. exact (@lem5458634 term120). Qed.
Lemma lem5458636 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458637 : term690 = term691.
Proof. exact (MK_COMB (@lem5458636) (@lem5458635)). Qed.
Lemma lem5458638 : term692 = term693.
Proof. exact (MK_COMB (@lem5458637) (@lem5458632)). Qed.
Lemma lem5458639 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5458641 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458642 : term444 = term445.
Proof. exact (@lem5458641 (NUMERAL 0) term120). Qed.
Lemma lem5458643 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458644 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458645 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458644 h1) (fun h1 : term445 = True => @lem5458643)). Qed.
Lemma lem5458646 : term445 = True.
Proof. exact (EQ_MP (@lem5458645) (@lem5458643)). Qed.
Lemma lem5458647 : term444 = True.
Proof. exact (TRANS (@lem5458642) (@lem5458646)). Qed.
Lemma lem5458648 : True = term444.
Proof. exact (SYM (@lem5458647)). Qed.
Lemma lem5458649 : term444.
Proof. exact (EQ_MP (@lem5458648) (@lem0)). Qed.
Lemma lem5458650 : term695.
Proof. exact (@lem5458639 (@lem5458649)). Qed.
Lemma lem5458652 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458653 : term444 = term445.
Proof. exact (@lem5458652 (NUMERAL 0) term120). Qed.
Lemma lem5458654 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458655 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458656 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458655 h1) (fun h1 : term445 = True => @lem5458654)). Qed.
Lemma lem5458657 : term445 = True.
Proof. exact (EQ_MP (@lem5458656) (@lem5458654)). Qed.
Lemma lem5458658 : term444 = True.
Proof. exact (TRANS (@lem5458653) (@lem5458657)). Qed.
Lemma lem5458659 : True = term444.
Proof. exact (SYM (@lem5458658)). Qed.
Lemma lem5458660 : term444.
Proof. exact (EQ_MP (@lem5458659) (@lem0)). Qed.
Lemma lem5458661 : term696.
Proof. exact (@lem5458650 (@lem5458660)). Qed.
Lemma lem5458663 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458664 : term444 = term445.
Proof. exact (@lem5458663 (NUMERAL 0) term120). Qed.
Lemma lem5458665 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458666 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458667 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458666 h1) (fun h1 : term445 = True => @lem5458665)). Qed.
Lemma lem5458668 : term445 = True.
Proof. exact (EQ_MP (@lem5458667) (@lem5458665)). Qed.
Lemma lem5458669 : term444 = True.
Proof. exact (TRANS (@lem5458664) (@lem5458668)). Qed.
Lemma lem5458670 : True = term444.
Proof. exact (SYM (@lem5458669)). Qed.
Lemma lem5458671 : term444.
Proof. exact (EQ_MP (@lem5458670) (@lem0)). Qed.
Lemma lem5458672 : term697.
Proof. exact (@lem5458661 (@lem5458671)). Qed.
Lemma lem5458674 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458675 : term344 = term345.
Proof. exact (@lem5458674 term120 term120). Qed.
Lemma lem5458676 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458677 : term347 = term120.
Proof. exact (EQ_MP (@lem5458676) (@lem940073)). Qed.
Lemma lem5458678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458679 : term345 = term272.
Proof. exact (MK_COMB (@lem5458678) (@lem5458677)). Qed.
Lemma lem5458680 : term344 = term272.
Proof. exact (TRANS (@lem5458675) (@lem5458679)). Qed.
Lemma lem5458682 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5458683 : term370 = term375.
Proof. exact (@lem5458682 term120 term120). Qed.
Lemma lem5458684 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458685 : term347 = term120.
Proof. exact (EQ_MP (@lem5458684) (@lem940073)). Qed.
Lemma lem5458686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458687 : term345 = term272.
Proof. exact (MK_COMB (@lem5458686) (@lem5458685)). Qed.
Lemma lem5458688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5458689 : term375 = term335.
Proof. exact (MK_COMB (@lem5458688) (@lem5458687)). Qed.
Lemma lem5458690 : term370 = term335.
Proof. exact (TRANS (@lem5458683) (@lem5458689)). Qed.
Lemma lem5458691 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458692 : term698 = term690.
Proof. exact (MK_COMB (@lem5458691) (@lem5458690)). Qed.
Lemma lem5458693 : term699 = term692.
Proof. exact (MK_COMB (@lem5458692) (@lem5458680)). Qed.
Lemma lem5458695 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5458696 : term692 = term260.
Proof. exact (@lem5458695 term120). Qed.
Lemma lem5458697 : term699 = term260.
Proof. exact (TRANS (@lem5458693) (@lem5458696)). Qed.
Lemma lem5458698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458699 : term701 = term454.
Proof. exact (MK_COMB (@lem5458698) (@lem5458697)). Qed.
Lemma lem5458700 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5458701 : term702 = term456.
Proof. exact (MK_COMB (@lem5458699) (@lem5458700)). Qed.
Lemma lem5458703 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458704 : term456 = term260.
Proof. exact (@lem5458703 term120). Qed.
Lemma lem5458705 : term702 = term260.
Proof. exact (TRANS (@lem5458701) (@lem5458704)). Qed.
Lemma lem5458707 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458708 : term344 = term345.
Proof. exact (@lem5458707 term120 term120). Qed.
Lemma lem5458709 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458710 : term347 = term120.
Proof. exact (EQ_MP (@lem5458709) (@lem940073)). Qed.
Lemma lem5458711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458712 : term345 = term272.
Proof. exact (MK_COMB (@lem5458711) (@lem5458710)). Qed.
Lemma lem5458713 : term344 = term272.
Proof. exact (TRANS (@lem5458708) (@lem5458712)). Qed.
Lemma lem5458714 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5458715 : term458 = term456.
Proof. exact (MK_COMB (@lem5458714) (@lem5458713)). Qed.
Lemma lem5458717 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458718 : term456 = term260.
Proof. exact (@lem5458717 term120). Qed.
Lemma lem5458719 : term458 = term260.
Proof. exact (TRANS (@lem5458715) (@lem5458718)). Qed.
Lemma lem5458720 : term260 = term458.
Proof. exact (SYM (@lem5458719)). Qed.
Lemma lem5458721 : term702 = term458.
Proof. exact (TRANS (@lem5458705) (@lem5458720)). Qed.
Lemma lem5458722 : term693 = term332.
Proof. exact (@lem5458672 (@lem5458721)). Qed.
Lemma lem5458723 : term692 = term332.
Proof. exact (TRANS (@lem5458638) (@lem5458722)). Qed.
Lemma lem5458725 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5458726 : term332 = term260.
Proof. exact (@lem5458725 term260). Qed.
Lemma lem5458727 : term692 = term260.
Proof. exact (TRANS (@lem5458723) (@lem5458726)). Qed.
Lemma lem5458728 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458729 : term703 = term454.
Proof. exact (MK_COMB (@lem5458728) (@lem5458727)). Qed.
Lemma lem5458730 (_70533 : int) : (real_of_int _70533) = (real_of_int _70533).
Proof. exact (eq_refl (real_of_int _70533)). Qed.
Lemma lem5458731 (_70533 : int) : (term689 _70533) = (term704 _70533).
Proof. exact (MK_COMB (@lem5458729) (@lem5458730 _70533)). Qed.
Lemma lem5458732 (_70533 : int) : (term688 _70533) = (term704 _70533).
Proof. exact (TRANS (@lem5458629 _70533) (@lem5458731 _70533)). Qed.
Lemma lem5458733 (_70533 : int) : (term704 _70533) = term260.
Proof. exact (@lem1982719 (real_of_int _70533)). Qed.
Lemma lem5458734 (_70533 : int) : (term688 _70533) = term260.
Proof. exact (TRANS (@lem5458732 _70533) (@lem5458733 _70533)). Qed.
Lemma lem5458735 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458736 (_70533 : int) : (term705 _70533) = term706.
Proof. exact (MK_COMB (@lem5458735) (@lem5458734 _70533)). Qed.
Lemma lem5458737 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = (term760 _70534 _70535).
Proof. exact (@lem1982753 (term360 _70534) (real_of_int _70534) (term749 _70535) (term360 _70535)). Qed.
Lemma lem5458738 (_70534 : int) : (term688 _70534) = (term689 _70534).
Proof. exact (@lem1982713 term335 (real_of_int _70534)). Qed.
Lemma lem5458740 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458741 : term272 = term369.
Proof. exact (@lem5458740 term120). Qed.
Lemma lem5458743 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458744 : term335 = term336.
Proof. exact (@lem5458743 term120). Qed.
Lemma lem5458745 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458746 : term690 = term691.
Proof. exact (MK_COMB (@lem5458745) (@lem5458744)). Qed.
Lemma lem5458747 : term692 = term693.
Proof. exact (MK_COMB (@lem5458746) (@lem5458741)). Qed.
Lemma lem5458748 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5458750 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458751 : term444 = term445.
Proof. exact (@lem5458750 (NUMERAL 0) term120). Qed.
Lemma lem5458752 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458753 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458754 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458753 h1) (fun h1 : term445 = True => @lem5458752)). Qed.
Lemma lem5458755 : term445 = True.
Proof. exact (EQ_MP (@lem5458754) (@lem5458752)). Qed.
Lemma lem5458756 : term444 = True.
Proof. exact (TRANS (@lem5458751) (@lem5458755)). Qed.
Lemma lem5458757 : True = term444.
Proof. exact (SYM (@lem5458756)). Qed.
Lemma lem5458758 : term444.
Proof. exact (EQ_MP (@lem5458757) (@lem0)). Qed.
Lemma lem5458759 : term695.
Proof. exact (@lem5458748 (@lem5458758)). Qed.
Lemma lem5458761 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458762 : term444 = term445.
Proof. exact (@lem5458761 (NUMERAL 0) term120). Qed.
Lemma lem5458763 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458764 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458765 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458764 h1) (fun h1 : term445 = True => @lem5458763)). Qed.
Lemma lem5458766 : term445 = True.
Proof. exact (EQ_MP (@lem5458765) (@lem5458763)). Qed.
Lemma lem5458767 : term444 = True.
Proof. exact (TRANS (@lem5458762) (@lem5458766)). Qed.
Lemma lem5458768 : True = term444.
Proof. exact (SYM (@lem5458767)). Qed.
Lemma lem5458769 : term444.
Proof. exact (EQ_MP (@lem5458768) (@lem0)). Qed.
Lemma lem5458770 : term696.
Proof. exact (@lem5458759 (@lem5458769)). Qed.
Lemma lem5458772 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458773 : term444 = term445.
Proof. exact (@lem5458772 (NUMERAL 0) term120). Qed.
Lemma lem5458774 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458775 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458776 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458775 h1) (fun h1 : term445 = True => @lem5458774)). Qed.
Lemma lem5458777 : term445 = True.
Proof. exact (EQ_MP (@lem5458776) (@lem5458774)). Qed.
Lemma lem5458778 : term444 = True.
Proof. exact (TRANS (@lem5458773) (@lem5458777)). Qed.
Lemma lem5458779 : True = term444.
Proof. exact (SYM (@lem5458778)). Qed.
Lemma lem5458780 : term444.
Proof. exact (EQ_MP (@lem5458779) (@lem0)). Qed.
Lemma lem5458781 : term697.
Proof. exact (@lem5458770 (@lem5458780)). Qed.
Lemma lem5458783 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458784 : term344 = term345.
Proof. exact (@lem5458783 term120 term120). Qed.
Lemma lem5458785 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458786 : term347 = term120.
Proof. exact (EQ_MP (@lem5458785) (@lem940073)). Qed.
Lemma lem5458787 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458788 : term345 = term272.
Proof. exact (MK_COMB (@lem5458787) (@lem5458786)). Qed.
Lemma lem5458789 : term344 = term272.
Proof. exact (TRANS (@lem5458784) (@lem5458788)). Qed.
Lemma lem5458791 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5458792 : term370 = term375.
Proof. exact (@lem5458791 term120 term120). Qed.
Lemma lem5458793 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458794 : term347 = term120.
Proof. exact (EQ_MP (@lem5458793) (@lem940073)). Qed.
Lemma lem5458795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458796 : term345 = term272.
Proof. exact (MK_COMB (@lem5458795) (@lem5458794)). Qed.
Lemma lem5458797 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5458798 : term375 = term335.
Proof. exact (MK_COMB (@lem5458797) (@lem5458796)). Qed.
Lemma lem5458799 : term370 = term335.
Proof. exact (TRANS (@lem5458792) (@lem5458798)). Qed.
Lemma lem5458800 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458801 : term698 = term690.
Proof. exact (MK_COMB (@lem5458800) (@lem5458799)). Qed.
Lemma lem5458802 : term699 = term692.
Proof. exact (MK_COMB (@lem5458801) (@lem5458789)). Qed.
Lemma lem5458804 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5458805 : term692 = term260.
Proof. exact (@lem5458804 term120). Qed.
Lemma lem5458806 : term699 = term260.
Proof. exact (TRANS (@lem5458802) (@lem5458805)). Qed.
Lemma lem5458807 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458808 : term701 = term454.
Proof. exact (MK_COMB (@lem5458807) (@lem5458806)). Qed.
Lemma lem5458809 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5458810 : term702 = term456.
Proof. exact (MK_COMB (@lem5458808) (@lem5458809)). Qed.
Lemma lem5458812 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458813 : term456 = term260.
Proof. exact (@lem5458812 term120). Qed.
Lemma lem5458814 : term702 = term260.
Proof. exact (TRANS (@lem5458810) (@lem5458813)). Qed.
Lemma lem5458816 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458817 : term344 = term345.
Proof. exact (@lem5458816 term120 term120). Qed.
Lemma lem5458818 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458819 : term347 = term120.
Proof. exact (EQ_MP (@lem5458818) (@lem940073)). Qed.
Lemma lem5458820 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458821 : term345 = term272.
Proof. exact (MK_COMB (@lem5458820) (@lem5458819)). Qed.
Lemma lem5458822 : term344 = term272.
Proof. exact (TRANS (@lem5458817) (@lem5458821)). Qed.
Lemma lem5458823 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5458824 : term458 = term456.
Proof. exact (MK_COMB (@lem5458823) (@lem5458822)). Qed.
Lemma lem5458826 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458827 : term456 = term260.
Proof. exact (@lem5458826 term120). Qed.
Lemma lem5458828 : term458 = term260.
Proof. exact (TRANS (@lem5458824) (@lem5458827)). Qed.
Lemma lem5458829 : term260 = term458.
Proof. exact (SYM (@lem5458828)). Qed.
Lemma lem5458830 : term702 = term458.
Proof. exact (TRANS (@lem5458814) (@lem5458829)). Qed.
Lemma lem5458831 : term693 = term332.
Proof. exact (@lem5458781 (@lem5458830)). Qed.
Lemma lem5458832 : term692 = term332.
Proof. exact (TRANS (@lem5458747) (@lem5458831)). Qed.
Lemma lem5458834 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5458835 : term332 = term260.
Proof. exact (@lem5458834 term260). Qed.
Lemma lem5458836 : term692 = term260.
Proof. exact (TRANS (@lem5458832) (@lem5458835)). Qed.
Lemma lem5458837 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458838 : term703 = term454.
Proof. exact (MK_COMB (@lem5458837) (@lem5458836)). Qed.
Lemma lem5458839 (_70534 : int) : (real_of_int _70534) = (real_of_int _70534).
Proof. exact (eq_refl (real_of_int _70534)). Qed.
Lemma lem5458840 (_70534 : int) : (term689 _70534) = (term704 _70534).
Proof. exact (MK_COMB (@lem5458838) (@lem5458839 _70534)). Qed.
Lemma lem5458841 (_70534 : int) : (term688 _70534) = (term704 _70534).
Proof. exact (TRANS (@lem5458738 _70534) (@lem5458840 _70534)). Qed.
Lemma lem5458842 (_70534 : int) : (term704 _70534) = term260.
Proof. exact (@lem1982719 (real_of_int _70534)). Qed.
Lemma lem5458843 (_70534 : int) : (term688 _70534) = term260.
Proof. exact (TRANS (@lem5458841 _70534) (@lem5458842 _70534)). Qed.
Lemma lem5458844 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458845 (_70534 : int) : (term705 _70534) = term706.
Proof. exact (MK_COMB (@lem5458844) (@lem5458843 _70534)). Qed.
Lemma lem5458846 (_70535 : int) : (term761 _70535) = (term708 _70535).
Proof. exact (@lem1982759 (real_of_int _70535) (term360 _70535) term335). Qed.
Lemma lem5458847 (_70535 : int) : (term709 _70535) = (term689 _70535).
Proof. exact (@lem1982715 term335 (real_of_int _70535)). Qed.
Lemma lem5458849 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458850 : term272 = term369.
Proof. exact (@lem5458849 term120). Qed.
Lemma lem5458852 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458853 : term335 = term336.
Proof. exact (@lem5458852 term120). Qed.
Lemma lem5458854 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458855 : term690 = term691.
Proof. exact (MK_COMB (@lem5458854) (@lem5458853)). Qed.
Lemma lem5458856 : term692 = term693.
Proof. exact (MK_COMB (@lem5458855) (@lem5458850)). Qed.
Lemma lem5458857 : term694.
Proof. exact (@lem1981473 term335 term272 term272 term272 term260 term272). Qed.
Lemma lem5458859 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458860 : term444 = term445.
Proof. exact (@lem5458859 (NUMERAL 0) term120). Qed.
Lemma lem5458861 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458862 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458863 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458862 h1) (fun h1 : term445 = True => @lem5458861)). Qed.
Lemma lem5458864 : term445 = True.
Proof. exact (EQ_MP (@lem5458863) (@lem5458861)). Qed.
Lemma lem5458865 : term444 = True.
Proof. exact (TRANS (@lem5458860) (@lem5458864)). Qed.
Lemma lem5458866 : True = term444.
Proof. exact (SYM (@lem5458865)). Qed.
Lemma lem5458867 : term444.
Proof. exact (EQ_MP (@lem5458866) (@lem0)). Qed.
Lemma lem5458868 : term695.
Proof. exact (@lem5458857 (@lem5458867)). Qed.
Lemma lem5458870 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458871 : term444 = term445.
Proof. exact (@lem5458870 (NUMERAL 0) term120). Qed.
Lemma lem5458872 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458873 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458874 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458873 h1) (fun h1 : term445 = True => @lem5458872)). Qed.
Lemma lem5458875 : term445 = True.
Proof. exact (EQ_MP (@lem5458874) (@lem5458872)). Qed.
Lemma lem5458876 : term444 = True.
Proof. exact (TRANS (@lem5458871) (@lem5458875)). Qed.
Lemma lem5458877 : True = term444.
Proof. exact (SYM (@lem5458876)). Qed.
Lemma lem5458878 : term444.
Proof. exact (EQ_MP (@lem5458877) (@lem0)). Qed.
Lemma lem5458879 : term696.
Proof. exact (@lem5458868 (@lem5458878)). Qed.
Lemma lem5458881 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458882 : term444 = term445.
Proof. exact (@lem5458881 (NUMERAL 0) term120). Qed.
Lemma lem5458883 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458884 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458885 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458884 h1) (fun h1 : term445 = True => @lem5458883)). Qed.
Lemma lem5458886 : term445 = True.
Proof. exact (EQ_MP (@lem5458885) (@lem5458883)). Qed.
Lemma lem5458887 : term444 = True.
Proof. exact (TRANS (@lem5458882) (@lem5458886)). Qed.
Lemma lem5458888 : True = term444.
Proof. exact (SYM (@lem5458887)). Qed.
Lemma lem5458889 : term444.
Proof. exact (EQ_MP (@lem5458888) (@lem0)). Qed.
Lemma lem5458890 : term697.
Proof. exact (@lem5458879 (@lem5458889)). Qed.
Lemma lem5458892 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458893 : term344 = term345.
Proof. exact (@lem5458892 term120 term120). Qed.
Lemma lem5458894 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458895 : term347 = term120.
Proof. exact (EQ_MP (@lem5458894) (@lem940073)). Qed.
Lemma lem5458896 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458897 : term345 = term272.
Proof. exact (MK_COMB (@lem5458896) (@lem5458895)). Qed.
Lemma lem5458898 : term344 = term272.
Proof. exact (TRANS (@lem5458893) (@lem5458897)). Qed.
Lemma lem5458900 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5458901 : term370 = term375.
Proof. exact (@lem5458900 term120 term120). Qed.
Lemma lem5458902 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458903 : term347 = term120.
Proof. exact (EQ_MP (@lem5458902) (@lem940073)). Qed.
Lemma lem5458904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458905 : term345 = term272.
Proof. exact (MK_COMB (@lem5458904) (@lem5458903)). Qed.
Lemma lem5458906 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5458907 : term375 = term335.
Proof. exact (MK_COMB (@lem5458906) (@lem5458905)). Qed.
Lemma lem5458908 : term370 = term335.
Proof. exact (TRANS (@lem5458901) (@lem5458907)). Qed.
Lemma lem5458909 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458910 : term698 = term690.
Proof. exact (MK_COMB (@lem5458909) (@lem5458908)). Qed.
Lemma lem5458911 : term699 = term692.
Proof. exact (MK_COMB (@lem5458910) (@lem5458898)). Qed.
Lemma lem5458913 (m : nat) : (term700 m) = term260.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5458914 : term692 = term260.
Proof. exact (@lem5458913 term120). Qed.
Lemma lem5458915 : term699 = term260.
Proof. exact (TRANS (@lem5458911) (@lem5458914)). Qed.
Lemma lem5458916 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458917 : term701 = term454.
Proof. exact (MK_COMB (@lem5458916) (@lem5458915)). Qed.
Lemma lem5458918 : term272 = term272.
Proof. exact (eq_refl term272). Qed.
Lemma lem5458919 : term702 = term456.
Proof. exact (MK_COMB (@lem5458917) (@lem5458918)). Qed.
Lemma lem5458921 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458922 : term456 = term260.
Proof. exact (@lem5458921 term120). Qed.
Lemma lem5458923 : term702 = term260.
Proof. exact (TRANS (@lem5458919) (@lem5458922)). Qed.
Lemma lem5458925 (m : nat) (n : nat) : (term342 m n) = (term343 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5458926 : term344 = term345.
Proof. exact (@lem5458925 term120 term120). Qed.
Lemma lem5458927 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5458928 : term347 = term120.
Proof. exact (EQ_MP (@lem5458927) (@lem940073)). Qed.
Lemma lem5458929 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5458930 : term345 = term272.
Proof. exact (MK_COMB (@lem5458929) (@lem5458928)). Qed.
Lemma lem5458931 : term344 = term272.
Proof. exact (TRANS (@lem5458926) (@lem5458930)). Qed.
Lemma lem5458932 : term454 = term454.
Proof. exact (eq_refl term454). Qed.
Lemma lem5458933 : term458 = term456.
Proof. exact (MK_COMB (@lem5458932) (@lem5458931)). Qed.
Lemma lem5458935 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5458936 : term456 = term260.
Proof. exact (@lem5458935 term120). Qed.
Lemma lem5458937 : term458 = term260.
Proof. exact (TRANS (@lem5458933) (@lem5458936)). Qed.
Lemma lem5458938 : term260 = term458.
Proof. exact (SYM (@lem5458937)). Qed.
Lemma lem5458939 : term702 = term458.
Proof. exact (TRANS (@lem5458923) (@lem5458938)). Qed.
Lemma lem5458940 : term693 = term332.
Proof. exact (@lem5458890 (@lem5458939)). Qed.
Lemma lem5458941 : term692 = term332.
Proof. exact (TRANS (@lem5458856) (@lem5458940)). Qed.
Lemma lem5458943 (x : real) : (term351 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5458944 : term332 = term260.
Proof. exact (@lem5458943 term260). Qed.
Lemma lem5458945 : term692 = term260.
Proof. exact (TRANS (@lem5458941) (@lem5458944)). Qed.
Lemma lem5458946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5458947 : term703 = term454.
Proof. exact (MK_COMB (@lem5458946) (@lem5458945)). Qed.
Lemma lem5458948 (_70535 : int) : (real_of_int _70535) = (real_of_int _70535).
Proof. exact (eq_refl (real_of_int _70535)). Qed.
Lemma lem5458949 (_70535 : int) : (term689 _70535) = (term704 _70535).
Proof. exact (MK_COMB (@lem5458947) (@lem5458948 _70535)). Qed.
Lemma lem5458950 (_70535 : int) : (term709 _70535) = (term704 _70535).
Proof. exact (TRANS (@lem5458847 _70535) (@lem5458949 _70535)). Qed.
Lemma lem5458951 (_70535 : int) : (term704 _70535) = term260.
Proof. exact (@lem1982719 (real_of_int _70535)). Qed.
Lemma lem5458952 (_70535 : int) : (term709 _70535) = term260.
Proof. exact (TRANS (@lem5458950 _70535) (@lem5458951 _70535)). Qed.
Lemma lem5458953 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5458954 (_70535 : int) : (term710 _70535) = term706.
Proof. exact (MK_COMB (@lem5458953) (@lem5458952 _70535)). Qed.
Lemma lem5458955 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem5458956 (_70535 : int) : (term708 _70535) = term711.
Proof. exact (MK_COMB (@lem5458954 _70535) (@lem5458955)). Qed.
Lemma lem5458957 (_70535 : int) : (term761 _70535) = term711.
Proof. exact (TRANS (@lem5458846 _70535) (@lem5458956 _70535)). Qed.
Lemma lem5458958 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5458959 (_70535 : int) : (term761 _70535) = term335.
Proof. exact (TRANS (@lem5458957 _70535) (@lem5458958)). Qed.
Lemma lem5458960 (_70534 : int) (_70535 : int) : (term760 _70534 _70535) = term711.
Proof. exact (MK_COMB (@lem5458845 _70534) (@lem5458959 _70535)). Qed.
Lemma lem5458961 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = term711.
Proof. exact (TRANS (@lem5458737 _70534 _70535) (@lem5458960 _70534 _70535)). Qed.
Lemma lem5458962 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5458963 (_70534 : int) (_70535 : int) : (term759 _70534 _70535) = term335.
Proof. exact (TRANS (@lem5458961 _70534 _70535) (@lem5458962)). Qed.
Lemma lem5458964 (_70533 : int) (_70534 : int) (_70535 : int) : (term794 _70533 _70534 _70535) = term711.
Proof. exact (MK_COMB (@lem5458736 _70533) (@lem5458963 _70534 _70535)). Qed.
Lemma lem5458965 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = term711.
Proof. exact (TRANS (@lem5458628 _70533 _70534 _70535) (@lem5458964 _70533 _70534 _70535)). Qed.
Lemma lem5458966 : term711 = term335.
Proof. exact (@lem1982721 term335). Qed.
Lemma lem5458967 (_70533 : int) (_70534 : int) (_70535 : int) : (term793 _70533 _70534 _70535) = term335.
Proof. exact (TRANS (@lem5458965 _70533 _70534 _70535) (@lem5458966)). Qed.
Lemma lem5458968 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5458969 (_70533 : int) (_70534 : int) (_70535 : int) : (term795 _70533 _70534 _70535) = term713.
Proof. exact (MK_COMB (@lem5458968) (@lem5458967 _70533 _70534 _70535)). Qed.
Lemma lem5458970 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem5458971 (_70533 : int) (_70534 : int) (_70535 : int) : (term792 _70533 _70534 _70535) = term714.
Proof. exact (MK_COMB (@lem5458969 _70533 _70534 _70535) (@lem5458970)). Qed.
Lemma lem5458972 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : term714.
Proof. exact (EQ_MP (@lem5458971 _70533 _70534 _70535) (@lem5458627 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5458974 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5458975 : term714 = term715.
Proof. exact (@lem5458974 term260 term335). Qed.
Lemma lem5458977 (x : nat) : (term333 x) = (term334 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5458978 : term335 = term336.
Proof. exact (@lem5458977 term120). Qed.
Lemma lem5458980 (x : nat) : (real_of_num x) = (term331 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5458981 : term260 = term332.
Proof. exact (@lem5458980 (NUMERAL 0)). Qed.
Lemma lem5458982 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5458983 : term262 = term716.
Proof. exact (MK_COMB (@lem5458982) (@lem5458981)). Qed.
Lemma lem5458984 : term715 = term717.
Proof. exact (MK_COMB (@lem5458983) (@lem5458978)). Qed.
Lemma lem5458985 : term718.
Proof. exact (@lem1980026 term260 term272 term335 term272). Qed.
Lemma lem5458987 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458988 : term444 = term445.
Proof. exact (@lem5458987 (NUMERAL 0) term120). Qed.
Lemma lem5458989 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5458990 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5458991 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5458990 h1) (fun h1 : term445 = True => @lem5458989)). Qed.
Lemma lem5458992 : term445 = True.
Proof. exact (EQ_MP (@lem5458991) (@lem5458989)). Qed.
Lemma lem5458993 : term444 = True.
Proof. exact (TRANS (@lem5458988) (@lem5458992)). Qed.
Lemma lem5458994 : True = term444.
Proof. exact (SYM (@lem5458993)). Qed.
Lemma lem5458995 : term444.
Proof. exact (EQ_MP (@lem5458994) (@lem0)). Qed.
Lemma lem5458996 : term719.
Proof. exact (@lem5458985 (@lem5458995)). Qed.
Lemma lem5458998 (m : nat) (n : nat) : (term443 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5458999 : term444 = term445.
Proof. exact (@lem5458998 (NUMERAL 0) term120). Qed.
Lemma lem5459000 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5459001 (h1 : term446 = (BIT1 0)) : term445 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5459002 : (term446 = (BIT1 0)) = (term445 = True).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5459001 h1) (fun h1 : term445 = True => @lem5459000)). Qed.
Lemma lem5459003 : term445 = True.
Proof. exact (EQ_MP (@lem5459002) (@lem5459000)). Qed.
Lemma lem5459004 : term444 = True.
Proof. exact (TRANS (@lem5458999) (@lem5459003)). Qed.
Lemma lem5459005 : True = term444.
Proof. exact (SYM (@lem5459004)). Qed.
Lemma lem5459006 : term444.
Proof. exact (EQ_MP (@lem5459005) (@lem0)). Qed.
Lemma lem5459007 : term717 = term720.
Proof. exact (@lem5458996 (@lem5459006)). Qed.
Lemma lem5459009 (m : nat) (n : nat) : (term373 m n) = (term374 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5459010 : term370 = term375.
Proof. exact (@lem5459009 term120 term120). Qed.
Lemma lem5459011 : (term346 = (BIT1 0)) = (term347 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5459012 : term347 = term120.
Proof. exact (EQ_MP (@lem5459011) (@lem940073)). Qed.
Lemma lem5459013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5459014 : term345 = term272.
Proof. exact (MK_COMB (@lem5459013) (@lem5459012)). Qed.
Lemma lem5459015 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5459016 : term375 = term335.
Proof. exact (MK_COMB (@lem5459015) (@lem5459014)). Qed.
Lemma lem5459017 : term370 = term335.
Proof. exact (TRANS (@lem5459010) (@lem5459016)). Qed.
Lemma lem5459019 (x : nat) : (term457 x) = term260.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5459020 : term456 = term260.
Proof. exact (@lem5459019 term120). Qed.
Lemma lem5459021 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5459022 : term721 = term262.
Proof. exact (MK_COMB (@lem5459021) (@lem5459020)). Qed.
Lemma lem5459023 : term720 = term715.
Proof. exact (MK_COMB (@lem5459022) (@lem5459017)). Qed.
Lemma lem5459025 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5459026 : term715 = term724.
Proof. exact (@lem5459025 (NUMERAL 0) term120). Qed.
Lemma lem5459027 : term446 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5459028 (h1 : term446 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5459029 : (term446 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term446 = (BIT1 0) => @lem5459028 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem5459027)). Qed.
Lemma lem5459030 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5459029) (@lem5459027)). Qed.
Lemma lem5459031 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5459032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5459033 : term725 = (and True).
Proof. exact (MK_COMB (@lem5459032) (@lem5459031)). Qed.
Lemma lem5459034 : term724 = (True /\ False).
Proof. exact (MK_COMB (@lem5459033) (@lem5459030)). Qed.
Lemma lem5459036 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5459037 : term724 = False.
Proof. exact (TRANS (@lem5459034) (@lem5459036)). Qed.
Lemma lem5459038 : term715 = False.
Proof. exact (TRANS (@lem5459026) (@lem5459037)). Qed.
Lemma lem5459039 : term720 = False.
Proof. exact (TRANS (@lem5459023) (@lem5459038)). Qed.
Lemma lem5459040 : term717 = False.
Proof. exact (TRANS (@lem5459007) (@lem5459039)). Qed.
Lemma lem5459041 : term715 = False.
Proof. exact (TRANS (@lem5458984) (@lem5459040)). Qed.
Lemma lem5459042 : term714 = False.
Proof. exact (TRANS (@lem5458975) (@lem5459041)). Qed.
Lemma lem5459043 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term799 _70532 _70533 _70534 _70535) : False.
Proof. exact (EQ_MP (@lem5459042) (@lem5458972 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5459044 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term636 _70532 _70533 _70534 _70535) : False.
Proof. exact (or_elim (@lem5457871 _70532 _70533 _70534 _70535 h1) (fun h0 : term798 _70532 _70533 _70534 _70535 => @lem5458457 _70532 _70533 _70534 _70535 h0) (fun h0 : term799 _70532 _70533 _70534 _70535 => @lem5459043 _70532 _70533 _70534 _70535 h0)). Qed.
Lemma lem5459045 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term645 _70532 _70533 _70534 _70535) : False.
Proof. exact (or_elim (@lem5456922 _70532 _70533 _70534 _70535 h1) (fun h0 : term640 _70532 _70534 _70533 _70535 => @lem5457870 _70532 _70534 _70533 _70535 h0) (fun h0 : term636 _70532 _70533 _70534 _70535 => @lem5459044 _70532 _70533 _70534 _70535 h0)). Qed.
Lemma lem5459046 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term661 _70532 _70533 _70534 _70535) : False.
Proof. exact (or_elim (@lem5454263 _70532 _70533 _70534 _70535 h1) (fun h0 : term658 _70532 _70533 _70534 _70535 => @lem5456921 _70532 _70533 _70534 _70535 h0) (fun h0 : term645 _70532 _70533 _70534 _70535 => @lem5459045 _70532 _70533 _70534 _70535 h0)). Qed.
Lemma lem5459048 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term661 _70532 _70533 _70534 _70535) : term661 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5459049 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term661 _70532 _70533 _70534 _70535) : (term661 _70532 _70533 _70534 _70535) = False.
Proof. exact (prop_ext (fun h2 : term661 _70532 _70533 _70534 _70535 => @lem5459046 _70532 _70533 _70534 _70535 h1) (fun h2 : False => @lem5459048 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5459050 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term661 _70532 _70533 _70534 _70535) : False.
Proof. exact (EQ_MP (@lem5459049 _70532 _70533 _70534 _70535 h1) (@lem5459048 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5459051 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term327 _70532 _70533 _70534 _70535) : term327 _70532 _70533 _70534 _70535.
Proof. exact (h1). Qed.
Lemma lem5459052 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term327 _70532 _70533 _70534 _70535) : term661 _70532 _70533 _70534 _70535.
Proof. exact (EQ_MP (@lem5454217 _70532 _70533 _70534 _70535) (@lem5459051 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5459053 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term327 _70532 _70533 _70534 _70535) : (term661 _70532 _70533 _70534 _70535) = False.
Proof. exact (prop_ext (fun h2 : term661 _70532 _70533 _70534 _70535 => @lem5459050 _70532 _70533 _70534 _70535 h2) (fun h2 : False => @lem5459052 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5459054 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) (h1 : term327 _70532 _70533 _70534 _70535) : False.
Proof. exact (EQ_MP (@lem5459053 _70532 _70533 _70534 _70535 h1) (@lem5459052 _70532 _70533 _70534 _70535 h1)). Qed.
Lemma lem5459055 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : term800 _70532 _70533 _70534 _70535.
Proof. exact (fun h0 : term327 _70532 _70533 _70534 _70535 => @lem5459054 _70532 _70533 _70534 _70535 h0). Qed.
Lemma lem5459056 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : term801 _70532 _70533 _70534 _70535.
Proof. exact (@lem1386578 (term802 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5459059 (_70532 : int) (_70533 : int) (_70534 : int) (_70535 : int) : term802 _70532 _70533 _70534 _70535.
Proof. exact (@lem5459056 _70532 _70533 _70534 _70535 (@lem5459055 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5459060 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term325 _70532 _70533 _70534 _70535) = (term253 _70532 _70535 _70533 _70534).
Proof. exact (SYM (@lem5452670 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5459061 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5459062 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : (term802 _70532 _70533 _70534 _70535) = (term172 _70532 _70535 _70533 _70534).
Proof. exact (MK_COMB (@lem5459061) (@lem5459060 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5459063 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : term172 _70532 _70535 _70533 _70534.
Proof. exact (EQ_MP (@lem5459062 _70532 _70535 _70533 _70534) (@lem5459059 _70532 _70533 _70534 _70535)). Qed.
Lemma lem5459064 (_70532 : int) (_70535 : int) (_70533 : int) (_70534 : int) : term173 _70532 _70535 _70533 _70534.
Proof. exact (EQ_MP (@lem5452127 _70532 _70535 _70533 _70534) (@lem5459063 _70532 _70535 _70533 _70534)). Qed.
Lemma lem5459065 (m : nat) (x : nat) (n : nat) (p : nat) : term803 m x n p.
Proof. exact (@lem5459064 (int_of_num m) (int_of_num x) (int_of_num n) (int_of_num p)). Qed.
Lemma lem5459066 (m : nat) (x : nat) (n : nat) (p : nat) : term804 m x n p.
Proof. exact (@lem5459065 m x n p (@lem5452117 m)). Qed.
Lemma lem5459067 (m : nat) (x : nat) (n : nat) (p : nat) : term805 m x n p.
Proof. exact (@lem5459066 m x n p (@lem5452120 n)). Qed.
Lemma lem5459068 (m : nat) (x : nat) (n : nat) (p : nat) : term806 m x n p.
Proof. exact (@lem5459067 m x n p (@lem5452123 p)). Qed.
Lemma lem5459069 (m : nat) (x : nat) (n : nat) (p : nat) : term161 m x n p.
Proof. exact (@lem5459068 m x n p (@lem5452126 x)). Qed.
Lemma lem5459070 (m : nat) (n : nat) (p : nat) : term163 m n p.
Proof. exact (fun x : nat => @lem5459069 m x n p). Qed.
Lemma lem5459071 (m : nat) (n : nat) : term165 m n.
Proof. exact (fun p : nat => @lem5459070 m n p). Qed.
Lemma lem5459072 (m : nat) : term167 m.
Proof. exact (fun n : nat => @lem5459071 m n). Qed.
Lemma lem5459073 : term169.
Proof. exact (fun m : nat => @lem5459072 m). Qed.
Lemma lem5459074 : term169 = term54.
Proof. exact (SYM (@lem5452114)). Qed.
Lemma lem5459075 : term54.
Proof. exact (EQ_MP (@lem5459074) (@lem5459073)). Qed.
Lemma lem5459076 : term54 = (term54 = True).
Proof. exact (@lem7 term54). Qed.
Lemma lem5459077 : term54 = True.
Proof. exact (EQ_MP (@lem5459076) (@lem5459075)). Qed.
Lemma lem5459078 : True = term54.
Proof. exact (SYM (@lem5459077)). Qed.
Lemma lem5459079 : term54.
Proof. exact (EQ_MP (@lem5459078) (@lem0)). Qed.
Lemma lem5459080 : term53.
Proof. exact (EQ_MP (@lem5451561) (@lem5459079)). Qed.
