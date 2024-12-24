Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_MONO_term_abbrevs.
Require Import LE_EXISTS_spec.
Require Import REAL_LE_LMUL_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_POW_ADD_spec.
Require Import REAL_POW_LE_1_spec.
Require Import thm0_spec.
Require Import thm1339577_spec.
Require Import thm1340282_spec.
Require Import thm1842_spec.
Require Import thm517422_spec.
Require Import thm519779_spec.
Require Import thm7_spec.
Lemma lem1636869 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1636870 (n : nat) (h1 : term0) : term1 n.
Proof. exact (@lem1636869 h1 n). Qed.
Lemma lem1636871 (n : nat) : (term1 n) = (term2 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1636872 (n : nat) (h1 : term0) : term2 n.
Proof. exact (EQ_MP (@lem1636871 n) (@lem1636870 n h1)). Qed.
Lemma lem1636873 (n : nat) (x : real) (h1 : term0) : term3 n x.
Proof. exact (@lem1636872 n h1 x). Qed.
Lemma lem1636874 (x : real) (n : nat) : (term3 n x) = (term4 x n).
Proof. exact (eq_refl (term3 n x)). Qed.
Lemma lem1636875 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (EQ_MP (@lem1636874 x n) (@lem1636873 n x h1)). Qed.
Lemma lem1636876 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1636877 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1636875 x n h1 (@lem1636876 x h2)). Qed.
Lemma lem1636878 (n : nat) (x : real) (h1 : term5 x) : term7 x n.
Proof. exact (fun h0 : term0 => @lem1636877 n x h0 h1). Qed.
Lemma lem1636879 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1636880 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1636878 n x h2 (@lem1636879 h1)). Qed.
Lemma lem1636881 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (fun h0 : term5 x => @lem1636880 n x h1 h0). Qed.
Lemma lem1636882 (x : real) (h1 : term0) : term8 x.
Proof. exact (fun n : nat => @lem1636881 x n h1). Qed.
Lemma lem1636883 (h1 : term0) : term9.
Proof. exact (fun x : real => @lem1636882 x h1). Qed.
Lemma lem1636884 : term10.
Proof. exact (fun h0 : term0 => @lem1636883 h0). Qed.
Lemma lem1636885 : term9.
Proof. exact (@lem1636884 (@lem1636789)). Qed.
Lemma lem1636886 (x : real) : term11 x.
Proof. exact (@lem1636885 x). Qed.
Lemma lem1636887 (x : real) : (term11 x) = (term8 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1636888 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1636887 x) (@lem1636886 x)). Qed.
Lemma lem1636889 (x : real) (n : nat) : term12 x n.
Proof. exact (@lem1636888 x n). Qed.
Lemma lem1636890 (x : real) (n : nat) : (term12 x n) = (term4 x n).
Proof. exact (eq_refl (term12 x n)). Qed.
Lemma lem1636892 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1636893 (n : nat) (h1 : term0) : term1 n.
Proof. exact (@lem1636892 h1 n). Qed.
Lemma lem1636894 (n : nat) : (term1 n) = (term2 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1636895 (n : nat) (h1 : term0) : term2 n.
Proof. exact (EQ_MP (@lem1636894 n) (@lem1636893 n h1)). Qed.
Lemma lem1636896 (n : nat) (x : real) (h1 : term0) : term3 n x.
Proof. exact (@lem1636895 n h1 x). Qed.
Lemma lem1636897 (x : real) (n : nat) : (term3 n x) = (term4 x n).
Proof. exact (eq_refl (term3 n x)). Qed.
Lemma lem1636898 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (EQ_MP (@lem1636897 x n) (@lem1636896 n x h1)). Qed.
Lemma lem1636899 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1636900 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1636898 x n h1 (@lem1636899 x h2)). Qed.
Lemma lem1636901 (n : nat) (x : real) (h1 : term5 x) : term7 x n.
Proof. exact (fun h0 : term0 => @lem1636900 n x h0 h1). Qed.
Lemma lem1636902 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1636903 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1636901 n x h2 (@lem1636902 h1)). Qed.
Lemma lem1636904 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (fun h0 : term5 x => @lem1636903 n x h1 h0). Qed.
Lemma lem1636905 (x : real) (h1 : term0) : term8 x.
Proof. exact (fun n : nat => @lem1636904 x n h1). Qed.
Lemma lem1636906 (h1 : term0) : term9.
Proof. exact (fun x : real => @lem1636905 x h1). Qed.
Lemma lem1636907 : term10.
Proof. exact (fun h0 : term0 => @lem1636906 h0). Qed.
Lemma lem1636908 : term9.
Proof. exact (@lem1636907 (@lem1636789)). Qed.
Lemma lem1636909 (x : real) : term11 x.
Proof. exact (@lem1636908 x). Qed.
Lemma lem1636910 (x : real) : (term11 x) = (term8 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1636911 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1636910 x) (@lem1636909 x)). Qed.
Lemma lem1636912 (x : real) (n : nat) : term12 x n.
Proof. exact (@lem1636911 x n). Qed.
Lemma lem1636913 (x : real) (n : nat) : (term12 x n) = (term4 x n).
Proof. exact (eq_refl (term12 x n)). Qed.
Lemma lem1637187 : term13.
Proof. exact (EQ_MP (@lem517422) (@lem519779)). Qed.
Lemma lem1637188 : term14.
Proof. exact (proj2 (@lem1637187)). Qed.
Lemma lem1637189 : term15.
Proof. exact (proj2 (@lem1637188)). Qed.
Lemma lem1637190 : term16.
Proof. exact (proj2 (@lem1637189)). Qed.
Lemma lem1637191 : term17.
Proof. exact (proj2 (@lem1637190)). Qed.
Lemma lem1637192 : term18.
Proof. exact (proj2 (@lem1637191)). Qed.
Lemma lem1637224 : term19.
Proof. exact (proj1 (@lem1637192)). Qed.
Lemma lem1637225 (n : nat) : term20 n.
Proof. exact (@lem1637224 n). Qed.
Lemma lem1637226 (n : nat) : (term20 n) = ((term21 n) = True).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem1637241 : term22.
Proof. exact (proj1 (@lem1637187)). Qed.
Lemma lem1637242 (m : nat) : term23 m.
Proof. exact (@lem1637241 m). Qed.
Lemma lem1637243 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem1637244 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem1637243 m) (@lem1637242 m)). Qed.
Lemma lem1637245 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem1637244 m n). Qed.
Lemma lem1637246 (m : nat) (n : nat) : (term25 m n) = ((term26 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1637559 (m : nat) : term27 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1637560 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1637561 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem1637560 m) (@lem1637559 m)). Qed.
Lemma lem1637562 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1637561 m n). Qed.
Lemma lem1637563 (m : nat) (n : nat) : (term29 m n) = ((term30 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1637565 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1637566 (x : real) (h1 : term31) : term32 x.
Proof. exact (@lem1637565 h1 x). Qed.
Lemma lem1637567 (x : real) : (term32 x) = (term33 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1637568 (x : real) (h1 : term31) : term33 x.
Proof. exact (EQ_MP (@lem1637567 x) (@lem1637566 x h1)). Qed.
Lemma lem1637569 (x : real) (y : real) (h1 : term31) : term34 x y.
Proof. exact (@lem1637568 x h1 y). Qed.
Lemma lem1637570 (y : real) (x : real) : (term34 x y) = (term35 y x).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1637571 (y : real) (x : real) (h1 : term31) : term35 y x.
Proof. exact (EQ_MP (@lem1637570 y x) (@lem1637569 x y h1)). Qed.
Lemma lem1637572 (y : real) (x : real) (z : real) (h1 : term31) : term36 y x z.
Proof. exact (@lem1637571 y x h1 z). Qed.
Lemma lem1637573 (y : real) (x : real) (z : real) : (term36 y x z) = (term37 y x z).
Proof. exact (eq_refl (term36 y x z)). Qed.
Lemma lem1637574 (y : real) (x : real) (z : real) (h1 : term31) : term37 y x z.
Proof. exact (EQ_MP (@lem1637573 y x z) (@lem1637572 y x z h1)). Qed.
Lemma lem1637575 (x : real) (y : real) (z : real) (h1 : term38 x y z) : term38 x y z.
Proof. exact (h1). Qed.
Lemma lem1637576 (x : real) (y : real) (z : real) (h1 : term31) (h2 : term38 x y z) : real_le x z.
Proof. exact (@lem1637574 y x z h1 (@lem1637575 x y z h2)). Qed.
Lemma lem1637577 (x : real) (y : real) (z : real) (h1 : term38 x y z) : term39 x z.
Proof. exact (fun h0 : term31 => @lem1637576 x y z h0 h1). Qed.
Lemma lem1637578 (x : real) (z : real) (h1 : term40 x z) : term40 x z.
Proof. exact (h1). Qed.
Lemma lem1637579 (x : real) (z : real) (h1 : term40 x z) : term39 x z.
Proof. exact (ex_elim (@lem1637578 x z h1) (fun y : real => fun h0 : term41 x z y => @lem1637577 x y z h0)). Qed.
Lemma lem1637580 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1637581 (x : real) (z : real) (h1 : term31) (h2 : term40 x z) : real_le x z.
Proof. exact (@lem1637579 x z h2 (@lem1637580 h1)). Qed.
Lemma lem1637582 (x : real) (z : real) (h1 : term31) : term42 x z.
Proof. exact (fun h0 : term40 x z => @lem1637581 x z h1 h0). Qed.
Lemma lem1637583 (x : real) (h1 : term31) : term43 x.
Proof. exact (fun z : real => @lem1637582 x z h1). Qed.
Lemma lem1637584 (h1 : term31) : term44.
Proof. exact (fun x : real => @lem1637583 x h1). Qed.
Lemma lem1637585 : term45.
Proof. exact (fun h0 : term31 => @lem1637584 h0). Qed.
Lemma lem1637586 : term44.
Proof. exact (@lem1637585 (@lem1339577)). Qed.
Lemma lem1637587 (x : real) : term46 x.
Proof. exact (@lem1637586 x). Qed.
Lemma lem1637588 (x : real) : (term46 x) = (term43 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1637589 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1637588 x) (@lem1637587 x)). Qed.
Lemma lem1637590 (x : real) (z : real) : term47 x z.
Proof. exact (@lem1637589 x z). Qed.
Lemma lem1637591 (x : real) (z : real) : (term47 x z) = (term42 x z).
Proof. exact (eq_refl (term47 x z)). Qed.
Lemma lem1637593 (h1 : term48) : term48.
Proof. exact (h1). Qed.
Lemma lem1637594 (x : real) (h1 : term48) : term49 x.
Proof. exact (@lem1637593 h1 x). Qed.
Lemma lem1637595 (x : real) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1637596 (x : real) (h1 : term48) : term50 x.
Proof. exact (EQ_MP (@lem1637595 x) (@lem1637594 x h1)). Qed.
Lemma lem1637597 (x : real) (y : real) (h1 : term48) : term51 x y.
Proof. exact (@lem1637596 x h1 y). Qed.
Lemma lem1637598 (y : real) (x : real) : (term51 x y) = (term52 y x).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem1637599 (y : real) (x : real) (h1 : term48) : term52 y x.
Proof. exact (EQ_MP (@lem1637598 y x) (@lem1637597 x y h1)). Qed.
Lemma lem1637600 (y : real) (x : real) (z : real) (h1 : term48) : term53 y x z.
Proof. exact (@lem1637599 y x h1 z). Qed.
Lemma lem1637601 (y : real) (x : real) (z : real) : (term53 y x z) = (term54 y x z).
Proof. exact (eq_refl (term53 y x z)). Qed.
Lemma lem1637602 (y : real) (x : real) (z : real) (h1 : term48) : term54 y x z.
Proof. exact (EQ_MP (@lem1637601 y x z) (@lem1637600 y x z h1)). Qed.
Lemma lem1637603 (x : real) (y : real) (z : real) (h1 : term55 x y z) : term55 x y z.
Proof. exact (h1). Qed.
Lemma lem1637604 (x : real) (y : real) (z : real) (h1 : term48) (h2 : term55 x y z) : term56 y x z.
Proof. exact (@lem1637602 y x z h1 (@lem1637603 x y z h2)). Qed.
Lemma lem1637605 (x : real) (y : real) (z : real) (h1 : term55 x y z) : term57 y x z.
Proof. exact (fun h0 : term48 => @lem1637604 x y z h0 h1). Qed.
Lemma lem1637606 (h1 : term48) : term48.
Proof. exact (h1). Qed.
Lemma lem1637607 (x : real) (y : real) (z : real) (h1 : term48) (h2 : term55 x y z) : term56 y x z.
Proof. exact (@lem1637605 x y z h2 (@lem1637606 h1)). Qed.
Lemma lem1637608 (y : real) (x : real) (z : real) (h1 : term48) : term54 y x z.
Proof. exact (fun h0 : term55 x y z => @lem1637607 x y z h1 h0). Qed.
Lemma lem1637609 (y : real) (x : real) (h1 : term48) : term52 y x.
Proof. exact (fun z : real => @lem1637608 y x z h1). Qed.
Lemma lem1637610 (y : real) (h1 : term48) : term58 y.
Proof. exact (fun x : real => @lem1637609 y x h1). Qed.
Lemma lem1637611 (h1 : term48) : term59.
Proof. exact (fun y : real => @lem1637610 y h1). Qed.
Lemma lem1637612 : term60.
Proof. exact (fun h0 : term48 => @lem1637611 h0). Qed.
Lemma lem1637613 : term59.
Proof. exact (@lem1637612 (@lem1583207)). Qed.
Lemma lem1637614 (y : real) : term61 y.
Proof. exact (@lem1637613 y). Qed.
Lemma lem1637615 (y : real) : (term61 y) = (term58 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem1637616 (y : real) : term58 y.
Proof. exact (EQ_MP (@lem1637615 y) (@lem1637614 y)). Qed.
Lemma lem1637617 (y : real) (x : real) : term62 y x.
Proof. exact (@lem1637616 y x). Qed.
Lemma lem1637618 (y : real) (x : real) : (term62 y x) = (term52 y x).
Proof. exact (eq_refl (term62 y x)). Qed.
Lemma lem1637619 (y : real) (x : real) : term52 y x.
Proof. exact (EQ_MP (@lem1637618 y x) (@lem1637617 y x)). Qed.
Lemma lem1637620 (y : real) (x : real) (z : real) : term53 y x z.
Proof. exact (@lem1637619 y x z). Qed.
Lemma lem1637621 (y : real) (x : real) (z : real) : (term53 y x z) = (term54 y x z).
Proof. exact (eq_refl (term53 y x z)). Qed.
Lemma lem1637624 (x : real) (h1 : (term63 x) = x) : (term63 x) = x.
Proof. exact (h1). Qed.
Lemma lem1637625 (x : real) (h1 : (term63 x) = x) : x = (term63 x).
Proof. exact (SYM (@lem1637624 x h1)). Qed.
Lemma lem1637626 (x : real) (h1 : x = (term63 x)) : x = (term63 x).
Proof. exact (h1). Qed.
Lemma lem1637627 (x : real) (h1 : x = (term63 x)) : (term63 x) = x.
Proof. exact (SYM (@lem1637626 x h1)). Qed.
Lemma lem1637628 (x : real) : ((term63 x) = x) = (x = (term63 x)).
Proof. exact (prop_ext (fun h1 : (term63 x) = x => @lem1637625 x h1) (fun h1 : x = (term63 x) => @lem1637627 x h1)). Qed.
Lemma lem1637629 : term64 = term65.
Proof. exact (fun_ext (fun x : real => @lem1637628 x)). Qed.
Lemma lem1637630 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1637631 : term66 = term67.
Proof. exact (MK_COMB (@lem1637630) (@lem1637629)). Qed.
Lemma lem1637632 : term67.
Proof. exact (EQ_MP (@lem1637631) (@lem1383409)). Qed.
Lemma lem1637633 (x : real) : term68 x.
Proof. exact (@lem1637632 x). Qed.
Lemma lem1637634 (x : real) : (term68 x) = (x = (term63 x)).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1637636 (x : real) : term69 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem1637637 (x : real) : (term69 x) = (term70 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1637638 (x : real) : term70 x.
Proof. exact (EQ_MP (@lem1637637 x) (@lem1637636 x)). Qed.
Lemma lem1637639 (x : real) (m : nat) : term71 x m.
Proof. exact (@lem1637638 x m). Qed.
Lemma lem1637640 (m : nat) (x : real) : (term71 x m) = (term72 m x).
Proof. exact (eq_refl (term71 x m)). Qed.
Lemma lem1637641 (m : nat) (x : real) : term72 m x.
Proof. exact (EQ_MP (@lem1637640 m x) (@lem1637639 x m)). Qed.
Lemma lem1637642 (m : nat) (x : real) (n : nat) : term73 m x n.
Proof. exact (@lem1637641 m x n). Qed.
Lemma lem1637643 (m : nat) (x : real) (n : nat) : (term73 m x n) = ((term74 x m n) = (term75 m x n)).
Proof. exact (eq_refl (term73 m x n)). Qed.
Lemma lem1637645 (m : nat) : term76 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1637646 (m : nat) : (term76 m) = (term77 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem1637647 (m : nat) : term77 m.
Proof. exact (EQ_MP (@lem1637646 m) (@lem1637645 m)). Qed.
Lemma lem1637648 (m : nat) (n : nat) : term78 m n.
Proof. exact (@lem1637647 m n). Qed.
Lemma lem1637649 (n : nat) (m : nat) : (term78 m n) = ((Peano.le m n) = (term79 n m)).
Proof. exact (eq_refl (term78 m n)). Qed.
Lemma lem1637656 (n : nat) (m : nat) : (Peano.le m n) = (term79 n m).
Proof. exact (EQ_MP (@lem1637649 n m) (@lem1637648 m n)). Qed.
Lemma lem1637663 (x : real) : (term80 x) = (term80 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1637664 (x : real) (n : nat) (m : nat) : (term81 x m n) = (term82 x n m).
Proof. exact (MK_COMB (@lem1637663 x) (@lem1637656 n m)). Qed.
Lemma lem1637667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1637668 (x : real) (n : nat) (m : nat) : (term83 x m n) = (term84 x n m).
Proof. exact (MK_COMB (@lem1637667) (@lem1637664 x n m)). Qed.
Lemma lem1637669 (m : nat) (x : real) (n : nat) : (term85 m x n) = (term85 m x n).
Proof. exact (eq_refl (term85 m x n)). Qed.
Lemma lem1637670 (m : nat) (x : real) (n : nat) : (term86 m x n) = (term87 m x n).
Proof. exact (MK_COMB (@lem1637668 x n m) (@lem1637669 m x n)). Qed.
Lemma lem1637673 (m : nat) (x : real) (n : nat) : (term87 m x n) = (term86 m x n).
Proof. exact (SYM (@lem1637670 m x n)). Qed.
Lemma lem1637674 (x : real) (n : nat) (m : nat) (h1 : term82 x n m) : term82 x n m.
Proof. exact (h1). Qed.
Lemma lem1637675 (n : nat) (m : nat) (h1 : term79 n m) : term79 n m.
Proof. exact (h1). Qed.
Lemma lem1637676 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1637677 (n : nat) (m : nat) (h1 : term79 n m) : term79 n m.
Proof. exact (h1). Qed.
Lemma lem1637678 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1637679 (m : nat) (x : real) : (term88 m x) = (term88 m x).
Proof. exact (eq_refl (term88 m x)). Qed.
Lemma lem1637680 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term89 m x n) = (term90 x m d).
Proof. exact (MK_COMB (@lem1637679 m x) (@lem1637678 n m d h1)). Qed.
Lemma lem1637681 (x : real) (m : nat) (d : nat) : (term90 x m d) = (term91 x m d).
Proof. exact (eq_refl (term90 x m d)). Qed.
Lemma lem1637682 (m : nat) (x : real) (n : nat) : (term92 m x n) = (term92 m x n).
Proof. exact (eq_refl (term92 m x n)). Qed.
Lemma lem1637683 (n : nat) (x : real) (m : nat) (d : nat) : ((term89 m x n) = (term90 x m d)) = ((term89 m x n) = (term91 x m d)).
Proof. exact (MK_COMB (@lem1637682 m x n) (@lem1637681 x m d)). Qed.
Lemma lem1637684 (m : nat) (x : real) (n : nat) : (term89 m x n) = (term85 m x n).
Proof. exact (eq_refl (term89 m x n)). Qed.
Lemma lem1637685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1637686 (m : nat) (x : real) (n : nat) : (term92 m x n) = (term93 m x n).
Proof. exact (MK_COMB (@lem1637685) (@lem1637684 m x n)). Qed.
Lemma lem1637687 (x : real) (m : nat) (d : nat) : (term91 x m d) = (term91 x m d).
Proof. exact (eq_refl (term91 x m d)). Qed.
Lemma lem1637688 (n : nat) (x : real) (m : nat) (d : nat) : ((term89 m x n) = (term91 x m d)) = ((term85 m x n) = (term91 x m d)).
Proof. exact (MK_COMB (@lem1637686 m x n) (@lem1637687 x m d)). Qed.
Lemma lem1637689 (n : nat) (x : real) (m : nat) (d : nat) : ((term89 m x n) = (term90 x m d)) = ((term85 m x n) = (term91 x m d)).
Proof. exact (TRANS (@lem1637683 n x m d) (@lem1637688 n x m d)). Qed.
Lemma lem1637690 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term85 m x n) = (term91 x m d).
Proof. exact (EQ_MP (@lem1637689 n x m d) (@lem1637680 x n m d h1)). Qed.
Lemma lem1637691 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term91 x m d) = (term85 m x n).
Proof. exact (SYM (@lem1637690 x n m d h1)). Qed.
Lemma lem1637693 (m : nat) (x : real) (n : nat) : (term74 x m n) = (term75 m x n).
Proof. exact (EQ_MP (@lem1637643 m x n) (@lem1637642 m x n)). Qed.
Lemma lem1637694 (m : nat) (x : real) (d : nat) : (term74 x m d) = (term75 m x d).
Proof. exact (@lem1637693 m x d). Qed.
Lemma lem1637695 (x : real) (m : nat) : (term94 x m) = (term94 x m).
Proof. exact (eq_refl (term94 x m)). Qed.
Lemma lem1637696 (m : nat) (x : real) (d : nat) : (term91 x m d) = (term95 m x d).
Proof. exact (MK_COMB (@lem1637695 x m) (@lem1637694 m x d)). Qed.
Lemma lem1637697 (x : real) (m : nat) (d : nat) : (term95 m x d) = (term91 x m d).
Proof. exact (SYM (@lem1637696 m x d)). Qed.
Lemma lem1637699 (x : real) : x = (term63 x).
Proof. exact (EQ_MP (@lem1637634 x) (@lem1637633 x)). Qed.
Lemma lem1637700 (x : real) (m : nat) : (real_pow x m) = (term96 x m).
Proof. exact (@lem1637699 (real_pow x m)). Qed.
Lemma lem1637701 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1637702 (x : real) (m : nat) : (term94 x m) = (term97 x m).
Proof. exact (MK_COMB (@lem1637701) (@lem1637700 x m)). Qed.
Lemma lem1637703 (m : nat) (x : real) (d : nat) : (term75 m x d) = (term75 m x d).
Proof. exact (eq_refl (term75 m x d)). Qed.
Lemma lem1637704 (m : nat) (x : real) (d : nat) : (term95 m x d) = (term98 m x d).
Proof. exact (MK_COMB (@lem1637702 x m) (@lem1637703 m x d)). Qed.
Lemma lem1637705 (m : nat) (x : real) (d : nat) : (term98 m x d) = (term95 m x d).
Proof. exact (SYM (@lem1637704 m x d)). Qed.
Lemma lem1637707 (y : real) (x : real) (z : real) : term54 y x z.
Proof. exact (EQ_MP (@lem1637621 y x z) (@lem1637620 y x z)). Qed.
Lemma lem1637708 (m : nat) (x : real) (d : nat) : term99 m x d.
Proof. exact (@lem1637707 term100 (real_pow x m) (real_pow x d)). Qed.
Lemma lem1637710 (x : real) (z : real) : term42 x z.
Proof. exact (EQ_MP (@lem1637591 x z) (@lem1637590 x z)). Qed.
Lemma lem1637711 (x : real) (m : nat) : term101 x m.
Proof. exact (@lem1637710 term102 (real_pow x m)). Qed.
Lemma lem1637715 (m : nat) (n : nat) : (term30 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1637563 m n) (@lem1637562 m n)). Qed.
Lemma lem1637716 : term103 = term104.
Proof. exact (@lem1637715 (NUMERAL 0) term105). Qed.
Lemma lem1637718 (m : nat) (n : nat) : (term26 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1637246 m n) (@lem1637245 m n)). Qed.
Lemma lem1637719 : term104 = term106.
Proof. exact (@lem1637718 0 (BIT1 0)). Qed.
Lemma lem1637721 (n : nat) : (term21 n) = True.
Proof. exact (EQ_MP (@lem1637226 n) (@lem1637225 n)). Qed.
Lemma lem1637722 : term106 = True.
Proof. exact (@lem1637721 0). Qed.
Lemma lem1637723 : term104 = True.
Proof. exact (TRANS (@lem1637719) (@lem1637722)). Qed.
Lemma lem1637724 : term103 = True.
Proof. exact (TRANS (@lem1637716) (@lem1637723)). Qed.
Lemma lem1637725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1637726 : term107 = (and True).
Proof. exact (MK_COMB (@lem1637725) (@lem1637724)). Qed.
Lemma lem1637727 (x : real) (m : nat) : (term6 x m) = (term6 x m).
Proof. exact (eq_refl (term6 x m)). Qed.
Lemma lem1637728 (x : real) (m : nat) : (term108 x m) = (term109 x m).
Proof. exact (MK_COMB (@lem1637726) (@lem1637727 x m)). Qed.
Lemma lem1637730 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1637731 (x : real) (m : nat) : (term109 x m) = (term6 x m).
Proof. exact (@lem1637730 (term6 x m)). Qed.
Lemma lem1637732 (x : real) (m : nat) : (term108 x m) = (term6 x m).
Proof. exact (TRANS (@lem1637728 x m) (@lem1637731 x m)). Qed.
Lemma lem1637733 (x : real) (m : nat) : (term6 x m) = (term108 x m).
Proof. exact (SYM (@lem1637732 x m)). Qed.
Lemma lem1637735 (x : real) (n : nat) : term4 x n.
Proof. exact (EQ_MP (@lem1636913 x n) (@lem1636912 x n)). Qed.
Lemma lem1637736 (x : real) (m : nat) : term4 x m.
Proof. exact (@lem1637735 x m). Qed.
Lemma lem1637737 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1637740 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1637737 x) (@lem1637676 x h1)). Qed.
Lemma lem1637741 (x : real) (h1 : term5 x) : True = (term5 x).
Proof. exact (SYM (@lem1637740 x h1)). Qed.
Lemma lem1637742 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (EQ_MP (@lem1637741 x h1) (@lem0)). Qed.
Lemma lem1637743 (m : nat) (x : real) (h1 : term5 x) : term6 x m.
Proof. exact (@lem1637736 x m (@lem1637742 x h1)). Qed.
Lemma lem1637744 (m : nat) (x : real) (h1 : term5 x) : term108 x m.
Proof. exact (EQ_MP (@lem1637733 x m) (@lem1637743 m x h1)). Qed.
Lemma lem1637745 (m : nat) (x : real) (h1 : term5 x) : term110 x m.
Proof. exact (ex_intro (term111 x m) term100 (@lem1637744 m x h1)). Qed.
Lemma lem1637746 (m : nat) (x : real) (h1 : term5 x) : term112 x m.
Proof. exact (@lem1637711 x m (@lem1637745 m x h1)). Qed.
Lemma lem1637748 (x : real) (n : nat) : term4 x n.
Proof. exact (EQ_MP (@lem1636890 x n) (@lem1636889 x n)). Qed.
Lemma lem1637749 (x : real) (d : nat) : term4 x d.
Proof. exact (@lem1637748 x d). Qed.
Lemma lem1637750 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1637753 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1637750 x) (@lem1637676 x h1)). Qed.
Lemma lem1637754 (x : real) (h1 : term5 x) : True = (term5 x).
Proof. exact (SYM (@lem1637753 x h1)). Qed.
Lemma lem1637755 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (EQ_MP (@lem1637754 x h1) (@lem0)). Qed.
Lemma lem1637756 (d : nat) (x : real) (h1 : term5 x) : term6 x d.
Proof. exact (@lem1637749 x d (@lem1637755 x h1)). Qed.
Lemma lem1637757 (m : nat) (d : nat) (x : real) (h1 : term5 x) : term113 m x d.
Proof. exact (conj (@lem1637746 m x h1) (@lem1637756 d x h1)). Qed.
Lemma lem1637758 (m : nat) (d : nat) (x : real) (h1 : term5 x) : term98 m x d.
Proof. exact (@lem1637708 m x d (@lem1637757 m d x h1)). Qed.
Lemma lem1637759 (m : nat) (d : nat) (x : real) (h1 : term5 x) : term95 m x d.
Proof. exact (EQ_MP (@lem1637705 m x d) (@lem1637758 m d x h1)). Qed.
Lemma lem1637760 (m : nat) (d : nat) (x : real) (h1 : term5 x) : term91 x m d.
Proof. exact (EQ_MP (@lem1637697 x m d) (@lem1637759 m d x h1)). Qed.
Lemma lem1637761 (n : nat) (m : nat) (d : nat) (x : real) (h1 : n = (Nat.add m d)) (h2 : term5 x) : term85 m x n.
Proof. exact (EQ_MP (@lem1637691 x n m d h1) (@lem1637760 m d x h2)). Qed.
Lemma lem1637762 (n : nat) (m : nat) (x : real) (h1 : term79 n m) (h2 : term5 x) : term85 m x n.
Proof. exact (ex_elim (@lem1637677 n m h1) (fun d : nat => fun h0 : term114 n m d => @lem1637761 n m d x h0 h2)). Qed.
Lemma lem1637763 (m : nat) (n : nat) (x : real) (h1 : term5 x) : term115 m x n.
Proof. exact (fun h0 : term79 n m => @lem1637762 n m x h0 h1). Qed.
Lemma lem1637764 (x : real) (n : nat) (m : nat) (h1 : term82 x n m) : term79 n m.
Proof. exact (proj2 (@lem1637674 x n m h1)). Qed.
Lemma lem1637765 (x : real) (n : nat) (m : nat) (h1 : term82 x n m) : term5 x.
Proof. exact (proj1 (@lem1637674 x n m h1)). Qed.
Lemma lem1637766 (n : nat) (m : nat) (x : real) (h1 : term79 n m) (h2 : term5 x) : term85 m x n.
Proof. exact (@lem1637763 m n x h2 (@lem1637675 n m h1)). Qed.
Lemma lem1637767 (n : nat) (m : nat) (x : real) (h1 : term79 n m) (h2 : term5 x) : (term5 x) = (term85 m x n).
Proof. exact (prop_ext (fun h3 : term5 x => @lem1637766 n m x h1 h2) (fun h3 : term85 m x n => @lem1637676 x h2)). Qed.
Lemma lem1637768 (n : nat) (m : nat) (x : real) (h1 : term79 n m) (h2 : term5 x) : term85 m x n.
Proof. exact (EQ_MP (@lem1637767 n m x h1 h2) (@lem1637676 x h2)). Qed.
Lemma lem1637769 (n : nat) (m : nat) (x : real) (h1 : term82 x n m) (h2 : term5 x) : (term79 n m) = (term85 m x n).
Proof. exact (prop_ext (fun h3 : term79 n m => @lem1637768 n m x h3 h2) (fun h3 : term85 m x n => @lem1637764 x n m h1)). Qed.
Lemma lem1637770 (n : nat) (m : nat) (x : real) (h1 : term82 x n m) (h2 : term5 x) : term85 m x n.
Proof. exact (EQ_MP (@lem1637769 n m x h1 h2) (@lem1637764 x n m h1)). Qed.
Lemma lem1637771 (x : real) (n : nat) (m : nat) (h1 : term82 x n m) : (term5 x) = (term85 m x n).
Proof. exact (prop_ext (fun h2 : term5 x => @lem1637770 n m x h1 h2) (fun h2 : term85 m x n => @lem1637765 x n m h1)). Qed.
Lemma lem1637772 (x : real) (n : nat) (m : nat) (h1 : term82 x n m) : term85 m x n.
Proof. exact (EQ_MP (@lem1637771 x n m h1) (@lem1637765 x n m h1)). Qed.
Lemma lem1637773 (m : nat) (x : real) (n : nat) : term87 m x n.
Proof. exact (fun h0 : term82 x n m => @lem1637772 x n m h0). Qed.
Lemma lem1637774 (m : nat) (x : real) (n : nat) : term86 m x n.
Proof. exact (EQ_MP (@lem1637673 m x n) (@lem1637773 m x n)). Qed.
Lemma lem1637779 (m : nat) (n : nat) : term116 m n.
Proof. exact (fun x : real => @lem1637774 m x n). Qed.
Lemma lem1637784 (m : nat) : term117 m.
Proof. exact (fun n : nat => @lem1637779 m n). Qed.
Lemma lem1637789 : term118.
Proof. exact (fun m : nat => @lem1637784 m). Qed.
