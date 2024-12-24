Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_MUL_WELLDEFR_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_AC_spec.
Require Import HREAL_ADD_RDISTRIB_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import treal_eq_spec.
Require Import treal_mul_spec.
Lemma lem1333562 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1333563 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1333564 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1333563 x) (@lem1333562 x)). Qed.
Lemma lem1333565 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1333564 x y). Qed.
Lemma lem1333566 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1333571 (m : hreal) (n : hreal) (p : hreal) (h1 : (term3 m n p) = (term4 m n p)) : (term3 m n p) = (term4 m n p).
Proof. exact (h1). Qed.
Lemma lem1333572 (m : hreal) (n : hreal) (p : hreal) (h1 : (term3 m n p) = (term4 m n p)) : (term4 m n p) = (term3 m n p).
Proof. exact (SYM (@lem1333571 m n p h1)). Qed.
Lemma lem1333573 (m : hreal) (n : hreal) (p : hreal) (h1 : (term4 m n p) = (term3 m n p)) : (term4 m n p) = (term3 m n p).
Proof. exact (h1). Qed.
Lemma lem1333574 (m : hreal) (n : hreal) (p : hreal) (h1 : (term4 m n p) = (term3 m n p)) : (term3 m n p) = (term4 m n p).
Proof. exact (SYM (@lem1333573 m n p h1)). Qed.
Lemma lem1333575 (m : hreal) (n : hreal) (p : hreal) : ((term3 m n p) = (term4 m n p)) = ((term4 m n p) = (term3 m n p)).
Proof. exact (prop_ext (fun h1 : (term3 m n p) = (term4 m n p) => @lem1333572 m n p h1) (fun h1 : (term4 m n p) = (term3 m n p) => @lem1333574 m n p h1)). Qed.
Lemma lem1333576 (m : hreal) (n : hreal) : (term5 m n) = (term6 m n).
Proof. exact (fun_ext (fun p : hreal => @lem1333575 m n p)). Qed.
Lemma lem1333577 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333578 (m : hreal) (n : hreal) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem1333577) (@lem1333576 m n)). Qed.
Lemma lem1333579 (m : hreal) : (term9 m) = (term10 m).
Proof. exact (fun_ext (fun n : hreal => @lem1333578 m n)). Qed.
Lemma lem1333580 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333581 (m : hreal) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem1333580) (@lem1333579 m)). Qed.
Lemma lem1333582 : term13 = term14.
Proof. exact (fun_ext (fun m : hreal => @lem1333581 m)). Qed.
Lemma lem1333583 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333584 : term15 = term16.
Proof. exact (MK_COMB (@lem1333583) (@lem1333582)). Qed.
Lemma lem1333585 : term16.
Proof. exact (EQ_MP (@lem1333584) (@lem1321767)). Qed.
Lemma lem1333586 (m : hreal) : term17 m.
Proof. exact (@lem1333585 m). Qed.
Lemma lem1333587 (m : hreal) : (term17 m) = (term12 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1333588 (m : hreal) : term12 m.
Proof. exact (EQ_MP (@lem1333587 m) (@lem1333586 m)). Qed.
Lemma lem1333589 (m : hreal) (n : hreal) : term18 m n.
Proof. exact (@lem1333588 m n). Qed.
Lemma lem1333590 (m : hreal) (n : hreal) : (term18 m n) = (term8 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1333591 (m : hreal) (n : hreal) : term8 m n.
Proof. exact (EQ_MP (@lem1333590 m n) (@lem1333589 m n)). Qed.
Lemma lem1333592 (m : hreal) (n : hreal) (p : hreal) : term19 m n p.
Proof. exact (@lem1333591 m n p). Qed.
Lemma lem1333593 (m : hreal) (n : hreal) (p : hreal) : (term19 m n p) = ((term4 m n p) = (term3 m n p)).
Proof. exact (eq_refl (term19 m n p)). Qed.
Lemma lem1333595 {A : Type'} (x : A) : term20 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1333596 {A : Type'} (x : A) : (term20 A x) = ((x = x) = True).
Proof. exact (eq_refl (term20 A x)). Qed.
Lemma lem1333598 (n : hreal) (m : hreal) (p : hreal) : term21 n m p.
Proof. exact (proj2 (@lem1322003 n m p)). Qed.
Lemma lem1333605 (m : hreal) (n : hreal) (p : hreal) : (term22 m n p) = (term23 m n p).
Proof. exact (proj1 (@lem1333598 n m p)). Qed.
Lemma lem1333606 (a : hreal) (b : hreal) (c : hreal) (d : hreal) : (term24 a b c d) = (term25 a b c d).
Proof. exact (@lem1333605 a b (hreal_add c d)). Qed.
Lemma lem1333622 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333623 (a : hreal) (b : hreal) (c : hreal) (d : hreal) : (term26 a b c d) = (term27 a b c d).
Proof. exact (MK_COMB (@lem1333622) (@lem1333606 a b c d)). Qed.
Lemma lem1333625 (m : hreal) (n : hreal) (p : hreal) : (term22 m n p) = (term23 m n p).
Proof. exact (proj1 (@lem1333598 n m p)). Qed.
Lemma lem1333626 (a : hreal) (d : hreal) (b : hreal) (c : hreal) : (term24 a d b c) = (term25 a d b c).
Proof. exact (@lem1333625 a d (hreal_add b c)). Qed.
Lemma lem1333634 (n : hreal) (m : hreal) (p : hreal) : (term23 m n p) = (term23 n m p).
Proof. exact (proj2 (@lem1333598 n m p)). Qed.
Lemma lem1333635 (b : hreal) (d : hreal) (c : hreal) : (term23 d b c) = (term23 b d c).
Proof. exact (@lem1333634 b d c). Qed.
Lemma lem1333643 (n : hreal) (m : hreal) : (hreal_add m n) = (hreal_add n m).
Proof. exact (proj1 (@lem1322003 n m (@el hreal))). Qed.
Lemma lem1333644 (c : hreal) (d : hreal) : (hreal_add d c) = (hreal_add c d).
Proof. exact (@lem1333643 c d). Qed.
Lemma lem1333648 (b : hreal) : (hreal_add b) = (hreal_add b).
Proof. exact (eq_refl (hreal_add b)). Qed.
Lemma lem1333649 (b : hreal) (c : hreal) (d : hreal) : (term23 b d c) = (term23 b c d).
Proof. exact (MK_COMB (@lem1333648 b) (@lem1333644 c d)). Qed.
Lemma lem1333656 (b : hreal) (c : hreal) (d : hreal) : (term23 d b c) = (term23 b c d).
Proof. exact (TRANS (@lem1333635 b d c) (@lem1333649 b c d)). Qed.
Lemma lem1333657 (a : hreal) : (hreal_add a) = (hreal_add a).
Proof. exact (eq_refl (hreal_add a)). Qed.
Lemma lem1333658 (a : hreal) (b : hreal) (c : hreal) (d : hreal) : (term25 a d b c) = (term25 a b c d).
Proof. exact (MK_COMB (@lem1333657 a) (@lem1333656 b c d)). Qed.
Lemma lem1333665 (a : hreal) (b : hreal) (c : hreal) (d : hreal) : (term24 a d b c) = (term25 a b c d).
Proof. exact (TRANS (@lem1333626 a d b c) (@lem1333658 a b c d)). Qed.
Lemma lem1333666 (a : hreal) (b : hreal) (c : hreal) (d : hreal) : ((term24 a b c d) = (term24 a d b c)) = ((term25 a b c d) = (term25 a b c d)).
Proof. exact (MK_COMB (@lem1333623 a b c d) (@lem1333665 a b c d)). Qed.
Lemma lem1333668 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1333596 A x) (@lem1333595 A x)). Qed.
Lemma lem1333669 (x : hreal) : (x = x) = True.
Proof. exact (@lem1333668 hreal x). Qed.
Lemma lem1333670 (a : hreal) (b : hreal) (c : hreal) (d : hreal) : ((term25 a b c d) = (term25 a b c d)) = True.
Proof. exact (@lem1333669 (term25 a b c d)). Qed.
Lemma lem1333671 (a : hreal) (d : hreal) (b : hreal) (c : hreal) : ((term24 a b c d) = (term24 a d b c)) = True.
Proof. exact (TRANS (@lem1333666 a b c d) (@lem1333670 a b c d)). Qed.
Lemma lem1333672 (a : hreal) (d : hreal) (b : hreal) (c : hreal) : True = ((term24 a b c d) = (term24 a d b c)).
Proof. exact (SYM (@lem1333671 a d b c)). Qed.
Lemma lem1333674 (x1 : hreal) : term28 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1333675 (x1 : hreal) : (term28 x1) = (term29 x1).
Proof. exact (eq_refl (term28 x1)). Qed.
Lemma lem1333676 (x1 : hreal) : term29 x1.
Proof. exact (EQ_MP (@lem1333675 x1) (@lem1333674 x1)). Qed.
Lemma lem1333677 (x1 : hreal) (y2 : hreal) : term30 x1 y2.
Proof. exact (@lem1333676 x1 y2). Qed.
Lemma lem1333678 (x1 : hreal) (y2 : hreal) : (term30 x1 y2) = (term31 x1 y2).
Proof. exact (eq_refl (term30 x1 y2)). Qed.
Lemma lem1333679 (x1 : hreal) (y2 : hreal) : term31 x1 y2.
Proof. exact (EQ_MP (@lem1333678 x1 y2) (@lem1333677 x1 y2)). Qed.
Lemma lem1333680 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term32 x1 y2 x2.
Proof. exact (@lem1333679 x1 y2 x2). Qed.
Lemma lem1333681 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term32 x1 y2 x2) = (term33 x1 y2 x2).
Proof. exact (eq_refl (term32 x1 y2 x2)). Qed.
Lemma lem1333682 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term33 x1 y2 x2.
Proof. exact (EQ_MP (@lem1333681 x1 y2 x2) (@lem1333680 x1 y2 x2)). Qed.
Lemma lem1333683 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term34 x1 y2 x2 y1.
Proof. exact (@lem1333682 x1 y2 x2 y1). Qed.
Lemma lem1333684 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term34 x1 y2 x2 y1) = ((term35 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term34 x1 y2 x2 y1)). Qed.
Lemma lem1333686 (x1 : hreal) : term36 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1333687 (x1 : hreal) : (term36 x1) = (term37 x1).
Proof. exact (eq_refl (term36 x1)). Qed.
Lemma lem1333688 (x1 : hreal) : term37 x1.
Proof. exact (EQ_MP (@lem1333687 x1) (@lem1333686 x1)). Qed.
Lemma lem1333689 (x1 : hreal) (y2 : hreal) : term38 x1 y2.
Proof. exact (@lem1333688 x1 y2). Qed.
Lemma lem1333690 (x1 : hreal) (y2 : hreal) : (term38 x1 y2) = (term39 x1 y2).
Proof. exact (eq_refl (term38 x1 y2)). Qed.
Lemma lem1333691 (x1 : hreal) (y2 : hreal) : term39 x1 y2.
Proof. exact (EQ_MP (@lem1333690 x1 y2) (@lem1333689 x1 y2)). Qed.
Lemma lem1333692 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term40 x1 y2 y1.
Proof. exact (@lem1333691 x1 y2 y1). Qed.
Lemma lem1333693 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term40 x1 y2 y1) = (term41 x1 y2 y1).
Proof. exact (eq_refl (term40 x1 y2 y1)). Qed.
Lemma lem1333694 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term41 x1 y2 y1.
Proof. exact (EQ_MP (@lem1333693 x1 y2 y1) (@lem1333692 x1 y2 y1)). Qed.
Lemma lem1333695 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term42 x1 y2 y1 x2.
Proof. exact (@lem1333694 x1 y2 y1 x2). Qed.
Lemma lem1333696 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term42 x1 y2 y1 x2) = ((term43 x1 y1 x2 y2) = (term44 x1 y2 y1 x2)).
Proof. exact (eq_refl (term42 x1 y2 y1 x2)). Qed.
Lemma lem1333698 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term45 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1333699 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term45 _5106 _5107 P) = ((term46 _5106 _5107 P) = (term47 _5106 _5107 P)).
Proof. exact (eq_refl (term45 _5106 _5107 P)). Qed.
Lemma lem1333706 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term46 _5106 _5107 P) = (term47 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1333699 _5106 _5107 P) (@lem1333698 _5106 _5107 P)). Qed.
Lemma lem1333707 (P : type1233) : (term48 P) = (term49 P).
Proof. exact (@lem1333706 hreal hreal P). Qed.
Lemma lem1333708 : term50 = term51.
Proof. exact (@lem1333707 term52). Qed.
Lemma lem1333709 (x1 : prod hreal hreal) : (term53 x1) = (term54 x1).
Proof. exact (eq_refl (term53 x1)). Qed.
Lemma lem1333710 : term55 = term52.
Proof. exact (fun_ext (fun x1 : prod hreal hreal => @lem1333709 x1)). Qed.
Lemma lem1333711 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1333712 : term50 = term56.
Proof. exact (MK_COMB (@lem1333711) (@lem1333710)). Qed.
Lemma lem1333713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1333714 : term57 = term58.
Proof. exact (MK_COMB (@lem1333713) (@lem1333712)). Qed.
Lemma lem1333715 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = (term60 p1 p2).
Proof. exact (eq_refl (term59 p1 p2)). Qed.
Lemma lem1333716 (p1 : hreal) : (term61 p1) = (term62 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1333715 p1 p2)). Qed.
Lemma lem1333717 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333718 (p1 : hreal) : (term63 p1) = (term64 p1).
Proof. exact (MK_COMB (@lem1333717) (@lem1333716 p1)). Qed.
Lemma lem1333719 : term65 = term66.
Proof. exact (fun_ext (fun p1 : hreal => @lem1333718 p1)). Qed.
Lemma lem1333720 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333721 : term51 = term67.
Proof. exact (MK_COMB (@lem1333720) (@lem1333719)). Qed.
Lemma lem1333722 : (term50 = term51) = (term56 = term67).
Proof. exact (MK_COMB (@lem1333714) (@lem1333721)). Qed.
Lemma lem1333723 : term56 = term67.
Proof. exact (EQ_MP (@lem1333722) (@lem1333708)). Qed.
Lemma lem1333741 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term46 _5106 _5107 P) = (term47 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1333699 _5106 _5107 P) (@lem1333698 _5106 _5107 P)). Qed.
Lemma lem1333742 (P : type1233) : (term48 P) = (term49 P).
Proof. exact (@lem1333741 hreal hreal P). Qed.
Lemma lem1333743 (p1 : hreal) (p2 : hreal) : (term68 p1 p2) = (term69 p1 p2).
Proof. exact (@lem1333742 (term70 p1 p2)). Qed.
Lemma lem1333744 (p1 : hreal) (p2 : hreal) (x2 : prod hreal hreal) : (term71 p1 p2 x2) = (term72 p1 p2 x2).
Proof. exact (eq_refl (term71 p1 p2 x2)). Qed.
Lemma lem1333745 (p1 : hreal) (p2 : hreal) : (term73 p1 p2) = (term70 p1 p2).
Proof. exact (fun_ext (fun x2 : prod hreal hreal => @lem1333744 p1 p2 x2)). Qed.
Lemma lem1333746 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1333747 (p1 : hreal) (p2 : hreal) : (term68 p1 p2) = (term60 p1 p2).
Proof. exact (MK_COMB (@lem1333746) (@lem1333745 p1 p2)). Qed.
Lemma lem1333748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1333749 (p1 : hreal) (p2 : hreal) : (term74 p1 p2) = (term75 p1 p2).
Proof. exact (MK_COMB (@lem1333748) (@lem1333747 p1 p2)). Qed.
Lemma lem1333750 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term76 p1 p2 p1' p2') = (term77 p1 p2 p1' p2').
Proof. exact (eq_refl (term76 p1 p2 p1' p2')). Qed.
Lemma lem1333751 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term78 p1 p2 p1') = (term79 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1333750 p1 p2 p1' p2')). Qed.
Lemma lem1333752 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333753 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term80 p1 p2 p1') = (term81 p1 p2 p1').
Proof. exact (MK_COMB (@lem1333752) (@lem1333751 p1 p2 p1')). Qed.
Lemma lem1333754 (p1 : hreal) (p2 : hreal) : (term82 p1 p2) = (term83 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1333753 p1 p2 p1')). Qed.
Lemma lem1333755 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333756 (p1 : hreal) (p2 : hreal) : (term69 p1 p2) = (term84 p1 p2).
Proof. exact (MK_COMB (@lem1333755) (@lem1333754 p1 p2)). Qed.
Lemma lem1333757 (p1 : hreal) (p2 : hreal) : ((term68 p1 p2) = (term69 p1 p2)) = ((term60 p1 p2) = (term84 p1 p2)).
Proof. exact (MK_COMB (@lem1333749 p1 p2) (@lem1333756 p1 p2)). Qed.
Lemma lem1333758 (p1 : hreal) (p2 : hreal) : (term60 p1 p2) = (term84 p1 p2).
Proof. exact (EQ_MP (@lem1333757 p1 p2) (@lem1333743 p1 p2)). Qed.
Lemma lem1333776 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term46 _5106 _5107 P) = (term47 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1333699 _5106 _5107 P) (@lem1333698 _5106 _5107 P)). Qed.
Lemma lem1333777 (P : type1233) : (term48 P) = (term49 P).
Proof. exact (@lem1333776 hreal hreal P). Qed.
Lemma lem1333778 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term85 p1 p2 p1' p2') = (term86 p1 p2 p1' p2').
Proof. exact (@lem1333777 (term87 p1 p2 p1' p2')). Qed.
Lemma lem1333779 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (y : prod hreal hreal) : (term88 p1 p2 p1' p2' y) = (term89 p1 p2 p1' p2' y).
Proof. exact (eq_refl (term88 p1 p2 p1' p2' y)). Qed.
Lemma lem1333780 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term90 p1 p2 p1' p2') = (term87 p1 p2 p1' p2').
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1333779 p1 p2 p1' p2' y)). Qed.
Lemma lem1333781 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1333782 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term85 p1 p2 p1' p2') = (term77 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1333781) (@lem1333780 p1 p2 p1' p2')). Qed.
Lemma lem1333783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1333784 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term91 p1 p2 p1' p2') = (term92 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1333783) (@lem1333782 p1 p2 p1' p2')). Qed.
Lemma lem1333785 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term93 p1 p2 p1' p2' p1'' p2'') = (term94 p1 p2 p1' p2' p1'' p2'').
Proof. exact (eq_refl (term93 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1333786 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term95 p1 p2 p1' p2' p1'') = (term96 p1 p2 p1' p2' p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1333785 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1333787 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333788 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term97 p1 p2 p1' p2' p1'') = (term98 p1 p2 p1' p2' p1'').
Proof. exact (MK_COMB (@lem1333787) (@lem1333786 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1333789 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term99 p1 p2 p1' p2') = (term100 p1 p2 p1' p2').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1333788 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1333790 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333791 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term86 p1 p2 p1' p2') = (term101 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1333790) (@lem1333789 p1 p2 p1' p2')). Qed.
Lemma lem1333792 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : ((term85 p1 p2 p1' p2') = (term86 p1 p2 p1' p2')) = ((term77 p1 p2 p1' p2') = (term101 p1 p2 p1' p2')).
Proof. exact (MK_COMB (@lem1333784 p1 p2 p1' p2') (@lem1333791 p1 p2 p1' p2')). Qed.
Lemma lem1333793 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term77 p1 p2 p1' p2') = (term101 p1 p2 p1' p2').
Proof. exact (EQ_MP (@lem1333792 p1 p2 p1' p2') (@lem1333778 p1 p2 p1' p2')). Qed.
Lemma lem1333809 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term35 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1333684 x1 y2 x2 y1) (@lem1333683 x1 y2 x2 y1)). Qed.
Lemma lem1333810 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term35 p1 p2 p1' p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1333809 p1 p2' p1' p2). Qed.
Lemma lem1333813 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1333814 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term102 p1 p2 p1' p2') = (term103 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1333813) (@lem1333810 p1 p2' p1' p2)). Qed.
Lemma lem1333816 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term43 x1 y1 x2 y2) = (term44 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1333696 x1 y2 y1 x2) (@lem1333695 x1 y2 y1 x2)). Qed.
Lemma lem1333817 (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term43 p1 p2 p1'' p2'') = (term44 p1 p2'' p2 p1'').
Proof. exact (@lem1333816 p1 p2'' p2 p1''). Qed.
Lemma lem1333818 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1333819 (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term104 p1 p2 p1'' p2'') = (term105 p1 p2'' p2 p1'').
Proof. exact (MK_COMB (@lem1333818) (@lem1333817 p1 p2'' p2 p1'')). Qed.
Lemma lem1333821 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term43 x1 y1 x2 y2) = (term44 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1333696 x1 y2 y1 x2) (@lem1333695 x1 y2 y1 x2)). Qed.
Lemma lem1333822 (p1' : hreal) (p2'' : hreal) (p2' : hreal) (p1'' : hreal) : (term43 p1' p2' p1'' p2'') = (term44 p1' p2'' p2' p1'').
Proof. exact (@lem1333821 p1' p2'' p2' p1''). Qed.
Lemma lem1333823 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p2' : hreal) (p1'' : hreal) : (term106 p1 p2 p1' p2' p1'' p2'') = (term107 p1 p2 p1' p2'' p2' p1'').
Proof. exact (MK_COMB (@lem1333819 p1 p2'' p2 p1'') (@lem1333822 p1' p2'' p2' p1'')). Qed.
Lemma lem1333825 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term35 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1333684 x1 y2 x2 y1) (@lem1333683 x1 y2 x2 y1)). Qed.
Lemma lem1333826 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term107 p1 p2 p1' p2'' p2' p1'') = ((term108 p1 p2 p1' p2'' p2' p1'') = (term108 p1' p2' p1 p2'' p2 p1'')).
Proof. exact (@lem1333825 (term109 p1 p1'' p2 p2'') (term109 p1' p2'' p2' p1'') (term109 p1' p1'' p2' p2'') (term109 p1 p2'' p2 p1'')). Qed.
Lemma lem1333829 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term106 p1 p2 p1' p2' p1'' p2'') = ((term108 p1 p2 p1' p2'' p2' p1'') = (term108 p1' p2' p1 p2'' p2 p1'')).
Proof. exact (TRANS (@lem1333823 p1 p2 p1' p2'' p2' p1'') (@lem1333826 p1' p2' p1 p2'' p2 p1'')). Qed.
Lemma lem1333830 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term94 p1 p2 p1' p2' p1'' p2'') = (term110 p1' p2' p1 p2'' p2 p1'').
Proof. exact (MK_COMB (@lem1333814 p1 p2' p1' p2) (@lem1333829 p1' p2' p1 p2'' p2 p1'')). Qed.
Lemma lem1333835 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term96 p1 p2 p1' p2' p1'') = (term111 p1' p2' p1 p2 p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1333830 p1' p2' p1 p2'' p2 p1'')). Qed.
Lemma lem1333836 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333837 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term98 p1 p2 p1' p2' p1'') = (term112 p1' p2' p1 p2 p1'').
Proof. exact (MK_COMB (@lem1333836) (@lem1333835 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1333844 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term100 p1 p2 p1' p2') = (term113 p1' p2' p1 p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1333837 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1333845 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333846 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term101 p1 p2 p1' p2') = (term114 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1333845) (@lem1333844 p1' p2' p1 p2)). Qed.
Lemma lem1333853 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term77 p1 p2 p1' p2') = (term114 p1' p2' p1 p2).
Proof. exact (TRANS (@lem1333793 p1 p2 p1' p2') (@lem1333846 p1' p2' p1 p2)). Qed.
Lemma lem1333854 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term79 p1 p2 p1') = (term115 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1333853 p1' p2' p1 p2)). Qed.
Lemma lem1333855 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333856 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term81 p1 p2 p1') = (term116 p1' p1 p2).
Proof. exact (MK_COMB (@lem1333855) (@lem1333854 p1' p1 p2)). Qed.
Lemma lem1333863 (p1 : hreal) (p2 : hreal) : (term83 p1 p2) = (term117 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1333856 p1' p1 p2)). Qed.
Lemma lem1333864 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333865 (p1 : hreal) (p2 : hreal) : (term84 p1 p2) = (term118 p1 p2).
Proof. exact (MK_COMB (@lem1333864) (@lem1333863 p1 p2)). Qed.
Lemma lem1333872 (p1 : hreal) (p2 : hreal) : (term60 p1 p2) = (term118 p1 p2).
Proof. exact (TRANS (@lem1333758 p1 p2) (@lem1333865 p1 p2)). Qed.
Lemma lem1333873 (p1 : hreal) : (term62 p1) = (term119 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1333872 p1 p2)). Qed.
Lemma lem1333874 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333875 (p1 : hreal) : (term64 p1) = (term120 p1).
Proof. exact (MK_COMB (@lem1333874) (@lem1333873 p1)). Qed.
Lemma lem1333882 : term66 = term121.
Proof. exact (fun_ext (fun p1 : hreal => @lem1333875 p1)). Qed.
Lemma lem1333883 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333884 : term67 = term122.
Proof. exact (MK_COMB (@lem1333883) (@lem1333882)). Qed.
Lemma lem1333891 : term56 = term122.
Proof. exact (TRANS (@lem1333723) (@lem1333884)). Qed.
Lemma lem1333892 : term122 = term56.
Proof. exact (SYM (@lem1333891)). Qed.
Lemma lem1333902 (a : hreal) (d : hreal) (b : hreal) (c : hreal) : (term24 a b c d) = (term24 a d b c).
Proof. exact (EQ_MP (@lem1333672 a d b c) (@lem0)). Qed.
Lemma lem1333903 (p1 : hreal) (p2' : hreal) (p1'' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term108 p1 p2 p1' p2'' p2' p1'') = (term123 p1 p2' p1'' p2 p1' p2'').
Proof. exact (@lem1333902 (hreal_mul p1 p1'') (hreal_mul p2' p1'') (hreal_mul p2 p2'') (hreal_mul p1' p2'')). Qed.
Lemma lem1333904 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333905 (p1 : hreal) (p2' : hreal) (p1'' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term124 p1 p2 p1' p2'' p2' p1'') = (term125 p1 p2' p1'' p2 p1' p2'').
Proof. exact (MK_COMB (@lem1333904) (@lem1333903 p1 p2' p1'' p2 p1' p2'')). Qed.
Lemma lem1333907 (a : hreal) (d : hreal) (b : hreal) (c : hreal) : (term24 a b c d) = (term24 a d b c).
Proof. exact (EQ_MP (@lem1333672 a d b c) (@lem0)). Qed.
Lemma lem1333908 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term108 p1' p2' p1 p2'' p2 p1'') = (term123 p1' p2 p1'' p2' p1 p2'').
Proof. exact (@lem1333907 (hreal_mul p1' p1'') (hreal_mul p2 p1'') (hreal_mul p2' p2'') (hreal_mul p1 p2'')). Qed.
Lemma lem1333909 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : ((term108 p1 p2 p1' p2'' p2' p1'') = (term108 p1' p2' p1 p2'' p2 p1'')) = ((term123 p1 p2' p1'' p2 p1' p2'') = (term123 p1' p2 p1'' p2' p1 p2'')).
Proof. exact (MK_COMB (@lem1333905 p1 p2' p1'' p2 p1' p2'') (@lem1333908 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333910 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term103 p1 p2' p1' p2) = (term103 p1 p2' p1' p2).
Proof. exact (eq_refl (term103 p1 p2' p1' p2)). Qed.
Lemma lem1333911 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term110 p1' p2' p1 p2'' p2 p1'') = (term126 p1' p2 p1'' p2' p1 p2'').
Proof. exact (MK_COMB (@lem1333910 p1 p2' p1' p2) (@lem1333909 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333912 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term126 p1' p2 p1'' p2' p1 p2'') = (term110 p1' p2' p1 p2'' p2 p1'').
Proof. exact (SYM (@lem1333911 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333922 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (term3 m n p).
Proof. exact (EQ_MP (@lem1333593 m n p) (@lem1333592 m n p)). Qed.
Lemma lem1333923 (p1 : hreal) (p2' : hreal) (p1'' : hreal) : (term4 p1 p2' p1'') = (term3 p1 p2' p1'').
Proof. exact (@lem1333922 p1 p2' p1''). Qed.
Lemma lem1333924 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1333925 (p1 : hreal) (p2' : hreal) (p1'' : hreal) : (term127 p1 p2' p1'') = (term128 p1 p2' p1'').
Proof. exact (MK_COMB (@lem1333924) (@lem1333923 p1 p2' p1'')). Qed.
Lemma lem1333927 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (term3 m n p).
Proof. exact (EQ_MP (@lem1333593 m n p) (@lem1333592 m n p)). Qed.
Lemma lem1333928 (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term4 p2 p1' p2'') = (term3 p2 p1' p2'').
Proof. exact (@lem1333927 p2 p1' p2''). Qed.
Lemma lem1333929 (p1 : hreal) (p2' : hreal) (p1'' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term123 p1 p2' p1'' p2 p1' p2'') = (term129 p1 p2' p1'' p2 p1' p2'').
Proof. exact (MK_COMB (@lem1333925 p1 p2' p1'') (@lem1333928 p2 p1' p2'')). Qed.
Lemma lem1333932 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333933 (p1 : hreal) (p2' : hreal) (p1'' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term125 p1 p2' p1'' p2 p1' p2'') = (term130 p1 p2' p1'' p2 p1' p2'').
Proof. exact (MK_COMB (@lem1333932) (@lem1333929 p1 p2' p1'' p2 p1' p2'')). Qed.
Lemma lem1333935 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (term3 m n p).
Proof. exact (EQ_MP (@lem1333593 m n p) (@lem1333592 m n p)). Qed.
Lemma lem1333936 (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term4 p1' p2 p1'') = (term3 p1' p2 p1'').
Proof. exact (@lem1333935 p1' p2 p1''). Qed.
Lemma lem1333937 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1333938 (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term127 p1' p2 p1'') = (term128 p1' p2 p1'').
Proof. exact (MK_COMB (@lem1333937) (@lem1333936 p1' p2 p1'')). Qed.
Lemma lem1333940 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = (term3 m n p).
Proof. exact (EQ_MP (@lem1333593 m n p) (@lem1333592 m n p)). Qed.
Lemma lem1333941 (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term4 p2' p1 p2'') = (term3 p2' p1 p2'').
Proof. exact (@lem1333940 p2' p1 p2''). Qed.
Lemma lem1333942 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term123 p1' p2 p1'' p2' p1 p2'') = (term129 p1' p2 p1'' p2' p1 p2'').
Proof. exact (MK_COMB (@lem1333938 p1' p2 p1'') (@lem1333941 p2' p1 p2'')). Qed.
Lemma lem1333945 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : ((term123 p1 p2' p1'' p2 p1' p2'') = (term123 p1' p2 p1'' p2' p1 p2'')) = ((term129 p1 p2' p1'' p2 p1' p2'') = (term129 p1' p2 p1'' p2' p1 p2'')).
Proof. exact (MK_COMB (@lem1333933 p1 p2' p1'' p2 p1' p2'') (@lem1333942 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333948 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term103 p1 p2' p1' p2) = (term103 p1 p2' p1' p2).
Proof. exact (eq_refl (term103 p1 p2' p1' p2)). Qed.
Lemma lem1333949 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term126 p1' p2 p1'' p2' p1 p2'') = (term131 p1' p2 p1'' p2' p1 p2'').
Proof. exact (MK_COMB (@lem1333948 p1 p2' p1' p2) (@lem1333945 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333954 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term131 p1' p2 p1'' p2' p1 p2'') = (term126 p1' p2 p1'' p2' p1 p2'').
Proof. exact (SYM (@lem1333949 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333955 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p1 p2') = (hreal_add p1' p2).
Proof. exact (h1). Qed.
Lemma lem1333959 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p1 p2') = (hreal_add p1' p2).
Proof. exact (h1). Qed.
Lemma lem1333960 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1333961 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term132 p1 p2') = (term132 p1' p2).
Proof. exact (MK_COMB (@lem1333960) (@lem1333959 p1 p2' p1' p2 h1)). Qed.
Lemma lem1333962 (p1'' : hreal) : p1'' = p1''.
Proof. exact (eq_refl p1''). Qed.
Lemma lem1333963 (p1'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term3 p1 p2' p1'') = (term3 p1' p2 p1'').
Proof. exact (MK_COMB (@lem1333961 p1 p2' p1' p2 h1) (@lem1333962 p1'')). Qed.
Lemma lem1333964 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1333965 (p1'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term128 p1 p2' p1'') = (term128 p1' p2 p1'').
Proof. exact (MK_COMB (@lem1333964) (@lem1333963 p1'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1333966 (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term3 p2 p1' p2'') = (term3 p2 p1' p2'').
Proof. exact (eq_refl (term3 p2 p1' p2'')). Qed.
Lemma lem1333967 (p1'' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term129 p1 p2' p1'' p2 p1' p2'') = (term133 p1'' p2 p1' p2'').
Proof. exact (MK_COMB (@lem1333965 p1'' p1 p2' p1' p2 h1) (@lem1333966 p2 p1' p2'')). Qed.
Lemma lem1333968 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333969 (p1'' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term130 p1 p2' p1'' p2 p1' p2'') = (term134 p1'' p2 p1' p2'').
Proof. exact (MK_COMB (@lem1333968) (@lem1333967 p1'' p2'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1333970 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term129 p1' p2 p1'' p2' p1 p2'') = (term129 p1' p2 p1'' p2' p1 p2'').
Proof. exact (eq_refl (term129 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333971 (p1'' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : ((term129 p1 p2' p1'' p2 p1' p2'') = (term129 p1' p2 p1'' p2' p1 p2'')) = ((term133 p1'' p2 p1' p2'') = (term129 p1' p2 p1'' p2' p1 p2'')).
Proof. exact (MK_COMB (@lem1333969 p1'' p2'' p1 p2' p1' p2 h1) (@lem1333970 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1333974 (p1'' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : ((term133 p1'' p2 p1' p2'') = (term129 p1' p2 p1'' p2' p1 p2'')) = ((term129 p1 p2' p1'' p2 p1' p2'') = (term129 p1' p2 p1'' p2' p1 p2'')).
Proof. exact (SYM (@lem1333971 p1'' p2'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1333975 (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term128 p1' p2 p1'') = (term128 p1' p2 p1'').
Proof. exact (eq_refl (term128 p1' p2 p1'')). Qed.
Lemma lem1333979 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1333566 y x) (@lem1333565 x y)). Qed.
Lemma lem1333980 (p1' : hreal) (p2 : hreal) : (hreal_add p2 p1') = (hreal_add p1' p2).
Proof. exact (@lem1333979 p1' p2). Qed.
Lemma lem1333981 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1333982 (p1' : hreal) (p2 : hreal) : (term132 p2 p1') = (term132 p1' p2).
Proof. exact (MK_COMB (@lem1333981) (@lem1333980 p1' p2)). Qed.
Lemma lem1333983 (p2'' : hreal) : p2'' = p2''.
Proof. exact (eq_refl p2''). Qed.
Lemma lem1333984 (p1' : hreal) (p2 : hreal) (p2'' : hreal) : (term3 p2 p1' p2'') = (term3 p1' p2 p2'').
Proof. exact (MK_COMB (@lem1333982 p1' p2) (@lem1333983 p2'')). Qed.
Lemma lem1333985 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333986 (p1' : hreal) (p2 : hreal) (p2'' : hreal) : (term135 p2 p1' p2'') = (term135 p1' p2 p2'').
Proof. exact (MK_COMB (@lem1333985) (@lem1333984 p1' p2 p2'')). Qed.
Lemma lem1333988 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1333566 y x) (@lem1333565 x y)). Qed.
Lemma lem1333989 (p1 : hreal) (p2' : hreal) : (hreal_add p2' p1) = (hreal_add p1 p2').
Proof. exact (@lem1333988 p1 p2'). Qed.
Lemma lem1333990 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1333991 (p1 : hreal) (p2' : hreal) : (term132 p2' p1) = (term132 p1 p2').
Proof. exact (MK_COMB (@lem1333990) (@lem1333989 p1 p2')). Qed.
Lemma lem1333992 (p2'' : hreal) : p2'' = p2''.
Proof. exact (eq_refl p2''). Qed.
Lemma lem1333993 (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term3 p2' p1 p2'') = (term3 p1 p2' p2'').
Proof. exact (MK_COMB (@lem1333991 p1 p2') (@lem1333992 p2'')). Qed.
Lemma lem1333994 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) (p2'' : hreal) : ((term3 p2 p1' p2'') = (term3 p2' p1 p2'')) = ((term3 p1' p2 p2'') = (term3 p1 p2' p2'')).
Proof. exact (MK_COMB (@lem1333986 p1' p2 p2'') (@lem1333993 p1 p2' p2'')). Qed.
Lemma lem1333995 (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : ((term3 p1' p2 p2'') = (term3 p1 p2' p2'')) = ((term3 p2 p1' p2'') = (term3 p2' p1 p2'')).
Proof. exact (SYM (@lem1333994 p1' p2 p1 p2' p2'')). Qed.
Lemma lem1333996 (p1' : hreal) (p2 : hreal) (p2'' : hreal) : (term136 p1' p2 p2'') = (term136 p1' p2 p2'').
Proof. exact (eq_refl (term136 p1' p2 p2'')). Qed.
Lemma lem1333997 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term137 p1' p2 p2'' p1 p2') = (term138 p2'' p1' p2).
Proof. exact (MK_COMB (@lem1333996 p1' p2 p2'') (@lem1333955 p1 p2' p1' p2 h1)). Qed.
Lemma lem1333998 (p1' : hreal) (p2 : hreal) (p2'' : hreal) : (term138 p2'' p1' p2) = ((term3 p1' p2 p2'') = (term3 p1' p2 p2'')).
Proof. exact (eq_refl (term138 p2'' p1' p2)). Qed.
Lemma lem1333999 (p1' : hreal) (p2 : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term139 p1' p2 p2'' p1 p2') = (term139 p1' p2 p2'' p1 p2').
Proof. exact (eq_refl (term139 p1' p2 p2'' p1 p2')). Qed.
Lemma lem1334000 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (p2'' : hreal) : ((term137 p1' p2 p2'' p1 p2') = (term138 p2'' p1' p2)) = ((term137 p1' p2 p2'' p1 p2') = ((term3 p1' p2 p2'') = (term3 p1' p2 p2''))).
Proof. exact (MK_COMB (@lem1333999 p1' p2 p2'' p1 p2') (@lem1333998 p1' p2 p2'')). Qed.
Lemma lem1334001 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term137 p1' p2 p2'' p1 p2') = ((term3 p1' p2 p2'') = (term3 p1 p2' p2'')).
Proof. exact (eq_refl (term137 p1' p2 p2'' p1 p2')). Qed.
Lemma lem1334002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1334003 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term139 p1' p2 p2'' p1 p2') = (term140 p1' p2 p1 p2' p2'').
Proof. exact (MK_COMB (@lem1334002) (@lem1334001 p1' p2 p1 p2' p2'')). Qed.
Lemma lem1334004 (p1' : hreal) (p2 : hreal) (p2'' : hreal) : ((term3 p1' p2 p2'') = (term3 p1' p2 p2'')) = ((term3 p1' p2 p2'') = (term3 p1' p2 p2'')).
Proof. exact (eq_refl ((term3 p1' p2 p2'') = (term3 p1' p2 p2''))). Qed.
Lemma lem1334005 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (p2'' : hreal) : ((term137 p1' p2 p2'' p1 p2') = ((term3 p1' p2 p2'') = (term3 p1' p2 p2''))) = (((term3 p1' p2 p2'') = (term3 p1 p2' p2'')) = ((term3 p1' p2 p2'') = (term3 p1' p2 p2''))).
Proof. exact (MK_COMB (@lem1334003 p1' p2 p1 p2' p2'') (@lem1334004 p1' p2 p2'')). Qed.
Lemma lem1334006 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (p2'' : hreal) : ((term137 p1' p2 p2'' p1 p2') = (term138 p2'' p1' p2)) = (((term3 p1' p2 p2'') = (term3 p1 p2' p2'')) = ((term3 p1' p2 p2'') = (term3 p1' p2 p2''))).
Proof. exact (TRANS (@lem1334000 p1 p2' p1' p2 p2'') (@lem1334005 p1 p2' p1' p2 p2'')). Qed.
Lemma lem1334007 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : ((term3 p1' p2 p2'') = (term3 p1 p2' p2'')) = ((term3 p1' p2 p2'') = (term3 p1' p2 p2'')).
Proof. exact (EQ_MP (@lem1334006 p1 p2' p1' p2 p2'') (@lem1333997 p2'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1334008 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : ((term3 p1' p2 p2'') = (term3 p1' p2 p2'')) = ((term3 p1' p2 p2'') = (term3 p1 p2' p2'')).
Proof. exact (SYM (@lem1334007 p2'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1334009 (p1' : hreal) (p2 : hreal) (p2'' : hreal) : (term3 p1' p2 p2'') = (term3 p1' p2 p2'').
Proof. exact (eq_refl (term3 p1' p2 p2'')). Qed.
Lemma lem1334010 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term3 p1' p2 p2'') = (term3 p1 p2' p2'').
Proof. exact (EQ_MP (@lem1334008 p2'' p1 p2' p1' p2 h1) (@lem1334009 p1' p2 p2'')). Qed.
Lemma lem1334011 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term3 p2 p1' p2'') = (term3 p2' p1 p2'').
Proof. exact (EQ_MP (@lem1333995 p2 p1' p2' p1 p2'') (@lem1334010 p2'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1334012 (p1'' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term133 p1'' p2 p1' p2'') = (term129 p1' p2 p1'' p2' p1 p2'').
Proof. exact (MK_COMB (@lem1333975 p1' p2 p1'') (@lem1334011 p2'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1334013 (p1'' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term129 p1 p2' p1'' p2 p1' p2'') = (term129 p1' p2 p1'' p2' p1 p2'').
Proof. exact (EQ_MP (@lem1333974 p1'' p2'' p1 p2' p1' p2 h1) (@lem1334012 p1'' p2'' p1 p2' p1' p2 h1)). Qed.
Lemma lem1334014 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : term131 p1' p2 p1'' p2' p1 p2''.
Proof. exact (fun h0 : (hreal_add p1 p2') = (hreal_add p1' p2) => @lem1334013 p1'' p2'' p1 p2' p1' p2 h0). Qed.
Lemma lem1334015 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) : term126 p1' p2 p1'' p2' p1 p2''.
Proof. exact (EQ_MP (@lem1333954 p1' p2 p1'' p2' p1 p2'') (@lem1334014 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1334016 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : term110 p1' p2' p1 p2'' p2 p1''.
Proof. exact (EQ_MP (@lem1333912 p1' p2' p1 p2'' p2 p1'') (@lem1334015 p1' p2 p1'' p2' p1 p2'')). Qed.
Lemma lem1334021 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : term112 p1' p2' p1 p2 p1''.
Proof. exact (fun p2'' : hreal => @lem1334016 p1' p2' p1 p2'' p2 p1''). Qed.
Lemma lem1334026 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : term114 p1' p2' p1 p2.
Proof. exact (fun p1'' : hreal => @lem1334021 p1' p2' p1 p2 p1''). Qed.
Lemma lem1334031 (p1' : hreal) (p1 : hreal) (p2 : hreal) : term116 p1' p1 p2.
Proof. exact (fun p2' : hreal => @lem1334026 p1' p2' p1 p2). Qed.
Lemma lem1334036 (p1 : hreal) (p2 : hreal) : term118 p1 p2.
Proof. exact (fun p1' : hreal => @lem1334031 p1' p1 p2). Qed.
Lemma lem1334041 (p1 : hreal) : term120 p1.
Proof. exact (fun p2 : hreal => @lem1334036 p1 p2). Qed.
Lemma lem1334046 : term122.
Proof. exact (fun p1 : hreal => @lem1334041 p1). Qed.
Lemma lem1334047 : term56.
Proof. exact (EQ_MP (@lem1333892) (@lem1334046)). Qed.
