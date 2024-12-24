Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import NOT_LE_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm19490_spec.
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
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
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
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5470572 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5470573 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5470574 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5470573 t1) (@lem5470572 t1)). Qed.
Lemma lem5470575 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5470574 t1 t2). Qed.
Lemma lem5470576 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5470577 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5470576 t1 t2) (@lem5470575 t1 t2)). Qed.
Lemma lem5470578 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5470577 t1 t2 t3). Qed.
Lemma lem5470579 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5470580 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5470579 t1 t2 t3) (@lem5470578 t1 t2 t3)). Qed.
Lemma lem5470581 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5470580 t1 t2 t3)). Qed.
Lemma lem5470582 (m : nat) : term7 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5470583 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem5470584 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem5470583 m) (@lem5470582 m)). Qed.
Lemma lem5470585 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem5470584 m n). Qed.
Lemma lem5470586 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem5470587 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem5470586 m n) (@lem5470585 m n)). Qed.
Lemma lem5470588 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem5470587 m n p). Qed.
Lemma lem5470589 (m : nat) (p : nat) (n : nat) : (term11 m n p) = ((term12 p m n) = (term13 m p n)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem5470591 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5470592 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem5470593 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem5470592 A s) (@lem5470591 A s)). Qed.
Lemma lem5470594 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem5470593 A s t). Qed.
Lemma lem5470595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((@SUBSET A s t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem5470600 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term17 A s t).
Proof. exact (EQ_MP (@lem5470595 A s t) (@lem5470594 A s t)). Qed.
Lemma lem5470601 (s : nat -> Prop) (t : nat -> Prop) : (@SUBSET nat s t) = (term18 s t).
Proof. exact (@lem5470600 nat s t). Qed.
Lemma lem5470602 (m : nat) (n : nat) (p : nat) (q : nat) : (term19 m n p q) = (term20 m n p q).
Proof. exact (@lem5470601 (dotdot m n) (dotdot p q)). Qed.
Lemma lem5470610 (m : nat) (p : nat) (n : nat) : (term12 p m n) = (term13 m p n).
Proof. exact (EQ_MP (@lem5470589 m p n) (@lem5470588 m n p)). Qed.
Lemma lem5470611 (m : nat) (x : nat) (n : nat) : (term12 x m n) = (term13 m x n).
Proof. exact (@lem5470610 m x n). Qed.
Lemma lem5470614 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5470615 (m : nat) (x : nat) (n : nat) : (term21 x m n) = (term22 m x n).
Proof. exact (MK_COMB (@lem5470614) (@lem5470611 m x n)). Qed.
Lemma lem5470617 (m : nat) (p : nat) (n : nat) : (term12 p m n) = (term13 m p n).
Proof. exact (EQ_MP (@lem5470589 m p n) (@lem5470588 m n p)). Qed.
Lemma lem5470618 (p : nat) (x : nat) (q : nat) : (term12 x p q) = (term13 p x q).
Proof. exact (@lem5470617 p x q). Qed.
Lemma lem5470621 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term23 m n x p q) = (term24 m n p x q).
Proof. exact (MK_COMB (@lem5470615 m x n) (@lem5470618 p x q)). Qed.
Lemma lem5470624 (m : nat) (n : nat) (p : nat) (q : nat) : (term25 m n p q) = (term26 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5470621 m n p x q)). Qed.
Lemma lem5470625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470626 (m : nat) (n : nat) (p : nat) (q : nat) : (term20 m n p q) = (term27 m n p q).
Proof. exact (MK_COMB (@lem5470625) (@lem5470624 m n p q)). Qed.
Lemma lem5470631 (m : nat) (n : nat) (p : nat) (q : nat) : (term19 m n p q) = (term27 m n p q).
Proof. exact (TRANS (@lem5470602 m n p q) (@lem5470626 m n p q)). Qed.
Lemma lem5470632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5470633 (m : nat) (n : nat) (p : nat) (q : nat) : (term28 m n p q) = (term29 m n p q).
Proof. exact (MK_COMB (@lem5470632) (@lem5470631 m n p q)). Qed.
Lemma lem5470638 (p : nat) (m : nat) (n : nat) (q : nat) : (term30 p m n q) = (term30 p m n q).
Proof. exact (eq_refl (term30 p m n q)). Qed.
Lemma lem5470639 (p : nat) (m : nat) (n : nat) (q : nat) : ((term19 m n p q) = (term30 p m n q)) = ((term27 m n p q) = (term30 p m n q)).
Proof. exact (MK_COMB (@lem5470633 m n p q) (@lem5470638 p m n q)). Qed.
Lemma lem5470642 (p : nat) (m : nat) (n : nat) (q : nat) : ((term27 m n p q) = (term30 p m n q)) = ((term19 m n p q) = (term30 p m n q)).
Proof. exact (SYM (@lem5470639 p m n q)). Qed.
Lemma lem5470644 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5470645 (p : nat) (m : nat) (n : nat) (q : nat) : (term32 p m n q) = (term33 p m n q).
Proof. exact (@lem5470644 (term32 p m n q)). Qed.
Lemma lem5470646 (p : nat) (m : nat) (n : nat) (q : nat) : (term33 p m n q) = (term32 p m n q).
Proof. exact (SYM (@lem5470645 p m n q)). Qed.
Lemma lem5470647 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term34 p m n q.
Proof. exact (h1). Qed.
Lemma lem5470650 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term35 p m n q) : term35 p m n q.
Proof. exact (h1). Qed.
Lemma lem5470651 (p : nat) (m : nat) (n : nat) (q : nat) : term36 p m n q.
Proof. exact (fun h0 : term35 p m n q => @lem5470650 p m n q h0). Qed.
Lemma lem5470652 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term36 p m n q) : term36 p m n q.
Proof. exact (h1). Qed.
Lemma lem5470653 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term35 p m n q) : term35 p m n q.
Proof. exact (h1). Qed.
Lemma lem5470654 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term35 p m n q) (h2 : term36 p m n q) : term35 p m n q.
Proof. exact (@lem5470652 p m n q h2 (@lem5470653 p m n q h1)). Qed.
Lemma lem5470655 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term35 p m n q) : term37 p m n q.
Proof. exact (fun h0 : term36 p m n q => @lem5470654 p m n q h1 h0). Qed.
Lemma lem5470656 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term36 p m n q) : term36 p m n q.
Proof. exact (h1). Qed.
Lemma lem5470657 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term35 p m n q) (h2 : term36 p m n q) : term35 p m n q.
Proof. exact (@lem5470655 p m n q h1 (@lem5470656 p m n q h2)). Qed.
Lemma lem5470658 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term36 p m n q) : term36 p m n q.
Proof. exact (fun h0 : term35 p m n q => @lem5470657 p m n q h0 h1). Qed.
Lemma lem5470659 (p : nat) (m : nat) (n : nat) (q : nat) : term38 p m n q.
Proof. exact (fun h0 : term36 p m n q => @lem5470658 p m n q h0). Qed.
Lemma lem5470662 (p : nat) (m : nat) (n : nat) (q : nat) : term36 p m n q.
Proof. exact (@lem5470659 p m n q (@lem5470651 p m n q)). Qed.
Lemma lem5470714 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5470715 : term39 = term40.
Proof. exact (@lem5470714 term41). Qed.
Lemma lem5470732 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem5470733 : term43 = term44.
Proof. exact (MK_COMB (@lem5470732) (@lem5470715)). Qed.
Lemma lem5470736 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem5470737 : term46 = term47.
Proof. exact (MK_COMB (@lem5470736) (@lem5470733)). Qed.
Lemma lem5470740 (p : nat) (m : nat) (n : nat) (q : nat) : (term48 p m n q) = (term48 p m n q).
Proof. exact (eq_refl (term48 p m n q)). Qed.
Lemma lem5470741 (p : nat) (m : nat) (n : nat) (q : nat) : (term35 p m n q) = (term49 p m n q).
Proof. exact (MK_COMB (@lem5470740 p m n q) (@lem5470737)). Qed.
Lemma lem5470744 (m : nat) (n : nat) (q : nat) : (term50 m n q) = (term51 m n q).
Proof. exact (fun_ext (fun p : nat => @lem5470741 p m n q)). Qed.
Lemma lem5470745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470746 (m : nat) (n : nat) (q : nat) : (term52 m n q) = (term53 m n q).
Proof. exact (MK_COMB (@lem5470745) (@lem5470744 m n q)). Qed.
Lemma lem5470751 (n : nat) (q : nat) : (term54 n q) = (term55 n q).
Proof. exact (fun_ext (fun m : nat => @lem5470746 m n q)). Qed.
Lemma lem5470752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470753 (n : nat) (q : nat) : (term56 n q) = (term57 n q).
Proof. exact (MK_COMB (@lem5470752) (@lem5470751 n q)). Qed.
Lemma lem5470758 (q : nat) : (term58 q) = (term59 q).
Proof. exact (fun_ext (fun n : nat => @lem5470753 n q)). Qed.
Lemma lem5470759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470760 (q : nat) : (term60 q) = (term61 q).
Proof. exact (MK_COMB (@lem5470759) (@lem5470758 q)). Qed.
Lemma lem5470765 : term62 = term63.
Proof. exact (fun_ext (fun q : nat => @lem5470760 q)). Qed.
Lemma lem5470766 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470775 : term64 = term65.
Proof. exact (MK_COMB (@lem5470766) (@lem5470765)). Qed.
Lemma lem5470784 (n : nat) (m : nat) (p : nat) : (term66 n m p) = (term66 n m p).
Proof. exact (eq_refl (term66 n m p)). Qed.
Lemma lem5470785 (n : nat) (m : nat) : (term67 n m) = (term67 n m).
Proof. exact (fun_ext (fun p : nat => @lem5470784 n m p)). Qed.
Lemma lem5470786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470787 (n : nat) (m : nat) : (term68 n m) = (term68 n m).
Proof. exact (MK_COMB (@lem5470786) (@lem5470785 n m)). Qed.
Lemma lem5470788 (m : nat) : (term69 m) = (term69 m).
Proof. exact (fun_ext (fun n : nat => @lem5470787 n m)). Qed.
Lemma lem5470789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470790 (m : nat) : (term70 m) = (term70 m).
Proof. exact (MK_COMB (@lem5470789) (@lem5470788 m)). Qed.
Lemma lem5470791 : term71 = term71.
Proof. exact (fun_ext (fun m : nat => @lem5470790 m)). Qed.
Lemma lem5470792 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470793 : term41 = term41.
Proof. exact (MK_COMB (@lem5470792) (@lem5470791)). Qed.
Lemma lem5470794 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5470795 : term40 = term40.
Proof. exact (MK_COMB (@lem5470794) (@lem5470793)). Qed.
Lemma lem5470802 (n : nat) (m : nat) : ((term72 m n) = (Peano.lt n m)) = ((term72 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term72 m n) = (Peano.lt n m))). Qed.
Lemma lem5470803 (m : nat) : (term73 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem5470802 n m)). Qed.
Lemma lem5470804 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470805 (m : nat) : (term74 m) = (term74 m).
Proof. exact (MK_COMB (@lem5470804) (@lem5470803 m)). Qed.
Lemma lem5470806 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem5470805 m)). Qed.
Lemma lem5470807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470808 : term76 = term76.
Proof. exact (MK_COMB (@lem5470807) (@lem5470806)). Qed.
Lemma lem5470809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5470810 : term42 = term42.
Proof. exact (MK_COMB (@lem5470809) (@lem5470808)). Qed.
Lemma lem5470811 : term44 = term44.
Proof. exact (MK_COMB (@lem5470810) (@lem5470795)). Qed.
Lemma lem5470812 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5470813 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem5470812 n)). Qed.
Lemma lem5470814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470815 : term78 = term78.
Proof. exact (MK_COMB (@lem5470814) (@lem5470813)). Qed.
Lemma lem5470816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5470817 : term45 = term45.
Proof. exact (MK_COMB (@lem5470816) (@lem5470815)). Qed.
Lemma lem5470818 : term47 = term47.
Proof. exact (MK_COMB (@lem5470817) (@lem5470811)). Qed.
Lemma lem5470827 (p : nat) (m : nat) (n : nat) (q : nat) : (term30 p m n q) = (term30 p m n q).
Proof. exact (eq_refl (term30 p m n q)). Qed.
Lemma lem5470840 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term24 m n p x q) = (term24 m n p x q).
Proof. exact (eq_refl (term24 m n p x q)). Qed.
Lemma lem5470841 (m : nat) (n : nat) (p : nat) (q : nat) : (term26 m n p q) = (term26 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5470840 m n p x q)). Qed.
Lemma lem5470842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470843 (m : nat) (n : nat) (p : nat) (q : nat) : (term27 m n p q) = (term27 m n p q).
Proof. exact (MK_COMB (@lem5470842) (@lem5470841 m n p q)). Qed.
Lemma lem5470844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5470845 (m : nat) (n : nat) (p : nat) (q : nat) : (term79 m n p q) = (term79 m n p q).
Proof. exact (MK_COMB (@lem5470844) (@lem5470843 m n p q)). Qed.
Lemma lem5470846 (p : nat) (m : nat) (n : nat) (q : nat) : (term32 p m n q) = (term32 p m n q).
Proof. exact (MK_COMB (@lem5470845 m n p q) (@lem5470827 p m n q)). Qed.
Lemma lem5470847 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5470848 (p : nat) (m : nat) (n : nat) (q : nat) : (term34 p m n q) = (term34 p m n q).
Proof. exact (MK_COMB (@lem5470847) (@lem5470846 p m n q)). Qed.
Lemma lem5470849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5470850 (p : nat) (m : nat) (n : nat) (q : nat) : (term48 p m n q) = (term48 p m n q).
Proof. exact (MK_COMB (@lem5470849) (@lem5470848 p m n q)). Qed.
Lemma lem5470851 (p : nat) (m : nat) (n : nat) (q : nat) : (term49 p m n q) = (term49 p m n q).
Proof. exact (MK_COMB (@lem5470850 p m n q) (@lem5470818)). Qed.
Lemma lem5470852 (m : nat) (n : nat) (q : nat) : (term51 m n q) = (term51 m n q).
Proof. exact (fun_ext (fun p : nat => @lem5470851 p m n q)). Qed.
Lemma lem5470853 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470854 (m : nat) (n : nat) (q : nat) : (term53 m n q) = (term53 m n q).
Proof. exact (MK_COMB (@lem5470853) (@lem5470852 m n q)). Qed.
Lemma lem5470855 (n : nat) (q : nat) : (term55 n q) = (term55 n q).
Proof. exact (fun_ext (fun m : nat => @lem5470854 m n q)). Qed.
Lemma lem5470856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470857 (n : nat) (q : nat) : (term57 n q) = (term57 n q).
Proof. exact (MK_COMB (@lem5470856) (@lem5470855 n q)). Qed.
Lemma lem5470858 (q : nat) : (term59 q) = (term59 q).
Proof. exact (fun_ext (fun n : nat => @lem5470857 n q)). Qed.
Lemma lem5470859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470860 (q : nat) : (term61 q) = (term61 q).
Proof. exact (MK_COMB (@lem5470859) (@lem5470858 q)). Qed.
Lemma lem5470861 : term63 = term63.
Proof. exact (fun_ext (fun q : nat => @lem5470860 q)). Qed.
Lemma lem5470862 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470863 : term65 = term65.
Proof. exact (MK_COMB (@lem5470862) (@lem5470861)). Qed.
Lemma lem5470954 : term64 = term65.
Proof. exact (TRANS (@lem5470775) (@lem5470863)). Qed.
Lemma lem5470955 : term65 = term64.
Proof. exact (SYM (@lem5470954)). Qed.
Lemma lem5470956 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term34 p m n q.
Proof. exact (h1). Qed.
Lemma lem5470957 (h1 : term78) : term78.
Proof. exact (h1). Qed.
Lemma lem5470958 (h1 : term76) : term76.
Proof. exact (h1). Qed.
Lemma lem5470966 (m : nat) (x : nat) (n : nat) : (term80 m x n) = (term81 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5470971 (p : nat) (x : nat) (q : nat) : (term13 p x q) = (term13 p x q).
Proof. exact (eq_refl (term13 p x q)). Qed.
Lemma lem5470972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5470973 (m : nat) (x : nat) (n : nat) : (term82 m x n) = (term83 m x n).
Proof. exact (MK_COMB (@lem5470972) (@lem5470966 m x n)). Qed.
Lemma lem5470974 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term84 m n p x q) = (term85 m n p x q).
Proof. exact (MK_COMB (@lem5470973 m x n) (@lem5470971 p x q)). Qed.
Lemma lem5470975 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term24 m n p x q) = (term84 m n p x q).
Proof. exact (@lem17265 (term13 m x n) (term13 p x q)). Qed.
Lemma lem5470976 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term24 m n p x q) = (term85 m n p x q).
Proof. exact (TRANS (@lem5470975 m n p x q) (@lem5470974 m n p x q)). Qed.
Lemma lem5470977 (m : nat) (n : nat) (p : nat) (q : nat) : (term26 m n p q) = (term86 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5470976 m n p x q)). Qed.
Lemma lem5470978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5470979 (m : nat) (n : nat) (p : nat) (q : nat) : (term27 m n p q) = (term87 m n p q).
Proof. exact (MK_COMB (@lem5470978) (@lem5470977 m n p q)). Qed.
Lemma lem5470987 (p : nat) (m : nat) (n : nat) (q : nat) : (term88 p m n q) = (term89 p m n q).
Proof. exact (@lem17045 (Peano.le p m) (Peano.le n q)). Qed.
Lemma lem5470989 (n : nat) (m : nat) : (term90 n m) = (term90 n m).
Proof. exact (eq_refl (term90 n m)). Qed.
Lemma lem5470990 (p : nat) (m : nat) (n : nat) (q : nat) : (term91 p m n q) = (term92 p m n q).
Proof. exact (MK_COMB (@lem5470989 n m) (@lem5470987 p m n q)). Qed.
Lemma lem5470991 (p : nat) (m : nat) (n : nat) (q : nat) : (term93 p m n q) = (term91 p m n q).
Proof. exact (@lem17160 (Peano.lt n m) (term94 p m n q)). Qed.
Lemma lem5470992 (p : nat) (m : nat) (n : nat) (q : nat) : (term93 p m n q) = (term92 p m n q).
Proof. exact (TRANS (@lem5470991 p m n q) (@lem5470990 p m n q)). Qed.
Lemma lem5470993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5470994 (m : nat) (n : nat) (p : nat) (q : nat) : (term95 m n p q) = (term96 m n p q).
Proof. exact (MK_COMB (@lem5470993) (@lem5470979 m n p q)). Qed.
Lemma lem5470995 (p : nat) (m : nat) (n : nat) (q : nat) : (term97 p m n q) = (term98 p m n q).
Proof. exact (MK_COMB (@lem5470994 m n p q) (@lem5470992 p m n q)). Qed.
Lemma lem5470996 (p : nat) (m : nat) (n : nat) (q : nat) : (term34 p m n q) = (term97 p m n q).
Proof. exact (@lem17362 (term27 m n p q) (term30 p m n q)). Qed.
Lemma lem5471049 (p : nat) (m : nat) (n : nat) (q : nat) : (term34 p m n q) = (term98 p m n q).
Proof. exact (TRANS (@lem5470996 p m n q) (@lem5470995 p m n q)). Qed.
Lemma lem5471050 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term98 p m n q.
Proof. exact (EQ_MP (@lem5471049 p m n q) (@lem5470956 p m n q h1)). Qed.
Lemma lem5471051 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5471052 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem5471051 n)). Qed.
Lemma lem5471053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471062 : term78 = term78.
Proof. exact (MK_COMB (@lem5471053) (@lem5471052)). Qed.
Lemma lem5471063 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem5471062) (@lem5470957 h1)). Qed.
Lemma lem5471067 (m : nat) (n : nat) : (term99 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem5471069 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem5471070 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5471071 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (MK_COMB (@lem5471070) (@lem5471067 m n)). Qed.
Lemma lem5471072 (n : nat) (m : nat) : (term102 n m) = (term103 n m).
Proof. exact (MK_COMB (@lem5471071 m n) (@lem5471069 n m)). Qed.
Lemma lem5471077 (n : nat) (m : nat) : (term104 n m) = (term104 n m).
Proof. exact (eq_refl (term104 n m)). Qed.
Lemma lem5471078 (n : nat) (m : nat) : (term105 n m) = (term106 n m).
Proof. exact (MK_COMB (@lem5471077 n m) (@lem5471072 n m)). Qed.
Lemma lem5471079 (n : nat) (m : nat) : ((term72 m n) = (Peano.lt n m)) = (term105 n m).
Proof. exact (@lem17784 (term72 m n) (Peano.lt n m)). Qed.
Lemma lem5471080 (n : nat) (m : nat) : ((term72 m n) = (Peano.lt n m)) = (term106 n m).
Proof. exact (TRANS (@lem5471079 n m) (@lem5471078 n m)). Qed.
Lemma lem5471081 (m : nat) : (term73 m) = (term107 m).
Proof. exact (fun_ext (fun n : nat => @lem5471080 n m)). Qed.
Lemma lem5471082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471083 (m : nat) : (term74 m) = (term108 m).
Proof. exact (MK_COMB (@lem5471082) (@lem5471081 m)). Qed.
Lemma lem5471084 : term75 = term109.
Proof. exact (fun_ext (fun m : nat => @lem5471083 m)). Qed.
Lemma lem5471085 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471086 : term76 = term110.
Proof. exact (MK_COMB (@lem5471085) (@lem5471084)). Qed.
Lemma lem5471092 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5471093 (P : nat -> Prop) (Q : nat -> Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem5471092 nat P Q). Qed.
Lemma lem5471094 (m : nat) : (term115 m) = (term116 m).
Proof. exact (@lem5471093 (term117 m) (term118 m)). Qed.
Lemma lem5471095 (n : nat) (m : nat) : (term119 m n) = (term120 n m).
Proof. exact (eq_refl (term119 m n)). Qed.
Lemma lem5471096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5471097 (n : nat) (m : nat) : (term121 m n) = (term104 n m).
Proof. exact (MK_COMB (@lem5471096) (@lem5471095 n m)). Qed.
Lemma lem5471098 (n : nat) (m : nat) : (term122 m n) = (term103 n m).
Proof. exact (eq_refl (term122 m n)). Qed.
Lemma lem5471099 (n : nat) (m : nat) : (term123 m n) = (term106 n m).
Proof. exact (MK_COMB (@lem5471097 n m) (@lem5471098 n m)). Qed.
Lemma lem5471100 (m : nat) : (term124 m) = (term107 m).
Proof. exact (fun_ext (fun n : nat => @lem5471099 n m)). Qed.
Lemma lem5471101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471102 (m : nat) : (term115 m) = (term108 m).
Proof. exact (MK_COMB (@lem5471101) (@lem5471100 m)). Qed.
Lemma lem5471103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5471104 (m : nat) : (term125 m) = (term126 m).
Proof. exact (MK_COMB (@lem5471103) (@lem5471102 m)). Qed.
Lemma lem5471105 (n : nat) (m : nat) : (term119 m n) = (term120 n m).
Proof. exact (eq_refl (term119 m n)). Qed.
Lemma lem5471106 (m : nat) : (term127 m) = (term117 m).
Proof. exact (fun_ext (fun n : nat => @lem5471105 n m)). Qed.
Lemma lem5471107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471108 (m : nat) : (term128 m) = (term129 m).
Proof. exact (MK_COMB (@lem5471107) (@lem5471106 m)). Qed.
Lemma lem5471109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5471110 (m : nat) : (term130 m) = (term131 m).
Proof. exact (MK_COMB (@lem5471109) (@lem5471108 m)). Qed.
Lemma lem5471111 (n : nat) (m : nat) : (term122 m n) = (term103 n m).
Proof. exact (eq_refl (term122 m n)). Qed.
Lemma lem5471112 (m : nat) : (term132 m) = (term118 m).
Proof. exact (fun_ext (fun n : nat => @lem5471111 n m)). Qed.
Lemma lem5471113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471114 (m : nat) : (term133 m) = (term134 m).
Proof. exact (MK_COMB (@lem5471113) (@lem5471112 m)). Qed.
Lemma lem5471115 (m : nat) : (term116 m) = (term135 m).
Proof. exact (MK_COMB (@lem5471110 m) (@lem5471114 m)). Qed.
Lemma lem5471116 (m : nat) : ((term115 m) = (term116 m)) = ((term108 m) = (term135 m)).
Proof. exact (MK_COMB (@lem5471104 m) (@lem5471115 m)). Qed.
Lemma lem5471117 (m : nat) : (term108 m) = (term135 m).
Proof. exact (EQ_MP (@lem5471116 m) (@lem5471094 m)). Qed.
Lemma lem5471214 : term109 = term136.
Proof. exact (fun_ext (fun m : nat => @lem5471117 m)). Qed.
Lemma lem5471215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471216 : term110 = term137.
Proof. exact (MK_COMB (@lem5471215) (@lem5471214)). Qed.
Lemma lem5471218 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5471219 (P : nat -> Prop) (Q : nat -> Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem5471218 nat P Q). Qed.
Lemma lem5471220 : term138 = term139.
Proof. exact (@lem5471219 term140 term141). Qed.
Lemma lem5471221 (m : nat) : (term142 m) = (term129 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem5471222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5471223 (m : nat) : (term143 m) = (term131 m).
Proof. exact (MK_COMB (@lem5471222) (@lem5471221 m)). Qed.
Lemma lem5471224 (m : nat) : (term144 m) = (term134 m).
Proof. exact (eq_refl (term144 m)). Qed.
Lemma lem5471225 (m : nat) : (term145 m) = (term135 m).
Proof. exact (MK_COMB (@lem5471223 m) (@lem5471224 m)). Qed.
Lemma lem5471226 : term146 = term136.
Proof. exact (fun_ext (fun m : nat => @lem5471225 m)). Qed.
Lemma lem5471227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471228 : term138 = term137.
Proof. exact (MK_COMB (@lem5471227) (@lem5471226)). Qed.
Lemma lem5471229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5471230 : term147 = term148.
Proof. exact (MK_COMB (@lem5471229) (@lem5471228)). Qed.
Lemma lem5471231 (m : nat) : (term142 m) = (term129 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem5471232 : term149 = term140.
Proof. exact (fun_ext (fun m : nat => @lem5471231 m)). Qed.
Lemma lem5471233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471234 : term150 = term151.
Proof. exact (MK_COMB (@lem5471233) (@lem5471232)). Qed.
Lemma lem5471235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5471236 : term152 = term153.
Proof. exact (MK_COMB (@lem5471235) (@lem5471234)). Qed.
Lemma lem5471237 (m : nat) : (term144 m) = (term134 m).
Proof. exact (eq_refl (term144 m)). Qed.
Lemma lem5471238 : term154 = term141.
Proof. exact (fun_ext (fun m : nat => @lem5471237 m)). Qed.
Lemma lem5471239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471240 : term155 = term156.
Proof. exact (MK_COMB (@lem5471239) (@lem5471238)). Qed.
Lemma lem5471241 : term139 = term157.
Proof. exact (MK_COMB (@lem5471236) (@lem5471240)). Qed.
Lemma lem5471242 : (term138 = term139) = (term137 = term157).
Proof. exact (MK_COMB (@lem5471230) (@lem5471241)). Qed.
Lemma lem5471243 : term137 = term157.
Proof. exact (EQ_MP (@lem5471242) (@lem5471220)). Qed.
Lemma lem5471350 : term110 = term157.
Proof. exact (TRANS (@lem5471216) (@lem5471243)). Qed.
Lemma lem5471351 : term76 = term157.
Proof. exact (TRANS (@lem5471086) (@lem5471350)). Qed.
Lemma lem5471352 (h1 : term76) : term157.
Proof. exact (EQ_MP (@lem5471351) (@lem5470958 h1)). Qed.
Lemma lem5471462 (p : nat) (m : nat) (n : nat) (q : nat) : (term92 p m n q) = (term92 p m n q).
Proof. exact (eq_refl (term92 p m n q)). Qed.
Lemma lem5471495 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term85 m n p x q) = (term85 m n p x q).
Proof. exact (eq_refl (term85 m n p x q)). Qed.
Lemma lem5471496 (m : nat) (n : nat) (p : nat) (q : nat) : (term86 m n p q) = (term86 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5471495 m n p x q)). Qed.
Lemma lem5471497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471498 (m : nat) (n : nat) (p : nat) (q : nat) : (term87 m n p q) = (term87 m n p q).
Proof. exact (MK_COMB (@lem5471497) (@lem5471496 m n p q)). Qed.
Lemma lem5471499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5471500 (m : nat) (n : nat) (p : nat) (q : nat) : (term96 m n p q) = (term96 m n p q).
Proof. exact (MK_COMB (@lem5471499) (@lem5471498 m n p q)). Qed.
Lemma lem5471501 (p : nat) (m : nat) (n : nat) (q : nat) : (term98 p m n q) = (term98 p m n q).
Proof. exact (MK_COMB (@lem5471500 m n p q) (@lem5471462 p m n q)). Qed.
Lemma lem5471502 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term98 p m n q.
Proof. exact (EQ_MP (@lem5471501 p m n q) (@lem5471050 p m n q h1)). Qed.
Lemma lem5471507 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5471508 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem5471507 n)). Qed.
Lemma lem5471509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471510 : term78 = term78.
Proof. exact (MK_COMB (@lem5471509) (@lem5471508)). Qed.
Lemma lem5471511 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem5471510) (@lem5471063 h1)). Qed.
Lemma lem5471524 (n : nat) (m : nat) : (term103 n m) = (term103 n m).
Proof. exact (eq_refl (term103 n m)). Qed.
Lemma lem5471525 (m : nat) : (term118 m) = (term118 m).
Proof. exact (fun_ext (fun n : nat => @lem5471524 n m)). Qed.
Lemma lem5471526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471527 (m : nat) : (term134 m) = (term134 m).
Proof. exact (MK_COMB (@lem5471526) (@lem5471525 m)). Qed.
Lemma lem5471528 : term141 = term141.
Proof. exact (fun_ext (fun m : nat => @lem5471527 m)). Qed.
Lemma lem5471529 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471530 : term156 = term156.
Proof. exact (MK_COMB (@lem5471529) (@lem5471528)). Qed.
Lemma lem5471547 (n : nat) (m : nat) : (term120 n m) = (term120 n m).
Proof. exact (eq_refl (term120 n m)). Qed.
Lemma lem5471548 (m : nat) : (term117 m) = (term117 m).
Proof. exact (fun_ext (fun n : nat => @lem5471547 n m)). Qed.
Lemma lem5471549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471550 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem5471549) (@lem5471548 m)). Qed.
Lemma lem5471551 : term140 = term140.
Proof. exact (fun_ext (fun m : nat => @lem5471550 m)). Qed.
Lemma lem5471552 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471553 : term151 = term151.
Proof. exact (MK_COMB (@lem5471552) (@lem5471551)). Qed.
Lemma lem5471554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5471555 : term153 = term153.
Proof. exact (MK_COMB (@lem5471554) (@lem5471553)). Qed.
Lemma lem5471556 : term157 = term157.
Proof. exact (MK_COMB (@lem5471555) (@lem5471530)). Qed.
Lemma lem5471557 (h1 : term76) : term157.
Proof. exact (EQ_MP (@lem5471556) (@lem5471352 h1)). Qed.
Lemma lem5471593 (h1 : term76) : term156.
Proof. exact (proj2 (@lem5471557 h1)). Qed.
Lemma lem5471595 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term92 p m n q.
Proof. exact (proj2 (@lem5471502 p m n q h1)). Qed.
Lemma lem5471596 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term87 m n p q.
Proof. exact (proj1 (@lem5471502 p m n q h1)). Qed.
Lemma lem5471597 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term89 p m n q.
Proof. exact (proj2 (@lem5471595 p m n q h1)). Qed.
Lemma lem5471602 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5471603 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem5471602 n)). Qed.
Lemma lem5471604 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471606 : term78 = term78.
Proof. exact (MK_COMB (@lem5471604) (@lem5471603)). Qed.
Lemma lem5471607 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem5471606) (@lem5471511 h1)). Qed.
Lemma lem5471656 (n : nat) (m : nat) : (term103 n m) = (term103 n m).
Proof. exact (eq_refl (term103 n m)). Qed.
Lemma lem5471657 (m : nat) : (term118 m) = (term118 m).
Proof. exact (fun_ext (fun n : nat => @lem5471656 n m)). Qed.
Lemma lem5471658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471659 (m : nat) : (term134 m) = (term134 m).
Proof. exact (MK_COMB (@lem5471658) (@lem5471657 m)). Qed.
Lemma lem5471660 : term141 = term141.
Proof. exact (fun_ext (fun m : nat => @lem5471659 m)). Qed.
Lemma lem5471661 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471663 : term156 = term156.
Proof. exact (MK_COMB (@lem5471661) (@lem5471660)). Qed.
Lemma lem5471664 (h1 : term76) : term156.
Proof. exact (EQ_MP (@lem5471663) (@lem5471593 h1)). Qed.
Lemma lem5471688 (p : nat) (m : nat) (n : nat) (x : nat) (q : nat) : (term85 m n p x q) = (term158 p m n x q).
Proof. exact (@lem19490 (Peano.le p x) (term81 m x n) (Peano.le x q)). Qed.
Lemma lem5471689 (p : nat) (m : nat) (n : nat) (q : nat) : (term86 m n p q) = (term159 p m n q).
Proof. exact (fun_ext (fun x : nat => @lem5471688 p m n x q)). Qed.
Lemma lem5471690 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471692 (p : nat) (m : nat) (n : nat) (q : nat) : (term87 m n p q) = (term160 p m n q).
Proof. exact (MK_COMB (@lem5471690) (@lem5471689 p m n q)). Qed.
Lemma lem5471693 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term160 p m n q.
Proof. exact (EQ_MP (@lem5471692 p m n q) (@lem5471596 p m n q h1)). Qed.
Lemma lem5471701 (p : nat) (m : nat) (h1 : term72 p m) : term72 p m.
Proof. exact (h1). Qed.
Lemma lem5471703 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5471704 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem5471703 n)). Qed.
Lemma lem5471705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471707 : term78 = term78.
Proof. exact (MK_COMB (@lem5471705) (@lem5471704)). Qed.
Lemma lem5471708 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem5471707) (@lem5471511 h1)). Qed.
Lemma lem5471757 (n : nat) (m : nat) : (term103 n m) = (term103 n m).
Proof. exact (eq_refl (term103 n m)). Qed.
Lemma lem5471758 (m : nat) : (term118 m) = (term118 m).
Proof. exact (fun_ext (fun n : nat => @lem5471757 n m)). Qed.
Lemma lem5471759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471760 (m : nat) : (term134 m) = (term134 m).
Proof. exact (MK_COMB (@lem5471759) (@lem5471758 m)). Qed.
Lemma lem5471761 : term141 = term141.
Proof. exact (fun_ext (fun m : nat => @lem5471760 m)). Qed.
Lemma lem5471762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471764 : term156 = term156.
Proof. exact (MK_COMB (@lem5471762) (@lem5471761)). Qed.
Lemma lem5471765 (h1 : term76) : term156.
Proof. exact (EQ_MP (@lem5471764) (@lem5471593 h1)). Qed.
Lemma lem5471789 (p : nat) (m : nat) (n : nat) (x : nat) (q : nat) : (term85 m n p x q) = (term158 p m n x q).
Proof. exact (@lem19490 (Peano.le p x) (term81 m x n) (Peano.le x q)). Qed.
Lemma lem5471790 (p : nat) (m : nat) (n : nat) (q : nat) : (term86 m n p q) = (term159 p m n q).
Proof. exact (fun_ext (fun x : nat => @lem5471789 p m n x q)). Qed.
Lemma lem5471791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5471793 (p : nat) (m : nat) (n : nat) (q : nat) : (term87 m n p q) = (term160 p m n q).
Proof. exact (MK_COMB (@lem5471791) (@lem5471790 p m n q)). Qed.
Lemma lem5471794 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term160 p m n q.
Proof. exact (EQ_MP (@lem5471793 p m n q) (@lem5471596 p m n q h1)). Qed.
Lemma lem5471802 (n : nat) (q : nat) (h1 : term72 n q) : term72 n q.
Proof. exact (h1). Qed.
Lemma lem5471803 (_70562 : nat) (h1 : term78) : term161 _70562.
Proof. exact (@lem5471607 h1 _70562). Qed.
Lemma lem5471804 (_70562 : nat) : (term161 _70562) = (Peano.le _70562 _70562).
Proof. exact (eq_refl (term161 _70562)). Qed.
Lemma lem5471821 (_70568 : nat) (h1 : term76) : term144 _70568.
Proof. exact (@lem5471664 h1 _70568). Qed.
Lemma lem5471822 (_70568 : nat) : (term144 _70568) = (term134 _70568).
Proof. exact (eq_refl (term144 _70568)). Qed.
Lemma lem5471823 (_70568 : nat) (h1 : term76) : term134 _70568.
Proof. exact (EQ_MP (@lem5471822 _70568) (@lem5471821 _70568 h1)). Qed.
Lemma lem5471824 (_70568 : nat) (_70569 : nat) (h1 : term76) : term122 _70568 _70569.
Proof. exact (@lem5471823 _70568 h1 _70569). Qed.
Lemma lem5471825 (_70569 : nat) (_70568 : nat) : (term122 _70568 _70569) = (term103 _70569 _70568).
Proof. exact (eq_refl (term122 _70568 _70569)). Qed.
Lemma lem5471827 (_70570 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term162 p m n q _70570.
Proof. exact (@lem5471693 p m n q h1 _70570). Qed.
Lemma lem5471828 (p : nat) (m : nat) (n : nat) (_70570 : nat) (q : nat) : (term162 p m n q _70570) = (term158 p m n _70570 q).
Proof. exact (eq_refl (term162 p m n q _70570)). Qed.
Lemma lem5471829 (_70570 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term158 p m n _70570 q.
Proof. exact (EQ_MP (@lem5471828 p m n _70570 q) (@lem5471827 _70570 p m n q h1)). Qed.
Lemma lem5471830 (_70571 : nat) (h1 : term78) : term161 _70571.
Proof. exact (@lem5471708 h1 _70571). Qed.
Lemma lem5471831 (_70571 : nat) : (term161 _70571) = (Peano.le _70571 _70571).
Proof. exact (eq_refl (term161 _70571)). Qed.
Lemma lem5471848 (_70577 : nat) (h1 : term76) : term144 _70577.
Proof. exact (@lem5471765 h1 _70577). Qed.
Lemma lem5471849 (_70577 : nat) : (term144 _70577) = (term134 _70577).
Proof. exact (eq_refl (term144 _70577)). Qed.
Lemma lem5471850 (_70577 : nat) (h1 : term76) : term134 _70577.
Proof. exact (EQ_MP (@lem5471849 _70577) (@lem5471848 _70577 h1)). Qed.
Lemma lem5471851 (_70577 : nat) (_70578 : nat) (h1 : term76) : term122 _70577 _70578.
Proof. exact (@lem5471850 _70577 h1 _70578). Qed.
Lemma lem5471852 (_70578 : nat) (_70577 : nat) : (term122 _70577 _70578) = (term103 _70578 _70577).
Proof. exact (eq_refl (term122 _70577 _70578)). Qed.
Lemma lem5471854 (_70579 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term162 p m n q _70579.
Proof. exact (@lem5471794 p m n q h1 _70579). Qed.
Lemma lem5471855 (p : nat) (m : nat) (n : nat) (_70579 : nat) (q : nat) : (term162 p m n q _70579) = (term158 p m n _70579 q).
Proof. exact (eq_refl (term162 p m n q _70579)). Qed.
Lemma lem5471856 (_70579 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term158 p m n _70579 q.
Proof. exact (EQ_MP (@lem5471855 p m n _70579 q) (@lem5471854 _70579 p m n q h1)). Qed.
Lemma lem5471858 (_70570 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term163 m n p _70570.
Proof. exact (proj1 (@lem5471829 _70570 p m n q h1)). Qed.
Lemma lem5471859 (_70579 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term164 m n _70579 q.
Proof. exact (proj2 (@lem5471856 _70579 p m n q h1)). Qed.
Lemma lem5471886 (_70569 : nat) (_70568 : nat) (h1 : term76) : term103 _70569 _70568.
Proof. exact (EQ_MP (@lem5471825 _70569 _70568) (@lem5471824 _70568 _70569 h1)). Qed.
Lemma lem5471890 (p : nat) (m : nat) (h1 : term72 p m) : term72 p m.
Proof. exact (h1). Qed.
Lemma lem5471901 (m : nat) (n : nat) (p : nat) (_70570 : nat) : (term163 m n p _70570) = (term165 m n p _70570).
Proof. exact (@lem5470581 (term72 m _70570) (term72 _70570 n) (Peano.le p _70570)). Qed.
Lemma lem5471902 (_70570 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term165 m n p _70570.
Proof. exact (EQ_MP (@lem5471901 m n p _70570) (@lem5471858 _70570 p m n q h1)). Qed.
Lemma lem5471940 (_70578 : nat) (_70577 : nat) (h1 : term76) : term103 _70578 _70577.
Proof. exact (EQ_MP (@lem5471852 _70578 _70577) (@lem5471851 _70577 _70578 h1)). Qed.
Lemma lem5471944 (n : nat) (q : nat) (h1 : term72 n q) : term72 n q.
Proof. exact (h1). Qed.
Lemma lem5471967 (m : nat) (n : nat) (_70579 : nat) (q : nat) : (term164 m n _70579 q) = (term166 m n _70579 q).
Proof. exact (@lem5470581 (term72 m _70579) (term72 _70579 n) (Peano.le _70579 q)). Qed.
Lemma lem5471968 (_70579 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term166 m n _70579 q.
Proof. exact (EQ_MP (@lem5471967 m n _70579 q) (@lem5471859 _70579 p m n q h1)). Qed.
Lemma lem5471970 (_70562 : nat) (h1 : term78) : Peano.le _70562 _70562.
Proof. exact (EQ_MP (@lem5471804 _70562) (@lem5471803 _70562 h1)). Qed.
Lemma lem5471971 (m : nat) (h1 : term78) : Peano.le m m.
Proof. exact (@lem5471970 m h1). Qed.
Lemma lem5471972 (m : nat) (h1 : term78) : term167 m.
Proof. exact (fun h0 : term168 m => @lem5471971 m h1). Qed.
Lemma lem5471974 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5471975 (m : nat) : (term167 m) = (Peano.le m m).
Proof. exact (@lem5471974 (Peano.le m m)). Qed.
Lemma lem5471976 (m : nat) (h1 : term78) : Peano.le m m.
Proof. exact (EQ_MP (@lem5471975 m) (@lem5471972 m h1)). Qed.
Lemma lem5471978 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term170 n m.
Proof. exact (proj1 (@lem5471595 p m n q h1)). Qed.
Lemma lem5471979 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term171 n m.
Proof. exact (fun h0 : Peano.lt n m => @lem5471978 p m n q h1). Qed.
Lemma lem5471981 (p : Prop) : (term172 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5471982 (n : nat) (m : nat) : (term171 n m) = (term170 n m).
Proof. exact (@lem5471981 (Peano.lt n m)). Qed.
Lemma lem5471983 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term170 n m.
Proof. exact (EQ_MP (@lem5471982 n m) (@lem5471979 p m n q h1)). Qed.
Lemma lem5471985 (b : Prop) (a : Prop) : (a \/ b) = (term173 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5471988 (_70568 : nat) (_70569 : nat) : (term103 _70569 _70568) = (term174 _70568 _70569).
Proof. exact (@lem5471985 (Peano.lt _70569 _70568) (Peano.le _70568 _70569)). Qed.
Lemma lem5471991 (_70568 : nat) (_70569 : nat) (h1 : term76) : term174 _70568 _70569.
Proof. exact (EQ_MP (@lem5471988 _70568 _70569) (@lem5471886 _70569 _70568 h1)). Qed.
Lemma lem5471992 (m : nat) (n : nat) (h1 : term76) : term174 m n.
Proof. exact (@lem5471991 m n h1). Qed.
Lemma lem5471995 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term34 p m n q) : Peano.le m n.
Proof. exact (@lem5471992 m n h1 (@lem5471983 p m n q h2)). Qed.
Lemma lem5471996 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term34 p m n q) : term175 m n.
Proof. exact (fun h0 : term72 m n => @lem5471995 p m n q h1 h2). Qed.
Lemma lem5471998 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5471999 (m : nat) (n : nat) : (term175 m n) = (Peano.le m n).
Proof. exact (@lem5471998 (Peano.le m n)). Qed.
Lemma lem5472000 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term34 p m n q) : Peano.le m n.
Proof. exact (EQ_MP (@lem5471999 m n) (@lem5471996 p m n q h1 h2)). Qed.
Lemma lem5472006 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5472007 (n : nat) (m : nat) (p : nat) (_70570 : nat) : (term165 m n p _70570) = (term176 n m p _70570).
Proof. exact (@lem5472006 (term72 _70570 n) (term72 m _70570) (Peano.le p _70570)). Qed.
Lemma lem5472021 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5472022 (p : nat) (m : nat) (_70570 : nat) : (term177 m p _70570) = (term178 p m _70570).
Proof. exact (@lem5472021 (Peano.le p _70570) (term72 m _70570)). Qed.
Lemma lem5472028 (_70570 : nat) (n : nat) : (term179 _70570 n) = (term179 _70570 n).
Proof. exact (eq_refl (term179 _70570 n)). Qed.
Lemma lem5472029 (n : nat) (p : nat) (m : nat) (_70570 : nat) : (term176 n m p _70570) = (term180 n p m _70570).
Proof. exact (MK_COMB (@lem5472028 _70570 n) (@lem5472022 p m _70570)). Qed.
Lemma lem5472033 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5472034 (p : nat) (n : nat) (m : nat) (_70570 : nat) : (term180 n p m _70570) = (term181 p n m _70570).
Proof. exact (@lem5472033 (Peano.le p _70570) (term72 _70570 n) (term72 m _70570)). Qed.
Lemma lem5472050 (p : nat) (n : nat) (m : nat) (_70570 : nat) : (term176 n m p _70570) = (term181 p n m _70570).
Proof. exact (TRANS (@lem5472029 n p m _70570) (@lem5472034 p n m _70570)). Qed.
Lemma lem5472051 (p : nat) (n : nat) (m : nat) (_70570 : nat) : (term165 m n p _70570) = (term181 p n m _70570).
Proof. exact (TRANS (@lem5472007 n m p _70570) (@lem5472050 p n m _70570)). Qed.
Lemma lem5472052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5472053 (p : nat) (n : nat) (m : nat) (_70570 : nat) : (term182 m n p _70570) = (term183 p n m _70570).
Proof. exact (MK_COMB (@lem5472052) (@lem5472051 p n m _70570)). Qed.
Lemma lem5472067 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5472068 (n : nat) (m : nat) (_70570 : nat) : (term81 m _70570 n) = (term184 n m _70570).
Proof. exact (@lem5472067 (term72 _70570 n) (term72 m _70570)). Qed.
Lemma lem5472074 (p : nat) (_70570 : nat) : (term101 p _70570) = (term101 p _70570).
Proof. exact (eq_refl (term101 p _70570)). Qed.
Lemma lem5472075 (p : nat) (n : nat) (m : nat) (_70570 : nat) : (term185 p m _70570 n) = (term181 p n m _70570).
Proof. exact (MK_COMB (@lem5472074 p _70570) (@lem5472068 n m _70570)). Qed.
Lemma lem5472086 (p : nat) (n : nat) (m : nat) (_70570 : nat) : ((term165 m n p _70570) = (term185 p m _70570 n)) = ((term181 p n m _70570) = (term181 p n m _70570)).
Proof. exact (MK_COMB (@lem5472053 p n m _70570) (@lem5472075 p n m _70570)). Qed.
Lemma lem5472088 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5472089 (x : Prop) : (x = x) = True.
Proof. exact (@lem5472088 Prop x). Qed.
Lemma lem5472090 (p : nat) (n : nat) (m : nat) (_70570 : nat) : ((term181 p n m _70570) = (term181 p n m _70570)) = True.
Proof. exact (@lem5472089 (term181 p n m _70570)). Qed.
Lemma lem5472091 (p : nat) (m : nat) (_70570 : nat) (n : nat) : ((term165 m n p _70570) = (term185 p m _70570 n)) = True.
Proof. exact (TRANS (@lem5472086 p n m _70570) (@lem5472090 p n m _70570)). Qed.
Lemma lem5472092 (p : nat) (m : nat) (_70570 : nat) (n : nat) : True = ((term165 m n p _70570) = (term185 p m _70570 n)).
Proof. exact (SYM (@lem5472091 p m _70570 n)). Qed.
Lemma lem5472093 (p : nat) (m : nat) (_70570 : nat) (n : nat) : (term165 m n p _70570) = (term185 p m _70570 n).
Proof. exact (EQ_MP (@lem5472092 p m _70570 n) (@lem0)). Qed.
Lemma lem5472094 (_70570 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term185 p m _70570 n.
Proof. exact (EQ_MP (@lem5472093 p m _70570 n) (@lem5471902 _70570 p m n q h1)). Qed.
Lemma lem5472096 (b : Prop) (a : Prop) : (a \/ b) = (term173 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5472097 (m : nat) (n : nat) (p : nat) (_70570 : nat) : (term185 p m _70570 n) = (term186 m n p _70570).
Proof. exact (@lem5472096 (term81 m _70570 n) (Peano.le p _70570)). Qed.
Lemma lem5472099 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5472100 (m : nat) (_70570 : nat) (n : nat) : (term189 m _70570 n) = (term190 m _70570 n).
Proof. exact (@lem5472099 (term72 m _70570) (term72 _70570 n)). Qed.
Lemma lem5472102 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5472103 (m : nat) (_70570 : nat) : (term99 m _70570) = (Peano.le m _70570).
Proof. exact (@lem5472102 (Peano.le m _70570)). Qed.
Lemma lem5472104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472105 (m : nat) (_70570 : nat) : (term192 m _70570) = (term193 m _70570).
Proof. exact (MK_COMB (@lem5472104) (@lem5472103 m _70570)). Qed.
Lemma lem5472107 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5472108 (_70570 : nat) (n : nat) : (term99 _70570 n) = (Peano.le _70570 n).
Proof. exact (@lem5472107 (Peano.le _70570 n)). Qed.
Lemma lem5472109 (m : nat) (_70570 : nat) (n : nat) : (term190 m _70570 n) = (term13 m _70570 n).
Proof. exact (MK_COMB (@lem5472105 m _70570) (@lem5472108 _70570 n)). Qed.
Lemma lem5472110 (m : nat) (_70570 : nat) (n : nat) : (term189 m _70570 n) = (term13 m _70570 n).
Proof. exact (TRANS (@lem5472100 m _70570 n) (@lem5472109 m _70570 n)). Qed.
Lemma lem5472111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5472112 (m : nat) (_70570 : nat) (n : nat) : (term194 m _70570 n) = (term22 m _70570 n).
Proof. exact (MK_COMB (@lem5472111) (@lem5472110 m _70570 n)). Qed.
Lemma lem5472113 (p : nat) (_70570 : nat) : (Peano.le p _70570) = (Peano.le p _70570).
Proof. exact (eq_refl (Peano.le p _70570)). Qed.
Lemma lem5472114 (m : nat) (n : nat) (p : nat) (_70570 : nat) : (term186 m n p _70570) = (term195 m n p _70570).
Proof. exact (MK_COMB (@lem5472112 m _70570 n) (@lem5472113 p _70570)). Qed.
Lemma lem5472115 (m : nat) (n : nat) (p : nat) (_70570 : nat) : (term185 p m _70570 n) = (term195 m n p _70570).
Proof. exact (TRANS (@lem5472097 m n p _70570) (@lem5472114 m n p _70570)). Qed.
Lemma lem5472117 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term196 m n.
Proof. exact (conj (@lem5471976 m h2) (@lem5472000 p m n q h1 h3)). Qed.
Lemma lem5472119 (_70570 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term195 m n p _70570.
Proof. exact (EQ_MP (@lem5472115 m n p _70570) (@lem5472094 _70570 p m n q h1)). Qed.
Lemma lem5472120 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term197 n p m.
Proof. exact (@lem5472119 m p m n q h1). Qed.
Lemma lem5472123 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : Peano.le p m.
Proof. exact (@lem5472120 p m n q h3 (@lem5472117 p m n q h1 h2 h3)). Qed.
Lemma lem5472124 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term175 p m.
Proof. exact (fun h0 : term72 p m => @lem5472123 p m n q h1 h2 h3). Qed.
Lemma lem5472126 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5472127 (p : nat) (m : nat) : (term175 p m) = (Peano.le p m).
Proof. exact (@lem5472126 (Peano.le p m)). Qed.
Lemma lem5472128 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : Peano.le p m.
Proof. exact (EQ_MP (@lem5472127 p m) (@lem5472124 p m n q h1 h2 h3)). Qed.
Lemma lem5472131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5472133 (p : nat) (m : nat) : (term72 p m) = (term198 p m).
Proof. exact (@lem5472131 (Peano.le p m)). Qed.
Lemma lem5472136 (p : nat) (m : nat) (h1 : term72 p m) : term198 p m.
Proof. exact (EQ_MP (@lem5472133 p m) (@lem5471890 p m h1)). Qed.
Lemma lem5472139 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : False.
Proof. exact (@lem5472136 p m h3 (@lem5472128 p m n q h1 h2 h4)). Qed.
Lemma lem5472140 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : term199.
Proof. exact (fun h0 : ~ False => @lem5472139 p m n q h1 h2 h3 h4). Qed.
Lemma lem5472142 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5472143 : term199 = False.
Proof. exact (@lem5472142 False). Qed.
Lemma lem5472144 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472143) (@lem5472140 p m n q h1 h2 h3 h4)). Qed.
Lemma lem5472146 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term170 n m.
Proof. exact (proj1 (@lem5471595 p m n q h1)). Qed.
Lemma lem5472147 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term171 n m.
Proof. exact (fun h0 : Peano.lt n m => @lem5472146 p m n q h1). Qed.
Lemma lem5472149 (p : Prop) : (term172 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5472150 (n : nat) (m : nat) : (term171 n m) = (term170 n m).
Proof. exact (@lem5472149 (Peano.lt n m)). Qed.
Lemma lem5472151 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term170 n m.
Proof. exact (EQ_MP (@lem5472150 n m) (@lem5472147 p m n q h1)). Qed.
Lemma lem5472153 (b : Prop) (a : Prop) : (a \/ b) = (term173 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5472156 (_70577 : nat) (_70578 : nat) : (term103 _70578 _70577) = (term174 _70577 _70578).
Proof. exact (@lem5472153 (Peano.lt _70578 _70577) (Peano.le _70577 _70578)). Qed.
Lemma lem5472159 (_70577 : nat) (_70578 : nat) (h1 : term76) : term174 _70577 _70578.
Proof. exact (EQ_MP (@lem5472156 _70577 _70578) (@lem5471940 _70578 _70577 h1)). Qed.
Lemma lem5472160 (m : nat) (n : nat) (h1 : term76) : term174 m n.
Proof. exact (@lem5472159 m n h1). Qed.
Lemma lem5472163 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term34 p m n q) : Peano.le m n.
Proof. exact (@lem5472160 m n h1 (@lem5472151 p m n q h2)). Qed.
Lemma lem5472164 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term34 p m n q) : term175 m n.
Proof. exact (fun h0 : term72 m n => @lem5472163 p m n q h1 h2). Qed.
Lemma lem5472166 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5472167 (m : nat) (n : nat) : (term175 m n) = (Peano.le m n).
Proof. exact (@lem5472166 (Peano.le m n)). Qed.
Lemma lem5472168 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term34 p m n q) : Peano.le m n.
Proof. exact (EQ_MP (@lem5472167 m n) (@lem5472164 p m n q h1 h2)). Qed.
Lemma lem5472170 (_70571 : nat) (h1 : term78) : Peano.le _70571 _70571.
Proof. exact (EQ_MP (@lem5471831 _70571) (@lem5471830 _70571 h1)). Qed.
Lemma lem5472171 (n : nat) (h1 : term78) : Peano.le n n.
Proof. exact (@lem5472170 n h1). Qed.
Lemma lem5472172 (n : nat) (h1 : term78) : term167 n.
Proof. exact (fun h0 : term168 n => @lem5472171 n h1). Qed.
Lemma lem5472174 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5472175 (n : nat) : (term167 n) = (Peano.le n n).
Proof. exact (@lem5472174 (Peano.le n n)). Qed.
Lemma lem5472176 (n : nat) (h1 : term78) : Peano.le n n.
Proof. exact (EQ_MP (@lem5472175 n) (@lem5472172 n h1)). Qed.
Lemma lem5472182 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5472183 (n : nat) (m : nat) (_70579 : nat) (q : nat) : (term166 m n _70579 q) = (term200 n m _70579 q).
Proof. exact (@lem5472182 (term72 _70579 n) (term72 m _70579) (Peano.le _70579 q)). Qed.
Lemma lem5472197 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5472198 (q : nat) (m : nat) (_70579 : nat) : (term201 m _70579 q) = (term202 q m _70579).
Proof. exact (@lem5472197 (Peano.le _70579 q) (term72 m _70579)). Qed.
Lemma lem5472204 (_70579 : nat) (n : nat) : (term179 _70579 n) = (term179 _70579 n).
Proof. exact (eq_refl (term179 _70579 n)). Qed.
Lemma lem5472205 (n : nat) (q : nat) (m : nat) (_70579 : nat) : (term200 n m _70579 q) = (term203 n q m _70579).
Proof. exact (MK_COMB (@lem5472204 _70579 n) (@lem5472198 q m _70579)). Qed.
Lemma lem5472209 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5472210 (q : nat) (n : nat) (m : nat) (_70579 : nat) : (term203 n q m _70579) = (term204 q n m _70579).
Proof. exact (@lem5472209 (Peano.le _70579 q) (term72 _70579 n) (term72 m _70579)). Qed.
Lemma lem5472226 (q : nat) (n : nat) (m : nat) (_70579 : nat) : (term200 n m _70579 q) = (term204 q n m _70579).
Proof. exact (TRANS (@lem5472205 n q m _70579) (@lem5472210 q n m _70579)). Qed.
Lemma lem5472227 (q : nat) (n : nat) (m : nat) (_70579 : nat) : (term166 m n _70579 q) = (term204 q n m _70579).
Proof. exact (TRANS (@lem5472183 n m _70579 q) (@lem5472226 q n m _70579)). Qed.
Lemma lem5472228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5472229 (q : nat) (n : nat) (m : nat) (_70579 : nat) : (term205 m n _70579 q) = (term206 q n m _70579).
Proof. exact (MK_COMB (@lem5472228) (@lem5472227 q n m _70579)). Qed.
Lemma lem5472243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5472244 (n : nat) (m : nat) (_70579 : nat) : (term81 m _70579 n) = (term184 n m _70579).
Proof. exact (@lem5472243 (term72 _70579 n) (term72 m _70579)). Qed.
Lemma lem5472250 (_70579 : nat) (q : nat) : (term101 _70579 q) = (term101 _70579 q).
Proof. exact (eq_refl (term101 _70579 q)). Qed.
Lemma lem5472251 (q : nat) (n : nat) (m : nat) (_70579 : nat) : (term207 q m _70579 n) = (term204 q n m _70579).
Proof. exact (MK_COMB (@lem5472250 _70579 q) (@lem5472244 n m _70579)). Qed.
Lemma lem5472262 (q : nat) (n : nat) (m : nat) (_70579 : nat) : ((term166 m n _70579 q) = (term207 q m _70579 n)) = ((term204 q n m _70579) = (term204 q n m _70579)).
Proof. exact (MK_COMB (@lem5472229 q n m _70579) (@lem5472251 q n m _70579)). Qed.
Lemma lem5472264 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5472265 (x : Prop) : (x = x) = True.
Proof. exact (@lem5472264 Prop x). Qed.
Lemma lem5472266 (q : nat) (n : nat) (m : nat) (_70579 : nat) : ((term204 q n m _70579) = (term204 q n m _70579)) = True.
Proof. exact (@lem5472265 (term204 q n m _70579)). Qed.
Lemma lem5472267 (q : nat) (m : nat) (_70579 : nat) (n : nat) : ((term166 m n _70579 q) = (term207 q m _70579 n)) = True.
Proof. exact (TRANS (@lem5472262 q n m _70579) (@lem5472266 q n m _70579)). Qed.
Lemma lem5472268 (q : nat) (m : nat) (_70579 : nat) (n : nat) : True = ((term166 m n _70579 q) = (term207 q m _70579 n)).
Proof. exact (SYM (@lem5472267 q m _70579 n)). Qed.
Lemma lem5472269 (q : nat) (m : nat) (_70579 : nat) (n : nat) : (term166 m n _70579 q) = (term207 q m _70579 n).
Proof. exact (EQ_MP (@lem5472268 q m _70579 n) (@lem0)). Qed.
Lemma lem5472270 (_70579 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term207 q m _70579 n.
Proof. exact (EQ_MP (@lem5472269 q m _70579 n) (@lem5471968 _70579 p m n q h1)). Qed.
Lemma lem5472272 (b : Prop) (a : Prop) : (a \/ b) = (term173 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5472273 (m : nat) (n : nat) (_70579 : nat) (q : nat) : (term207 q m _70579 n) = (term208 m n _70579 q).
Proof. exact (@lem5472272 (term81 m _70579 n) (Peano.le _70579 q)). Qed.
Lemma lem5472275 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5472276 (m : nat) (_70579 : nat) (n : nat) : (term189 m _70579 n) = (term190 m _70579 n).
Proof. exact (@lem5472275 (term72 m _70579) (term72 _70579 n)). Qed.
Lemma lem5472278 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5472279 (m : nat) (_70579 : nat) : (term99 m _70579) = (Peano.le m _70579).
Proof. exact (@lem5472278 (Peano.le m _70579)). Qed.
Lemma lem5472280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472281 (m : nat) (_70579 : nat) : (term192 m _70579) = (term193 m _70579).
Proof. exact (MK_COMB (@lem5472280) (@lem5472279 m _70579)). Qed.
Lemma lem5472283 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5472284 (_70579 : nat) (n : nat) : (term99 _70579 n) = (Peano.le _70579 n).
Proof. exact (@lem5472283 (Peano.le _70579 n)). Qed.
Lemma lem5472285 (m : nat) (_70579 : nat) (n : nat) : (term190 m _70579 n) = (term13 m _70579 n).
Proof. exact (MK_COMB (@lem5472281 m _70579) (@lem5472284 _70579 n)). Qed.
Lemma lem5472286 (m : nat) (_70579 : nat) (n : nat) : (term189 m _70579 n) = (term13 m _70579 n).
Proof. exact (TRANS (@lem5472276 m _70579 n) (@lem5472285 m _70579 n)). Qed.
Lemma lem5472287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5472288 (m : nat) (_70579 : nat) (n : nat) : (term194 m _70579 n) = (term22 m _70579 n).
Proof. exact (MK_COMB (@lem5472287) (@lem5472286 m _70579 n)). Qed.
Lemma lem5472289 (_70579 : nat) (q : nat) : (Peano.le _70579 q) = (Peano.le _70579 q).
Proof. exact (eq_refl (Peano.le _70579 q)). Qed.
Lemma lem5472290 (m : nat) (n : nat) (_70579 : nat) (q : nat) : (term208 m n _70579 q) = (term209 m n _70579 q).
Proof. exact (MK_COMB (@lem5472288 m _70579 n) (@lem5472289 _70579 q)). Qed.
Lemma lem5472291 (m : nat) (n : nat) (_70579 : nat) (q : nat) : (term207 q m _70579 n) = (term209 m n _70579 q).
Proof. exact (TRANS (@lem5472273 m n _70579 q) (@lem5472290 m n _70579 q)). Qed.
Lemma lem5472293 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term210 m n.
Proof. exact (conj (@lem5472168 p m n q h1 h3) (@lem5472176 n h2)). Qed.
Lemma lem5472295 (_70579 : nat) (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term209 m n _70579 q.
Proof. exact (EQ_MP (@lem5472291 m n _70579 q) (@lem5472270 _70579 p m n q h1)). Qed.
Lemma lem5472296 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term211 m n q.
Proof. exact (@lem5472295 n p m n q h1). Qed.
Lemma lem5472299 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : Peano.le n q.
Proof. exact (@lem5472296 p m n q h3 (@lem5472293 p m n q h1 h2 h3)). Qed.
Lemma lem5472300 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term175 n q.
Proof. exact (fun h0 : term72 n q => @lem5472299 p m n q h1 h2 h3). Qed.
Lemma lem5472302 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5472303 (n : nat) (q : nat) : (term175 n q) = (Peano.le n q).
Proof. exact (@lem5472302 (Peano.le n q)). Qed.
Lemma lem5472304 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : Peano.le n q.
Proof. exact (EQ_MP (@lem5472303 n q) (@lem5472300 p m n q h1 h2 h3)). Qed.
Lemma lem5472307 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5472309 (n : nat) (q : nat) : (term72 n q) = (term198 n q).
Proof. exact (@lem5472307 (Peano.le n q)). Qed.
Lemma lem5472312 (n : nat) (q : nat) (h1 : term72 n q) : term198 n q.
Proof. exact (EQ_MP (@lem5472309 n q) (@lem5471944 n q h1)). Qed.
Lemma lem5472315 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : False.
Proof. exact (@lem5472312 n q h3 (@lem5472304 p m n q h1 h2 h4)). Qed.
Lemma lem5472316 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : term199.
Proof. exact (fun h0 : ~ False => @lem5472315 p m n q h1 h2 h3 h4). Qed.
Lemma lem5472318 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5472319 : term199 = False.
Proof. exact (@lem5472318 False). Qed.
Lemma lem5472320 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472319) (@lem5472316 p m n q h1 h2 h3 h4)). Qed.
Lemma lem5472321 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : (term72 n q) = False.
Proof. exact (prop_ext (fun h5 : term72 n q => @lem5472320 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471944 n q h3)). Qed.
Lemma lem5472322 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472321 p m n q h1 h2 h3 h4) (@lem5471944 n q h3)). Qed.
Lemma lem5472323 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : (term72 p m) = False.
Proof. exact (prop_ext (fun h5 : term72 p m => @lem5472144 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471890 p m h3)). Qed.
Lemma lem5472324 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472323 p m n q h1 h2 h3 h4) (@lem5471890 p m h3)). Qed.
Lemma lem5472325 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : (term72 n q) = False.
Proof. exact (prop_ext (fun h5 : term72 n q => @lem5472322 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471802 n q h3)). Qed.
Lemma lem5472326 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472325 p m n q h1 h2 h3 h4) (@lem5471802 n q h3)). Qed.
Lemma lem5472327 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : (term72 p m) = False.
Proof. exact (prop_ext (fun h5 : term72 p m => @lem5472324 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471701 p m h3)). Qed.
Lemma lem5472328 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472327 p m n q h1 h2 h3 h4) (@lem5471701 p m h3)). Qed.
Lemma lem5472329 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : (term72 n q) = False.
Proof. exact (prop_ext (fun h5 : term72 n q => @lem5472326 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471802 n q h3)). Qed.
Lemma lem5472330 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472329 p m n q h1 h2 h3 h4) (@lem5471802 n q h3)). Qed.
Lemma lem5472331 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : term78 = False.
Proof. exact (prop_ext (fun h5 : term78 => @lem5472330 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471708 h2)). Qed.
Lemma lem5472332 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 n q) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472331 p m n q h1 h2 h3 h4) (@lem5471708 h2)). Qed.
Lemma lem5472333 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : (term72 p m) = False.
Proof. exact (prop_ext (fun h5 : term72 p m => @lem5472328 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471701 p m h3)). Qed.
Lemma lem5472334 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472333 p m n q h1 h2 h3 h4) (@lem5471701 p m h3)). Qed.
Lemma lem5472335 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : term78 = False.
Proof. exact (prop_ext (fun h5 : term78 => @lem5472334 p m n q h1 h2 h3 h4) (fun h5 : False => @lem5471607 h2)). Qed.
Lemma lem5472336 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term72 p m) (h4 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472335 p m n q h1 h2 h3 h4) (@lem5471607 h2)). Qed.
Lemma lem5472337 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : False.
Proof. exact (or_elim (@lem5471597 p m n q h3) (fun h0 : term72 p m => @lem5472336 p m n q h1 h2 h0 h3) (fun h0 : term72 n q => @lem5472332 p m n q h1 h2 h0 h3)). Qed.
Lemma lem5472338 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term78 = False.
Proof. exact (prop_ext (fun h4 : term78 => @lem5472337 p m n q h1 h2 h3) (fun h4 : False => @lem5471511 h2)). Qed.
Lemma lem5472339 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472338 p m n q h1 h2 h3) (@lem5471511 h2)). Qed.
Lemma lem5472340 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term78 = False.
Proof. exact (prop_ext (fun h4 : term78 => @lem5472339 p m n q h1 h2 h3) (fun h4 : False => @lem5471063 h2)). Qed.
Lemma lem5472341 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472340 p m n q h1 h2 h3) (@lem5471063 h2)). Qed.
Lemma lem5472342 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term39.
Proof. exact (fun h0 : term41 => @lem5472341 p m n q h1 h2 h3). Qed.
Lemma lem5472343 : term39 = term40.
Proof. exact (@lem69 term41). Qed.
Lemma lem5472344 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term76) (h2 : term78) (h3 : term34 p m n q) : term40.
Proof. exact (EQ_MP (@lem5472343) (@lem5472342 p m n q h1 h2 h3)). Qed.
Lemma lem5472345 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term78) (h2 : term34 p m n q) : term44.
Proof. exact (fun h0 : term76 => @lem5472344 p m n q h0 h1 h2). Qed.
Lemma lem5472346 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term47.
Proof. exact (fun h0 : term78 => @lem5472345 p m n q h0 h1). Qed.
Lemma lem5472347 (p : nat) (m : nat) (n : nat) (q : nat) : term49 p m n q.
Proof. exact (fun h0 : term34 p m n q => @lem5472346 p m n q h0). Qed.
Lemma lem5472352 (m : nat) (n : nat) (q : nat) : term53 m n q.
Proof. exact (fun p : nat => @lem5472347 p m n q). Qed.
Lemma lem5472357 (n : nat) (q : nat) : term57 n q.
Proof. exact (fun m : nat => @lem5472352 m n q). Qed.
Lemma lem5472362 (q : nat) : term61 q.
Proof. exact (fun n : nat => @lem5472357 n q). Qed.
Lemma lem5472367 : term65.
Proof. exact (fun q : nat => @lem5472362 q). Qed.
Lemma lem5472368 : term64.
Proof. exact (EQ_MP (@lem5470955) (@lem5472367)). Qed.
Lemma lem5472369 (q : nat) : term212 q.
Proof. exact (@lem5472368 q). Qed.
Lemma lem5472370 (q : nat) : (term212 q) = (term60 q).
Proof. exact (eq_refl (term212 q)). Qed.
Lemma lem5472371 (q : nat) : term60 q.
Proof. exact (EQ_MP (@lem5472370 q) (@lem5472369 q)). Qed.
Lemma lem5472372 (q : nat) (n : nat) : term213 q n.
Proof. exact (@lem5472371 q n). Qed.
Lemma lem5472373 (n : nat) (q : nat) : (term213 q n) = (term56 n q).
Proof. exact (eq_refl (term213 q n)). Qed.
Lemma lem5472374 (n : nat) (q : nat) : term56 n q.
Proof. exact (EQ_MP (@lem5472373 n q) (@lem5472372 q n)). Qed.
Lemma lem5472375 (n : nat) (q : nat) (m : nat) : term214 n q m.
Proof. exact (@lem5472374 n q m). Qed.
Lemma lem5472376 (m : nat) (n : nat) (q : nat) : (term214 n q m) = (term52 m n q).
Proof. exact (eq_refl (term214 n q m)). Qed.
Lemma lem5472377 (m : nat) (n : nat) (q : nat) : term52 m n q.
Proof. exact (EQ_MP (@lem5472376 m n q) (@lem5472375 n q m)). Qed.
Lemma lem5472378 (m : nat) (n : nat) (q : nat) (p : nat) : term215 m n q p.
Proof. exact (@lem5472377 m n q p). Qed.
Lemma lem5472379 (p : nat) (m : nat) (n : nat) (q : nat) : (term215 m n q p) = (term35 p m n q).
Proof. exact (eq_refl (term215 m n q p)). Qed.
Lemma lem5472380 (p : nat) (m : nat) (n : nat) (q : nat) : term35 p m n q.
Proof. exact (EQ_MP (@lem5472379 p m n q) (@lem5472378 m n q p)). Qed.
Lemma lem5472382 (p : nat) (m : nat) (n : nat) (q : nat) : term35 p m n q.
Proof. exact (@lem5470662 p m n q (@lem5472380 p m n q)). Qed.
Lemma lem5472383 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term46.
Proof. exact (@lem5472382 p m n q (@lem5470647 p m n q h1)). Qed.
Lemma lem5472384 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term43.
Proof. exact (@lem5472383 p m n q h1 (@lem91603)). Qed.
Lemma lem5472385 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : term39.
Proof. exact (@lem5472384 p m n q h1 (@lem97961)). Qed.
Lemma lem5472386 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : False.
Proof. exact (@lem5472385 p m n q h1 (@lem93743)). Qed.
Lemma lem5472387 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : (term34 p m n q) = False.
Proof. exact (prop_ext (fun h2 : term34 p m n q => @lem5472386 p m n q h1) (fun h2 : False => @lem5470647 p m n q h1)). Qed.
Lemma lem5472388 (p : nat) (m : nat) (n : nat) (q : nat) (h1 : term34 p m n q) : False.
Proof. exact (EQ_MP (@lem5472387 p m n q h1) (@lem5470647 p m n q h1)). Qed.
Lemma lem5472389 (p : nat) (m : nat) (n : nat) (q : nat) : term33 p m n q.
Proof. exact (fun h0 : term34 p m n q => @lem5472388 p m n q h0). Qed.
Lemma lem5472390 (p : nat) (m : nat) (n : nat) (q : nat) : term32 p m n q.
Proof. exact (EQ_MP (@lem5470646 p m n q) (@lem5472389 p m n q)). Qed.
Lemma lem5472420 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term24 m n p x q) = (term24 m n p x q).
Proof. exact (eq_refl (term24 m n p x q)). Qed.
Lemma lem5472421 (m : nat) (n : nat) (p : nat) (q : nat) : (term26 m n p q) = (term26 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5472420 m n p x q)). Qed.
Lemma lem5472422 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5472423 (m : nat) (n : nat) (p : nat) (q : nat) : (term27 m n p q) = (term27 m n p q).
Proof. exact (MK_COMB (@lem5472422) (@lem5472421 m n p q)). Qed.
Lemma lem5472434 (p : nat) (m : nat) (n : nat) (q : nat) : (term216 p m n q) = (term216 p m n q).
Proof. exact (eq_refl (term216 p m n q)). Qed.
Lemma lem5472436 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term217 m n p q).
Proof. exact (MK_COMB (@lem5472434 p m n q) (@lem5472423 m n p q)). Qed.
Lemma lem5472444 (p : nat) (m : nat) (n : nat) (q : nat) : (term88 p m n q) = (term89 p m n q).
Proof. exact (@lem17045 (Peano.le p m) (Peano.le n q)). Qed.
Lemma lem5472446 (n : nat) (m : nat) : (term90 n m) = (term90 n m).
Proof. exact (eq_refl (term90 n m)). Qed.
Lemma lem5472447 (p : nat) (m : nat) (n : nat) (q : nat) : (term91 p m n q) = (term92 p m n q).
Proof. exact (MK_COMB (@lem5472446 n m) (@lem5472444 p m n q)). Qed.
Lemma lem5472448 (p : nat) (m : nat) (n : nat) (q : nat) : (term93 p m n q) = (term91 p m n q).
Proof. exact (@lem17160 (Peano.lt n m) (term94 p m n q)). Qed.
Lemma lem5472449 (p : nat) (m : nat) (n : nat) (q : nat) : (term93 p m n q) = (term92 p m n q).
Proof. exact (TRANS (@lem5472448 p m n q) (@lem5472447 p m n q)). Qed.
Lemma lem5472456 (m : nat) (x : nat) (n : nat) : (term80 m x n) = (term81 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5472461 (p : nat) (x : nat) (q : nat) : (term13 p x q) = (term13 p x q).
Proof. exact (eq_refl (term13 p x q)). Qed.
Lemma lem5472462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472463 (m : nat) (x : nat) (n : nat) : (term82 m x n) = (term83 m x n).
Proof. exact (MK_COMB (@lem5472462) (@lem5472456 m x n)). Qed.
Lemma lem5472464 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term84 m n p x q) = (term85 m n p x q).
Proof. exact (MK_COMB (@lem5472463 m x n) (@lem5472461 p x q)). Qed.
Lemma lem5472465 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term24 m n p x q) = (term84 m n p x q).
Proof. exact (@lem17265 (term13 m x n) (term13 p x q)). Qed.
Lemma lem5472466 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term24 m n p x q) = (term85 m n p x q).
Proof. exact (TRANS (@lem5472465 m n p x q) (@lem5472464 m n p x q)). Qed.
Lemma lem5472467 (m : nat) (n : nat) (p : nat) (q : nat) : (term26 m n p q) = (term86 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5472466 m n p x q)). Qed.
Lemma lem5472468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5472469 (m : nat) (n : nat) (p : nat) (q : nat) : (term27 m n p q) = (term87 m n p q).
Proof. exact (MK_COMB (@lem5472468) (@lem5472467 m n p q)). Qed.
Lemma lem5472470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472471 (p : nat) (m : nat) (n : nat) (q : nat) : (term218 p m n q) = (term219 p m n q).
Proof. exact (MK_COMB (@lem5472470) (@lem5472449 p m n q)). Qed.
Lemma lem5472472 (m : nat) (n : nat) (p : nat) (q : nat) : (term220 m n p q) = (term221 m n p q).
Proof. exact (MK_COMB (@lem5472471 p m n q) (@lem5472469 m n p q)). Qed.
Lemma lem5472473 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term220 m n p q).
Proof. exact (@lem17265 (term30 p m n q) (term27 m n p q)). Qed.
Lemma lem5472474 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term221 m n p q).
Proof. exact (TRANS (@lem5472473 m n p q) (@lem5472472 m n p q)). Qed.
Lemma lem5472475 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term221 m n p q).
Proof. exact (TRANS (@lem5472436 m n p q) (@lem5472474 m n p q)). Qed.
Lemma lem5472476 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term85 m n p x q) = (term85 m n p x q).
Proof. exact (eq_refl (term85 m n p x q)). Qed.
Lemma lem5472477 (m : nat) (n : nat) (p : nat) (q : nat) : (term86 m n p q) = (term86 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5472476 m n p x q)). Qed.
Lemma lem5472478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5472479 (m : nat) (n : nat) (p : nat) (q : nat) : (term87 m n p q) = (term87 m n p q).
Proof. exact (MK_COMB (@lem5472478) (@lem5472477 m n p q)). Qed.
Lemma lem5472482 (p : nat) (m : nat) (n : nat) (q : nat) : (term219 p m n q) = (term219 p m n q).
Proof. exact (eq_refl (term219 p m n q)). Qed.
Lemma lem5472483 (m : nat) (n : nat) (p : nat) (q : nat) : (term221 m n p q) = (term221 m n p q).
Proof. exact (MK_COMB (@lem5472482 p m n q) (@lem5472479 m n p q)). Qed.
Lemma lem5472506 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term221 m n p q).
Proof. exact (TRANS (@lem5472475 m n p q) (@lem5472483 m n p q)). Qed.
Lemma lem5472539 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term85 m n p x q) = (term85 m n p x q).
Proof. exact (eq_refl (term85 m n p x q)). Qed.
Lemma lem5472540 (m : nat) (n : nat) (p : nat) (q : nat) : (term86 m n p q) = (term86 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5472539 m n p x q)). Qed.
Lemma lem5472541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5472542 (m : nat) (n : nat) (p : nat) (q : nat) : (term87 m n p q) = (term87 m n p q).
Proof. exact (MK_COMB (@lem5472541) (@lem5472540 m n p q)). Qed.
Lemma lem5472571 (p : nat) (m : nat) (n : nat) (q : nat) : (term219 p m n q) = (term219 p m n q).
Proof. exact (eq_refl (term219 p m n q)). Qed.
Lemma lem5472572 (m : nat) (n : nat) (p : nat) (q : nat) : (term221 m n p q) = (term221 m n p q).
Proof. exact (MK_COMB (@lem5472571 p m n q) (@lem5472542 m n p q)). Qed.
Lemma lem5472573 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term221 m n p q).
Proof. exact (TRANS (@lem5472506 m n p q) (@lem5472572 m n p q)). Qed.
Lemma lem5472575 {A : Type'} (P : Prop) (Q : A -> Prop) : (term222 A P Q) = (term223 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5472576 (P : Prop) (Q : nat -> Prop) : (term224 P Q) = (term225 P Q).
Proof. exact (@lem5472575 nat P Q). Qed.
Lemma lem5472577 (m : nat) (n : nat) (p : nat) (q : nat) : (term226 m n p q) = (term227 m n p q).
Proof. exact (@lem5472576 (term92 p m n q) (term86 m n p q)). Qed.
Lemma lem5472578 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term228 m n p q x) = (term85 m n p x q).
Proof. exact (eq_refl (term228 m n p q x)). Qed.
Lemma lem5472579 (m : nat) (n : nat) (p : nat) (q : nat) : (term229 m n p q) = (term86 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5472578 m n p x q)). Qed.
Lemma lem5472580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5472581 (m : nat) (n : nat) (p : nat) (q : nat) : (term230 m n p q) = (term87 m n p q).
Proof. exact (MK_COMB (@lem5472580) (@lem5472579 m n p q)). Qed.
Lemma lem5472582 (p : nat) (m : nat) (n : nat) (q : nat) : (term219 p m n q) = (term219 p m n q).
Proof. exact (eq_refl (term219 p m n q)). Qed.
Lemma lem5472583 (m : nat) (n : nat) (p : nat) (q : nat) : (term226 m n p q) = (term221 m n p q).
Proof. exact (MK_COMB (@lem5472582 p m n q) (@lem5472581 m n p q)). Qed.
Lemma lem5472584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5472585 (m : nat) (n : nat) (p : nat) (q : nat) : (term231 m n p q) = (term232 m n p q).
Proof. exact (MK_COMB (@lem5472584) (@lem5472583 m n p q)). Qed.
Lemma lem5472586 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term228 m n p q x) = (term85 m n p x q).
Proof. exact (eq_refl (term228 m n p q x)). Qed.
Lemma lem5472587 (p : nat) (m : nat) (n : nat) (q : nat) : (term219 p m n q) = (term219 p m n q).
Proof. exact (eq_refl (term219 p m n q)). Qed.
Lemma lem5472588 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term233 m n p q x) = (term234 m n p x q).
Proof. exact (MK_COMB (@lem5472587 p m n q) (@lem5472586 m n p x q)). Qed.
Lemma lem5472589 (m : nat) (n : nat) (p : nat) (q : nat) : (term235 m n p q) = (term236 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5472588 m n p x q)). Qed.
Lemma lem5472590 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5472591 (m : nat) (n : nat) (p : nat) (q : nat) : (term227 m n p q) = (term237 m n p q).
Proof. exact (MK_COMB (@lem5472590) (@lem5472589 m n p q)). Qed.
Lemma lem5472592 (m : nat) (n : nat) (p : nat) (q : nat) : ((term226 m n p q) = (term227 m n p q)) = ((term221 m n p q) = (term237 m n p q)).
Proof. exact (MK_COMB (@lem5472585 m n p q) (@lem5472591 m n p q)). Qed.
Lemma lem5472593 (m : nat) (n : nat) (p : nat) (q : nat) : (term221 m n p q) = (term237 m n p q).
Proof. exact (EQ_MP (@lem5472592 m n p q) (@lem5472577 m n p q)). Qed.
Lemma lem5472594 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term237 m n p q).
Proof. exact (TRANS (@lem5472573 m n p q) (@lem5472593 m n p q)). Qed.
Lemma lem5472596 (m : nat) (n : nat) : (Peano.lt m n) = (term238 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5472597 (n : nat) (m : nat) : (Peano.lt n m) = (term238 n m).
Proof. exact (@lem5472596 n m). Qed.
Lemma lem5472598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5472599 (n : nat) (m : nat) : (term170 n m) = (term239 n m).
Proof. exact (MK_COMB (@lem5472598) (@lem5472597 n m)). Qed.
Lemma lem5472600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472601 (n : nat) (m : nat) : (term90 n m) = (term240 n m).
Proof. exact (MK_COMB (@lem5472600) (@lem5472599 n m)). Qed.
Lemma lem5472603 (m : nat) (n : nat) : (Peano.le m n) = (term241 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5472604 (p : nat) (m : nat) : (Peano.le p m) = (term241 p m).
Proof. exact (@lem5472603 p m). Qed.
Lemma lem5472605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5472606 (p : nat) (m : nat) : (term72 p m) = (term242 p m).
Proof. exact (MK_COMB (@lem5472605) (@lem5472604 p m)). Qed.
Lemma lem5472607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472608 (p : nat) (m : nat) : (term179 p m) = (term243 p m).
Proof. exact (MK_COMB (@lem5472607) (@lem5472606 p m)). Qed.
Lemma lem5472610 (m : nat) (n : nat) : (Peano.le m n) = (term241 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5472611 (n : nat) (q : nat) : (Peano.le n q) = (term241 n q).
Proof. exact (@lem5472610 n q). Qed.
Lemma lem5472612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5472613 (n : nat) (q : nat) : (term72 n q) = (term242 n q).
Proof. exact (MK_COMB (@lem5472612) (@lem5472611 n q)). Qed.
Lemma lem5472614 (p : nat) (m : nat) (n : nat) (q : nat) : (term89 p m n q) = (term244 p m n q).
Proof. exact (MK_COMB (@lem5472608 p m) (@lem5472613 n q)). Qed.
Lemma lem5472615 (p : nat) (m : nat) (n : nat) (q : nat) : (term92 p m n q) = (term245 p m n q).
Proof. exact (MK_COMB (@lem5472601 n m) (@lem5472614 p m n q)). Qed.
Lemma lem5472616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472617 (p : nat) (m : nat) (n : nat) (q : nat) : (term219 p m n q) = (term246 p m n q).
Proof. exact (MK_COMB (@lem5472616) (@lem5472615 p m n q)). Qed.
Lemma lem5472619 (m : nat) (n : nat) : (Peano.le m n) = (term241 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5472620 (m : nat) (x : nat) : (Peano.le m x) = (term241 m x).
Proof. exact (@lem5472619 m x). Qed.
Lemma lem5472621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5472622 (m : nat) (x : nat) : (term72 m x) = (term242 m x).
Proof. exact (MK_COMB (@lem5472621) (@lem5472620 m x)). Qed.
Lemma lem5472623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472624 (m : nat) (x : nat) : (term179 m x) = (term243 m x).
Proof. exact (MK_COMB (@lem5472623) (@lem5472622 m x)). Qed.
Lemma lem5472626 (m : nat) (n : nat) : (Peano.le m n) = (term241 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5472627 (x : nat) (n : nat) : (Peano.le x n) = (term241 x n).
Proof. exact (@lem5472626 x n). Qed.
Lemma lem5472628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5472629 (x : nat) (n : nat) : (term72 x n) = (term242 x n).
Proof. exact (MK_COMB (@lem5472628) (@lem5472627 x n)). Qed.
Lemma lem5472630 (m : nat) (x : nat) (n : nat) : (term81 m x n) = (term247 m x n).
Proof. exact (MK_COMB (@lem5472624 m x) (@lem5472629 x n)). Qed.
Lemma lem5472631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472632 (m : nat) (x : nat) (n : nat) : (term83 m x n) = (term248 m x n).
Proof. exact (MK_COMB (@lem5472631) (@lem5472630 m x n)). Qed.
Lemma lem5472634 (m : nat) (n : nat) : (Peano.le m n) = (term241 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5472635 (p : nat) (x : nat) : (Peano.le p x) = (term241 p x).
Proof. exact (@lem5472634 p x). Qed.
Lemma lem5472636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472637 (p : nat) (x : nat) : (term193 p x) = (term249 p x).
Proof. exact (MK_COMB (@lem5472636) (@lem5472635 p x)). Qed.
Lemma lem5472639 (m : nat) (n : nat) : (Peano.le m n) = (term241 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5472640 (x : nat) (q : nat) : (Peano.le x q) = (term241 x q).
Proof. exact (@lem5472639 x q). Qed.
Lemma lem5472641 (p : nat) (x : nat) (q : nat) : (term13 p x q) = (term250 p x q).
Proof. exact (MK_COMB (@lem5472637 p x) (@lem5472640 x q)). Qed.
Lemma lem5472642 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term85 m n p x q) = (term251 m n p x q).
Proof. exact (MK_COMB (@lem5472632 m x n) (@lem5472641 p x q)). Qed.
Lemma lem5472643 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : (term234 m n p x q) = (term252 m n p x q).
Proof. exact (MK_COMB (@lem5472617 p m n q) (@lem5472642 m n p x q)). Qed.
Lemma lem5472644 (m : nat) (n : nat) (p : nat) (q : nat) : (term236 m n p q) = (term253 m n p q).
Proof. exact (fun_ext (fun x : nat => @lem5472643 m n p x q)). Qed.
Lemma lem5472645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5472646 (m : nat) (n : nat) (p : nat) (q : nat) : (term237 m n p q) = (term254 m n p q).
Proof. exact (MK_COMB (@lem5472645) (@lem5472644 m n p q)). Qed.
Lemma lem5472647 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = (term254 m n p q).
Proof. exact (TRANS (@lem5472594 m n p q) (@lem5472646 m n p q)). Qed.
Lemma lem5472648 (m : nat) : term255 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5472649 (m : nat) : (term255 m) = (term256 m).
Proof. exact (eq_refl (term255 m)). Qed.
Lemma lem5472650 (m : nat) : term256 m.
Proof. exact (EQ_MP (@lem5472649 m) (@lem5472648 m)). Qed.
Lemma lem5472651 (n : nat) : term255 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5472652 (n : nat) : (term255 n) = (term256 n).
Proof. exact (eq_refl (term255 n)). Qed.
Lemma lem5472653 (n : nat) : term256 n.
Proof. exact (EQ_MP (@lem5472652 n) (@lem5472651 n)). Qed.
Lemma lem5472654 (p : nat) : term255 p.
Proof. exact (@lem2307535 p). Qed.
Lemma lem5472655 (p : nat) : (term255 p) = (term256 p).
Proof. exact (eq_refl (term255 p)). Qed.
Lemma lem5472656 (p : nat) : term256 p.
Proof. exact (EQ_MP (@lem5472655 p) (@lem5472654 p)). Qed.
Lemma lem5472657 (q : nat) : term255 q.
Proof. exact (@lem2307535 q). Qed.
Lemma lem5472658 (q : nat) : (term255 q) = (term256 q).
Proof. exact (eq_refl (term255 q)). Qed.
Lemma lem5472659 (q : nat) : term256 q.
Proof. exact (EQ_MP (@lem5472658 q) (@lem5472657 q)). Qed.
Lemma lem5472660 (x : nat) : term255 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5472661 (x : nat) : (term255 x) = (term256 x).
Proof. exact (eq_refl (term255 x)). Qed.
Lemma lem5472662 (x : nat) : term256 x.
Proof. exact (EQ_MP (@lem5472661 x) (@lem5472660 x)). Qed.
Lemma lem5472663 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term257 _70580 _70581 _70582 _70584 _70583) = (term258 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem2318604 (term258 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472698 (_70581 : int) (_70580 : int) : (term259 _70581 _70580) = (int_lt _70581 _70580).
Proof. exact (@lem16933 (int_lt _70581 _70580)). Qed.
Lemma lem5472701 (_70582 : int) (_70580 : int) : (term260 _70582 _70580) = (int_le _70582 _70580).
Proof. exact (@lem16933 (int_le _70582 _70580)). Qed.
Lemma lem5472704 (_70581 : int) (_70583 : int) : (term260 _70581 _70583) = (int_le _70581 _70583).
Proof. exact (@lem16933 (int_le _70581 _70583)). Qed.
Lemma lem5472705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472706 (_70582 : int) (_70580 : int) : (term261 _70582 _70580) = (term262 _70582 _70580).
Proof. exact (MK_COMB (@lem5472705) (@lem5472701 _70582 _70580)). Qed.
Lemma lem5472707 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term263 _70582 _70580 _70581 _70583) = (term264 _70582 _70580 _70581 _70583).
Proof. exact (MK_COMB (@lem5472706 _70582 _70580) (@lem5472704 _70581 _70583)). Qed.
Lemma lem5472708 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term265 _70582 _70580 _70581 _70583) = (term263 _70582 _70580 _70581 _70583).
Proof. exact (@lem17160 (term266 _70582 _70580) (term266 _70581 _70583)). Qed.
Lemma lem5472709 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term265 _70582 _70580 _70581 _70583) = (term264 _70582 _70580 _70581 _70583).
Proof. exact (TRANS (@lem5472708 _70582 _70580 _70581 _70583) (@lem5472707 _70582 _70580 _70581 _70583)). Qed.
Lemma lem5472710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472711 (_70581 : int) (_70580 : int) : (term267 _70581 _70580) = (term268 _70581 _70580).
Proof. exact (MK_COMB (@lem5472710) (@lem5472698 _70581 _70580)). Qed.
Lemma lem5472712 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term269 _70582 _70580 _70581 _70583) = (term270 _70582 _70580 _70581 _70583).
Proof. exact (MK_COMB (@lem5472711 _70581 _70580) (@lem5472709 _70582 _70580 _70581 _70583)). Qed.
Lemma lem5472713 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term271 _70582 _70580 _70581 _70583) = (term269 _70582 _70580 _70581 _70583).
Proof. exact (@lem17045 (term272 _70581 _70580) (term273 _70582 _70580 _70581 _70583)). Qed.
Lemma lem5472714 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term271 _70582 _70580 _70581 _70583) = (term270 _70582 _70580 _70581 _70583).
Proof. exact (TRANS (@lem5472713 _70582 _70580 _70581 _70583) (@lem5472712 _70582 _70580 _70581 _70583)). Qed.
Lemma lem5472717 (_70580 : int) (_70584 : int) : (term260 _70580 _70584) = (int_le _70580 _70584).
Proof. exact (@lem16933 (int_le _70580 _70584)). Qed.
Lemma lem5472720 (_70584 : int) (_70581 : int) : (term260 _70584 _70581) = (int_le _70584 _70581).
Proof. exact (@lem16933 (int_le _70584 _70581)). Qed.
Lemma lem5472721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472722 (_70580 : int) (_70584 : int) : (term261 _70580 _70584) = (term262 _70580 _70584).
Proof. exact (MK_COMB (@lem5472721) (@lem5472717 _70580 _70584)). Qed.
Lemma lem5472723 (_70580 : int) (_70584 : int) (_70581 : int) : (term274 _70580 _70584 _70581) = (term275 _70580 _70584 _70581).
Proof. exact (MK_COMB (@lem5472722 _70580 _70584) (@lem5472720 _70584 _70581)). Qed.
Lemma lem5472724 (_70580 : int) (_70584 : int) (_70581 : int) : (term276 _70580 _70584 _70581) = (term274 _70580 _70584 _70581).
Proof. exact (@lem17160 (term266 _70580 _70584) (term266 _70584 _70581)). Qed.
Lemma lem5472725 (_70580 : int) (_70584 : int) (_70581 : int) : (term276 _70580 _70584 _70581) = (term275 _70580 _70584 _70581).
Proof. exact (TRANS (@lem5472724 _70580 _70584 _70581) (@lem5472723 _70580 _70584 _70581)). Qed.
Lemma lem5472732 (_70582 : int) (_70584 : int) (_70583 : int) : (term277 _70582 _70584 _70583) = (term278 _70582 _70584 _70583).
Proof. exact (@lem17045 (int_le _70582 _70584) (int_le _70584 _70583)). Qed.
Lemma lem5472733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472734 (_70580 : int) (_70584 : int) (_70581 : int) : (term279 _70580 _70584 _70581) = (term280 _70580 _70584 _70581).
Proof. exact (MK_COMB (@lem5472733) (@lem5472725 _70580 _70584 _70581)). Qed.
Lemma lem5472735 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term281 _70580 _70581 _70582 _70584 _70583) = (term282 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5472734 _70580 _70584 _70581) (@lem5472732 _70582 _70584 _70583)). Qed.
Lemma lem5472736 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term283 _70580 _70581 _70582 _70584 _70583) = (term281 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem17160 (term278 _70580 _70584 _70581) (term275 _70582 _70584 _70583)). Qed.
Lemma lem5472737 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term283 _70580 _70581 _70582 _70584 _70583) = (term282 _70580 _70581 _70582 _70584 _70583).
Proof. exact (TRANS (@lem5472736 _70580 _70581 _70582 _70584 _70583) (@lem5472735 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472739 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term284 _70582 _70580 _70581 _70583) = (term285 _70582 _70580 _70581 _70583).
Proof. exact (MK_COMB (@lem5472738) (@lem5472714 _70582 _70580 _70581 _70583)). Qed.
Lemma lem5472740 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term286 _70580 _70581 _70582 _70584 _70583) = (term287 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5472739 _70582 _70580 _70581 _70583) (@lem5472737 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472741 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term288 _70580 _70581 _70582 _70584 _70583) = (term286 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem17160 (term289 _70582 _70580 _70581 _70583) (term290 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472742 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term288 _70580 _70581 _70582 _70584 _70583) = (term287 _70580 _70581 _70582 _70584 _70583).
Proof. exact (TRANS (@lem5472741 _70580 _70581 _70582 _70584 _70583) (@lem5472740 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472744 (_70584 : int) : (term291 _70584) = (term291 _70584).
Proof. exact (eq_refl (term291 _70584)). Qed.
Lemma lem5472745 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term292 _70580 _70581 _70582 _70584 _70583) = (term293 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5472744 _70584) (@lem5472742 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472746 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term294 _70580 _70581 _70582 _70584 _70583) = (term292 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem17362 (term295 _70584) (term296 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472747 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term294 _70580 _70581 _70582 _70584 _70583) = (term293 _70580 _70581 _70582 _70584 _70583).
Proof. exact (TRANS (@lem5472746 _70580 _70581 _70582 _70584 _70583) (@lem5472745 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472749 (_70583 : int) : (term291 _70583) = (term291 _70583).
Proof. exact (eq_refl (term291 _70583)). Qed.
Lemma lem5472750 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term297 _70580 _70581 _70582 _70584 _70583) = (term298 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5472749 _70583) (@lem5472747 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472751 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term299 _70580 _70581 _70582 _70584 _70583) = (term297 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem17362 (term295 _70583) (term300 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472752 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term299 _70580 _70581 _70582 _70584 _70583) = (term298 _70580 _70581 _70582 _70584 _70583).
Proof. exact (TRANS (@lem5472751 _70580 _70581 _70582 _70584 _70583) (@lem5472750 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472754 (_70582 : int) : (term291 _70582) = (term291 _70582).
Proof. exact (eq_refl (term291 _70582)). Qed.
Lemma lem5472755 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term301 _70580 _70581 _70582 _70584 _70583) = (term302 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5472754 _70582) (@lem5472752 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472756 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term303 _70580 _70581 _70582 _70584 _70583) = (term301 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem17362 (term295 _70582) (term304 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472757 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term303 _70580 _70581 _70582 _70584 _70583) = (term302 _70580 _70581 _70582 _70584 _70583).
Proof. exact (TRANS (@lem5472756 _70580 _70581 _70582 _70584 _70583) (@lem5472755 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472759 (_70581 : int) : (term291 _70581) = (term291 _70581).
Proof. exact (eq_refl (term291 _70581)). Qed.
Lemma lem5472760 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term305 _70580 _70581 _70582 _70584 _70583) = (term306 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5472759 _70581) (@lem5472757 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472761 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term307 _70580 _70581 _70582 _70584 _70583) = (term305 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem17362 (term295 _70581) (term308 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472762 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term307 _70580 _70581 _70582 _70584 _70583) = (term306 _70580 _70581 _70582 _70584 _70583).
Proof. exact (TRANS (@lem5472761 _70580 _70581 _70582 _70584 _70583) (@lem5472760 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472764 (_70580 : int) : (term291 _70580) = (term291 _70580).
Proof. exact (eq_refl (term291 _70580)). Qed.
Lemma lem5472765 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term309 _70580 _70581 _70582 _70584 _70583) = (term310 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5472764 _70580) (@lem5472762 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472766 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term311 _70580 _70581 _70582 _70584 _70583) = (term309 _70580 _70581 _70582 _70584 _70583).
Proof. exact (@lem17362 (term295 _70580) (term312 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472818 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term311 _70580 _70581 _70582 _70584 _70583) = (term310 _70580 _70581 _70582 _70584 _70583).
Proof. exact (TRANS (@lem5472766 _70580 _70581 _70582 _70584 _70583) (@lem5472765 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5472821 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472822 (_70580 : int) : (term295 _70580) = (term314 _70580).
Proof. exact (@lem5472821 term315 _70580). Qed.
Lemma lem5472824 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472825 : term317 = term318.
Proof. exact (@lem5472824 (NUMERAL 0)). Qed.
Lemma lem5472826 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472827 : term319 = term320.
Proof. exact (MK_COMB (@lem5472826) (@lem5472825)). Qed.
Lemma lem5472828 (_70580 : int) : (real_of_int _70580) = (real_of_int _70580).
Proof. exact (eq_refl (real_of_int _70580)). Qed.
Lemma lem5472829 (_70580 : int) : (term314 _70580) = (term321 _70580).
Proof. exact (MK_COMB (@lem5472827) (@lem5472828 _70580)). Qed.
Lemma lem5472831 (_70580 : int) : (term295 _70580) = (term321 _70580).
Proof. exact (TRANS (@lem5472822 _70580) (@lem5472829 _70580)). Qed.
Lemma lem5472834 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472835 (_70581 : int) : (term295 _70581) = (term314 _70581).
Proof. exact (@lem5472834 term315 _70581). Qed.
Lemma lem5472837 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472838 : term317 = term318.
Proof. exact (@lem5472837 (NUMERAL 0)). Qed.
Lemma lem5472839 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472840 : term319 = term320.
Proof. exact (MK_COMB (@lem5472839) (@lem5472838)). Qed.
Lemma lem5472841 (_70581 : int) : (real_of_int _70581) = (real_of_int _70581).
Proof. exact (eq_refl (real_of_int _70581)). Qed.
Lemma lem5472842 (_70581 : int) : (term314 _70581) = (term321 _70581).
Proof. exact (MK_COMB (@lem5472840) (@lem5472841 _70581)). Qed.
Lemma lem5472844 (_70581 : int) : (term295 _70581) = (term321 _70581).
Proof. exact (TRANS (@lem5472835 _70581) (@lem5472842 _70581)). Qed.
Lemma lem5472847 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472848 (_70582 : int) : (term295 _70582) = (term314 _70582).
Proof. exact (@lem5472847 term315 _70582). Qed.
Lemma lem5472850 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472851 : term317 = term318.
Proof. exact (@lem5472850 (NUMERAL 0)). Qed.
Lemma lem5472852 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472853 : term319 = term320.
Proof. exact (MK_COMB (@lem5472852) (@lem5472851)). Qed.
Lemma lem5472854 (_70582 : int) : (real_of_int _70582) = (real_of_int _70582).
Proof. exact (eq_refl (real_of_int _70582)). Qed.
Lemma lem5472855 (_70582 : int) : (term314 _70582) = (term321 _70582).
Proof. exact (MK_COMB (@lem5472853) (@lem5472854 _70582)). Qed.
Lemma lem5472857 (_70582 : int) : (term295 _70582) = (term321 _70582).
Proof. exact (TRANS (@lem5472848 _70582) (@lem5472855 _70582)). Qed.
Lemma lem5472860 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472861 (_70583 : int) : (term295 _70583) = (term314 _70583).
Proof. exact (@lem5472860 term315 _70583). Qed.
Lemma lem5472863 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472864 : term317 = term318.
Proof. exact (@lem5472863 (NUMERAL 0)). Qed.
Lemma lem5472865 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472866 : term319 = term320.
Proof. exact (MK_COMB (@lem5472865) (@lem5472864)). Qed.
Lemma lem5472867 (_70583 : int) : (real_of_int _70583) = (real_of_int _70583).
Proof. exact (eq_refl (real_of_int _70583)). Qed.
Lemma lem5472868 (_70583 : int) : (term314 _70583) = (term321 _70583).
Proof. exact (MK_COMB (@lem5472866) (@lem5472867 _70583)). Qed.
Lemma lem5472870 (_70583 : int) : (term295 _70583) = (term321 _70583).
Proof. exact (TRANS (@lem5472861 _70583) (@lem5472868 _70583)). Qed.
Lemma lem5472873 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472874 (_70584 : int) : (term295 _70584) = (term314 _70584).
Proof. exact (@lem5472873 term315 _70584). Qed.
Lemma lem5472876 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472877 : term317 = term318.
Proof. exact (@lem5472876 (NUMERAL 0)). Qed.
Lemma lem5472878 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472879 : term319 = term320.
Proof. exact (MK_COMB (@lem5472878) (@lem5472877)). Qed.
Lemma lem5472880 (_70584 : int) : (real_of_int _70584) = (real_of_int _70584).
Proof. exact (eq_refl (real_of_int _70584)). Qed.
Lemma lem5472881 (_70584 : int) : (term314 _70584) = (term321 _70584).
Proof. exact (MK_COMB (@lem5472879) (@lem5472880 _70584)). Qed.
Lemma lem5472883 (_70584 : int) : (term295 _70584) = (term321 _70584).
Proof. exact (TRANS (@lem5472874 _70584) (@lem5472881 _70584)). Qed.
Lemma lem5472885 (x : int) (y : int) : (int_lt x y) = (term322 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5472886 (_70581 : int) (_70580 : int) : (int_lt _70581 _70580) = (term322 _70581 _70580).
Proof. exact (@lem5472885 _70581 _70580). Qed.
Lemma lem5472888 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472889 (_70581 : int) (_70580 : int) : (term322 _70581 _70580) = (term323 _70581 _70580).
Proof. exact (@lem5472888 (term324 _70581) _70580). Qed.
Lemma lem5472891 (x : int) (y : int) : (term325 x y) = (term326 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5472892 (_70581 : int) : (term327 _70581) = (term328 _70581).
Proof. exact (@lem5472891 _70581 term329). Qed.
Lemma lem5472894 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472895 : term330 = term331.
Proof. exact (@lem5472894 term332). Qed.
Lemma lem5472896 (_70581 : int) : (term333 _70581) = (term333 _70581).
Proof. exact (eq_refl (term333 _70581)). Qed.
Lemma lem5472897 (_70581 : int) : (term328 _70581) = (term334 _70581).
Proof. exact (MK_COMB (@lem5472896 _70581) (@lem5472895)). Qed.
Lemma lem5472898 (_70581 : int) : (term327 _70581) = (term334 _70581).
Proof. exact (TRANS (@lem5472892 _70581) (@lem5472897 _70581)). Qed.
Lemma lem5472899 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472900 (_70581 : int) : (term335 _70581) = (term336 _70581).
Proof. exact (MK_COMB (@lem5472899) (@lem5472898 _70581)). Qed.
Lemma lem5472901 (_70580 : int) : (real_of_int _70580) = (real_of_int _70580).
Proof. exact (eq_refl (real_of_int _70580)). Qed.
Lemma lem5472902 (_70581 : int) (_70580 : int) : (term323 _70581 _70580) = (term337 _70581 _70580).
Proof. exact (MK_COMB (@lem5472900 _70581) (@lem5472901 _70580)). Qed.
Lemma lem5472903 (_70581 : int) (_70580 : int) : (term322 _70581 _70580) = (term337 _70581 _70580).
Proof. exact (TRANS (@lem5472889 _70581 _70580) (@lem5472902 _70581 _70580)). Qed.
Lemma lem5472904 (_70581 : int) (_70580 : int) : (int_lt _70581 _70580) = (term337 _70581 _70580).
Proof. exact (TRANS (@lem5472886 _70581 _70580) (@lem5472903 _70581 _70580)). Qed.
Lemma lem5472907 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472909 (_70582 : int) (_70580 : int) : (int_le _70582 _70580) = (term313 _70582 _70580).
Proof. exact (@lem5472907 _70582 _70580). Qed.
Lemma lem5472912 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472914 (_70581 : int) (_70583 : int) : (int_le _70581 _70583) = (term313 _70581 _70583).
Proof. exact (@lem5472912 _70581 _70583). Qed.
Lemma lem5472915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472916 (_70582 : int) (_70580 : int) : (term262 _70582 _70580) = (term338 _70582 _70580).
Proof. exact (MK_COMB (@lem5472915) (@lem5472909 _70582 _70580)). Qed.
Lemma lem5472917 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term264 _70582 _70580 _70581 _70583) = (term339 _70582 _70580 _70581 _70583).
Proof. exact (MK_COMB (@lem5472916 _70582 _70580) (@lem5472914 _70581 _70583)). Qed.
Lemma lem5472918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472919 (_70581 : int) (_70580 : int) : (term268 _70581 _70580) = (term340 _70581 _70580).
Proof. exact (MK_COMB (@lem5472918) (@lem5472904 _70581 _70580)). Qed.
Lemma lem5472920 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term270 _70582 _70580 _70581 _70583) = (term341 _70582 _70580 _70581 _70583).
Proof. exact (MK_COMB (@lem5472919 _70581 _70580) (@lem5472917 _70582 _70580 _70581 _70583)). Qed.
Lemma lem5472923 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472925 (_70580 : int) (_70584 : int) : (int_le _70580 _70584) = (term313 _70580 _70584).
Proof. exact (@lem5472923 _70580 _70584). Qed.
Lemma lem5472928 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472930 (_70584 : int) (_70581 : int) : (int_le _70584 _70581) = (term313 _70584 _70581).
Proof. exact (@lem5472928 _70584 _70581). Qed.
Lemma lem5472931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472932 (_70580 : int) (_70584 : int) : (term262 _70580 _70584) = (term338 _70580 _70584).
Proof. exact (MK_COMB (@lem5472931) (@lem5472925 _70580 _70584)). Qed.
Lemma lem5472933 (_70580 : int) (_70584 : int) (_70581 : int) : (term275 _70580 _70584 _70581) = (term342 _70580 _70584 _70581).
Proof. exact (MK_COMB (@lem5472932 _70580 _70584) (@lem5472930 _70584 _70581)). Qed.
Lemma lem5472935 (y : int) (x : int) : (term266 x y) = (term322 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5472936 (_70584 : int) (_70582 : int) : (term266 _70582 _70584) = (term322 _70584 _70582).
Proof. exact (@lem5472935 _70584 _70582). Qed.
Lemma lem5472938 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472939 (_70584 : int) (_70582 : int) : (term322 _70584 _70582) = (term323 _70584 _70582).
Proof. exact (@lem5472938 (term324 _70584) _70582). Qed.
Lemma lem5472941 (x : int) (y : int) : (term325 x y) = (term326 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5472942 (_70584 : int) : (term327 _70584) = (term328 _70584).
Proof. exact (@lem5472941 _70584 term329). Qed.
Lemma lem5472944 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472945 : term330 = term331.
Proof. exact (@lem5472944 term332). Qed.
Lemma lem5472946 (_70584 : int) : (term333 _70584) = (term333 _70584).
Proof. exact (eq_refl (term333 _70584)). Qed.
Lemma lem5472947 (_70584 : int) : (term328 _70584) = (term334 _70584).
Proof. exact (MK_COMB (@lem5472946 _70584) (@lem5472945)). Qed.
Lemma lem5472948 (_70584 : int) : (term327 _70584) = (term334 _70584).
Proof. exact (TRANS (@lem5472942 _70584) (@lem5472947 _70584)). Qed.
Lemma lem5472949 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472950 (_70584 : int) : (term335 _70584) = (term336 _70584).
Proof. exact (MK_COMB (@lem5472949) (@lem5472948 _70584)). Qed.
Lemma lem5472951 (_70582 : int) : (real_of_int _70582) = (real_of_int _70582).
Proof. exact (eq_refl (real_of_int _70582)). Qed.
Lemma lem5472952 (_70584 : int) (_70582 : int) : (term323 _70584 _70582) = (term337 _70584 _70582).
Proof. exact (MK_COMB (@lem5472950 _70584) (@lem5472951 _70582)). Qed.
Lemma lem5472953 (_70584 : int) (_70582 : int) : (term322 _70584 _70582) = (term337 _70584 _70582).
Proof. exact (TRANS (@lem5472939 _70584 _70582) (@lem5472952 _70584 _70582)). Qed.
Lemma lem5472954 (_70584 : int) (_70582 : int) : (term266 _70582 _70584) = (term337 _70584 _70582).
Proof. exact (TRANS (@lem5472936 _70584 _70582) (@lem5472953 _70584 _70582)). Qed.
Lemma lem5472956 (y : int) (x : int) : (term266 x y) = (term322 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5472957 (_70583 : int) (_70584 : int) : (term266 _70584 _70583) = (term322 _70583 _70584).
Proof. exact (@lem5472956 _70583 _70584). Qed.
Lemma lem5472959 (x : int) (y : int) : (int_le x y) = (term313 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5472960 (_70583 : int) (_70584 : int) : (term322 _70583 _70584) = (term323 _70583 _70584).
Proof. exact (@lem5472959 (term324 _70583) _70584). Qed.
Lemma lem5472962 (x : int) (y : int) : (term325 x y) = (term326 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5472963 (_70583 : int) : (term327 _70583) = (term328 _70583).
Proof. exact (@lem5472962 _70583 term329). Qed.
Lemma lem5472965 (n : nat) : (term316 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5472966 : term330 = term331.
Proof. exact (@lem5472965 term332). Qed.
Lemma lem5472967 (_70583 : int) : (term333 _70583) = (term333 _70583).
Proof. exact (eq_refl (term333 _70583)). Qed.
Lemma lem5472968 (_70583 : int) : (term328 _70583) = (term334 _70583).
Proof. exact (MK_COMB (@lem5472967 _70583) (@lem5472966)). Qed.
Lemma lem5472969 (_70583 : int) : (term327 _70583) = (term334 _70583).
Proof. exact (TRANS (@lem5472963 _70583) (@lem5472968 _70583)). Qed.
Lemma lem5472970 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5472971 (_70583 : int) : (term335 _70583) = (term336 _70583).
Proof. exact (MK_COMB (@lem5472970) (@lem5472969 _70583)). Qed.
Lemma lem5472972 (_70584 : int) : (real_of_int _70584) = (real_of_int _70584).
Proof. exact (eq_refl (real_of_int _70584)). Qed.
Lemma lem5472973 (_70583 : int) (_70584 : int) : (term323 _70583 _70584) = (term337 _70583 _70584).
Proof. exact (MK_COMB (@lem5472971 _70583) (@lem5472972 _70584)). Qed.
Lemma lem5472974 (_70583 : int) (_70584 : int) : (term322 _70583 _70584) = (term337 _70583 _70584).
Proof. exact (TRANS (@lem5472960 _70583 _70584) (@lem5472973 _70583 _70584)). Qed.
Lemma lem5472975 (_70583 : int) (_70584 : int) : (term266 _70584 _70583) = (term337 _70583 _70584).
Proof. exact (TRANS (@lem5472957 _70583 _70584) (@lem5472974 _70583 _70584)). Qed.
Lemma lem5472976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5472977 (_70584 : int) (_70582 : int) : (term343 _70582 _70584) = (term340 _70584 _70582).
Proof. exact (MK_COMB (@lem5472976) (@lem5472954 _70584 _70582)). Qed.
Lemma lem5472978 (_70582 : int) (_70583 : int) (_70584 : int) : (term278 _70582 _70584 _70583) = (term344 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472977 _70584 _70582) (@lem5472975 _70583 _70584)). Qed.
Lemma lem5472979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472980 (_70580 : int) (_70584 : int) (_70581 : int) : (term280 _70580 _70584 _70581) = (term345 _70580 _70584 _70581).
Proof. exact (MK_COMB (@lem5472979) (@lem5472933 _70580 _70584 _70581)). Qed.
Lemma lem5472981 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term282 _70580 _70581 _70582 _70584 _70583) = (term346 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472980 _70580 _70584 _70581) (@lem5472978 _70582 _70583 _70584)). Qed.
Lemma lem5472982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472983 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) : (term285 _70582 _70580 _70581 _70583) = (term347 _70582 _70580 _70581 _70583).
Proof. exact (MK_COMB (@lem5472982) (@lem5472920 _70582 _70580 _70581 _70583)). Qed.
Lemma lem5472984 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term287 _70580 _70581 _70582 _70584 _70583) = (term348 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472983 _70582 _70580 _70581 _70583) (@lem5472981 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5472985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472986 (_70584 : int) : (term291 _70584) = (term349 _70584).
Proof. exact (MK_COMB (@lem5472985) (@lem5472883 _70584)). Qed.
Lemma lem5472987 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term293 _70580 _70581 _70582 _70584 _70583) = (term350 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472986 _70584) (@lem5472984 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5472988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472989 (_70583 : int) : (term291 _70583) = (term349 _70583).
Proof. exact (MK_COMB (@lem5472988) (@lem5472870 _70583)). Qed.
Lemma lem5472990 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term298 _70580 _70581 _70582 _70584 _70583) = (term351 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472989 _70583) (@lem5472987 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5472991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472992 (_70582 : int) : (term291 _70582) = (term349 _70582).
Proof. exact (MK_COMB (@lem5472991) (@lem5472857 _70582)). Qed.
Lemma lem5472993 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term302 _70580 _70581 _70582 _70584 _70583) = (term352 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472992 _70582) (@lem5472990 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5472994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472995 (_70581 : int) : (term291 _70581) = (term349 _70581).
Proof. exact (MK_COMB (@lem5472994) (@lem5472844 _70581)). Qed.
Lemma lem5472996 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term306 _70580 _70581 _70582 _70584 _70583) = (term353 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472995 _70581) (@lem5472993 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5472997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5472998 (_70580 : int) : (term291 _70580) = (term349 _70580).
Proof. exact (MK_COMB (@lem5472997) (@lem5472831 _70580)). Qed.
Lemma lem5472999 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term310 _70580 _70581 _70582 _70584 _70583) = (term354 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5472998 _70580) (@lem5472996 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473000 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term311 _70580 _70581 _70582 _70584 _70583) = (term354 _70580 _70581 _70582 _70583 _70584).
Proof. exact (TRANS (@lem5472818 _70580 _70581 _70582 _70584 _70583) (@lem5472999 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473004 (t : Prop) : (term191 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5473120 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term355 _70580 _70581 _70582 _70583 _70584) = (term354 _70580 _70581 _70582 _70583 _70584).
Proof. exact (@lem5473004 (term354 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473121 (_70580 : int) : (term321 _70580) = (term356 _70580).
Proof. exact (@lem1988287 (real_of_int _70580) term318). Qed.
Lemma lem5473127 (_70580 : int) : (term357 _70580) = (term358 _70580).
Proof. exact (@lem1982792 (real_of_int _70580) term318). Qed.
Lemma lem5473129 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473130 : term318 = term360.
Proof. exact (@lem5473129 (NUMERAL 0)). Qed.
Lemma lem5473132 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473133 : term363 = term364.
Proof. exact (@lem5473132 term332). Qed.
Lemma lem5473134 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473135 : term365 = term366.
Proof. exact (MK_COMB (@lem5473134) (@lem5473133)). Qed.
Lemma lem5473136 : term367 = term368.
Proof. exact (MK_COMB (@lem5473135) (@lem5473130)). Qed.
Lemma lem5473137 : term368 = term369.
Proof. exact (@lem1981613 term363 term318 term331 term331). Qed.
Lemma lem5473139 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473140 : term372 = term373.
Proof. exact (@lem5473139 term332 term332). Qed.
Lemma lem5473141 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473142 : term375 = term332.
Proof. exact (EQ_MP (@lem5473141) (@lem940073)). Qed.
Lemma lem5473143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473144 : term373 = term331.
Proof. exact (MK_COMB (@lem5473143) (@lem5473142)). Qed.
Lemma lem5473145 : term372 = term331.
Proof. exact (TRANS (@lem5473140) (@lem5473144)). Qed.
Lemma lem5473147 (x : nat) : (term376 x) = term318.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5473148 : term367 = term318.
Proof. exact (@lem5473147 term332). Qed.
Lemma lem5473149 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473150 : term377 = term378.
Proof. exact (MK_COMB (@lem5473149) (@lem5473148)). Qed.
Lemma lem5473151 : term369 = term360.
Proof. exact (MK_COMB (@lem5473150) (@lem5473145)). Qed.
Lemma lem5473152 : term368 = term360.
Proof. exact (TRANS (@lem5473137) (@lem5473151)). Qed.
Lemma lem5473153 : term367 = term360.
Proof. exact (TRANS (@lem5473136) (@lem5473152)). Qed.
Lemma lem5473155 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473156 : term360 = term318.
Proof. exact (@lem5473155 term318). Qed.
Lemma lem5473157 : term367 = term318.
Proof. exact (TRANS (@lem5473153) (@lem5473156)). Qed.
Lemma lem5473158 (_70580 : int) : (term333 _70580) = (term333 _70580).
Proof. exact (eq_refl (term333 _70580)). Qed.
Lemma lem5473159 (_70580 : int) : (term358 _70580) = (term380 _70580).
Proof. exact (MK_COMB (@lem5473158 _70580) (@lem5473157)). Qed.
Lemma lem5473160 (_70580 : int) : (term380 _70580) = (real_of_int _70580).
Proof. exact (@lem1982723 (real_of_int _70580)). Qed.
Lemma lem5473161 (_70580 : int) : (term358 _70580) = (real_of_int _70580).
Proof. exact (TRANS (@lem5473159 _70580) (@lem5473160 _70580)). Qed.
Lemma lem5473163 (_70580 : int) : (term357 _70580) = (real_of_int _70580).
Proof. exact (TRANS (@lem5473127 _70580) (@lem5473161 _70580)). Qed.
Lemma lem5473164 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473165 (_70580 : int) : (term381 _70580) = (term382 _70580).
Proof. exact (MK_COMB (@lem5473164) (@lem5473163 _70580)). Qed.
Lemma lem5473166 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473167 (_70580 : int) : (term356 _70580) = (term383 _70580).
Proof. exact (MK_COMB (@lem5473165 _70580) (@lem5473166)). Qed.
Lemma lem5473168 (_70580 : int) : (term321 _70580) = (term383 _70580).
Proof. exact (TRANS (@lem5473121 _70580) (@lem5473167 _70580)). Qed.
Lemma lem5473169 (_70581 : int) : (term321 _70581) = (term356 _70581).
Proof. exact (@lem1988287 (real_of_int _70581) term318). Qed.
Lemma lem5473175 (_70581 : int) : (term357 _70581) = (term358 _70581).
Proof. exact (@lem1982792 (real_of_int _70581) term318). Qed.
Lemma lem5473177 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473178 : term318 = term360.
Proof. exact (@lem5473177 (NUMERAL 0)). Qed.
Lemma lem5473180 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473181 : term363 = term364.
Proof. exact (@lem5473180 term332). Qed.
Lemma lem5473182 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473183 : term365 = term366.
Proof. exact (MK_COMB (@lem5473182) (@lem5473181)). Qed.
Lemma lem5473184 : term367 = term368.
Proof. exact (MK_COMB (@lem5473183) (@lem5473178)). Qed.
Lemma lem5473185 : term368 = term369.
Proof. exact (@lem1981613 term363 term318 term331 term331). Qed.
Lemma lem5473187 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473188 : term372 = term373.
Proof. exact (@lem5473187 term332 term332). Qed.
Lemma lem5473189 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473190 : term375 = term332.
Proof. exact (EQ_MP (@lem5473189) (@lem940073)). Qed.
Lemma lem5473191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473192 : term373 = term331.
Proof. exact (MK_COMB (@lem5473191) (@lem5473190)). Qed.
Lemma lem5473193 : term372 = term331.
Proof. exact (TRANS (@lem5473188) (@lem5473192)). Qed.
Lemma lem5473195 (x : nat) : (term376 x) = term318.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5473196 : term367 = term318.
Proof. exact (@lem5473195 term332). Qed.
Lemma lem5473197 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473198 : term377 = term378.
Proof. exact (MK_COMB (@lem5473197) (@lem5473196)). Qed.
Lemma lem5473199 : term369 = term360.
Proof. exact (MK_COMB (@lem5473198) (@lem5473193)). Qed.
Lemma lem5473200 : term368 = term360.
Proof. exact (TRANS (@lem5473185) (@lem5473199)). Qed.
Lemma lem5473201 : term367 = term360.
Proof. exact (TRANS (@lem5473184) (@lem5473200)). Qed.
Lemma lem5473203 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473204 : term360 = term318.
Proof. exact (@lem5473203 term318). Qed.
Lemma lem5473205 : term367 = term318.
Proof. exact (TRANS (@lem5473201) (@lem5473204)). Qed.
Lemma lem5473206 (_70581 : int) : (term333 _70581) = (term333 _70581).
Proof. exact (eq_refl (term333 _70581)). Qed.
Lemma lem5473207 (_70581 : int) : (term358 _70581) = (term380 _70581).
Proof. exact (MK_COMB (@lem5473206 _70581) (@lem5473205)). Qed.
Lemma lem5473208 (_70581 : int) : (term380 _70581) = (real_of_int _70581).
Proof. exact (@lem1982723 (real_of_int _70581)). Qed.
Lemma lem5473209 (_70581 : int) : (term358 _70581) = (real_of_int _70581).
Proof. exact (TRANS (@lem5473207 _70581) (@lem5473208 _70581)). Qed.
Lemma lem5473211 (_70581 : int) : (term357 _70581) = (real_of_int _70581).
Proof. exact (TRANS (@lem5473175 _70581) (@lem5473209 _70581)). Qed.
Lemma lem5473212 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473213 (_70581 : int) : (term381 _70581) = (term382 _70581).
Proof. exact (MK_COMB (@lem5473212) (@lem5473211 _70581)). Qed.
Lemma lem5473214 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473215 (_70581 : int) : (term356 _70581) = (term383 _70581).
Proof. exact (MK_COMB (@lem5473213 _70581) (@lem5473214)). Qed.
Lemma lem5473216 (_70581 : int) : (term321 _70581) = (term383 _70581).
Proof. exact (TRANS (@lem5473169 _70581) (@lem5473215 _70581)). Qed.
Lemma lem5473217 (_70582 : int) : (term321 _70582) = (term356 _70582).
Proof. exact (@lem1988287 (real_of_int _70582) term318). Qed.
Lemma lem5473223 (_70582 : int) : (term357 _70582) = (term358 _70582).
Proof. exact (@lem1982792 (real_of_int _70582) term318). Qed.
Lemma lem5473225 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473226 : term318 = term360.
Proof. exact (@lem5473225 (NUMERAL 0)). Qed.
Lemma lem5473228 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473229 : term363 = term364.
Proof. exact (@lem5473228 term332). Qed.
Lemma lem5473230 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473231 : term365 = term366.
Proof. exact (MK_COMB (@lem5473230) (@lem5473229)). Qed.
Lemma lem5473232 : term367 = term368.
Proof. exact (MK_COMB (@lem5473231) (@lem5473226)). Qed.
Lemma lem5473233 : term368 = term369.
Proof. exact (@lem1981613 term363 term318 term331 term331). Qed.
Lemma lem5473235 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473236 : term372 = term373.
Proof. exact (@lem5473235 term332 term332). Qed.
Lemma lem5473237 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473238 : term375 = term332.
Proof. exact (EQ_MP (@lem5473237) (@lem940073)). Qed.
Lemma lem5473239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473240 : term373 = term331.
Proof. exact (MK_COMB (@lem5473239) (@lem5473238)). Qed.
Lemma lem5473241 : term372 = term331.
Proof. exact (TRANS (@lem5473236) (@lem5473240)). Qed.
Lemma lem5473243 (x : nat) : (term376 x) = term318.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5473244 : term367 = term318.
Proof. exact (@lem5473243 term332). Qed.
Lemma lem5473245 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473246 : term377 = term378.
Proof. exact (MK_COMB (@lem5473245) (@lem5473244)). Qed.
Lemma lem5473247 : term369 = term360.
Proof. exact (MK_COMB (@lem5473246) (@lem5473241)). Qed.
Lemma lem5473248 : term368 = term360.
Proof. exact (TRANS (@lem5473233) (@lem5473247)). Qed.
Lemma lem5473249 : term367 = term360.
Proof. exact (TRANS (@lem5473232) (@lem5473248)). Qed.
Lemma lem5473251 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473252 : term360 = term318.
Proof. exact (@lem5473251 term318). Qed.
Lemma lem5473253 : term367 = term318.
Proof. exact (TRANS (@lem5473249) (@lem5473252)). Qed.
Lemma lem5473254 (_70582 : int) : (term333 _70582) = (term333 _70582).
Proof. exact (eq_refl (term333 _70582)). Qed.
Lemma lem5473255 (_70582 : int) : (term358 _70582) = (term380 _70582).
Proof. exact (MK_COMB (@lem5473254 _70582) (@lem5473253)). Qed.
Lemma lem5473256 (_70582 : int) : (term380 _70582) = (real_of_int _70582).
Proof. exact (@lem1982723 (real_of_int _70582)). Qed.
Lemma lem5473257 (_70582 : int) : (term358 _70582) = (real_of_int _70582).
Proof. exact (TRANS (@lem5473255 _70582) (@lem5473256 _70582)). Qed.
Lemma lem5473259 (_70582 : int) : (term357 _70582) = (real_of_int _70582).
Proof. exact (TRANS (@lem5473223 _70582) (@lem5473257 _70582)). Qed.
Lemma lem5473260 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473261 (_70582 : int) : (term381 _70582) = (term382 _70582).
Proof. exact (MK_COMB (@lem5473260) (@lem5473259 _70582)). Qed.
Lemma lem5473262 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473263 (_70582 : int) : (term356 _70582) = (term383 _70582).
Proof. exact (MK_COMB (@lem5473261 _70582) (@lem5473262)). Qed.
Lemma lem5473264 (_70582 : int) : (term321 _70582) = (term383 _70582).
Proof. exact (TRANS (@lem5473217 _70582) (@lem5473263 _70582)). Qed.
Lemma lem5473265 (_70583 : int) : (term321 _70583) = (term356 _70583).
Proof. exact (@lem1988287 (real_of_int _70583) term318). Qed.
Lemma lem5473271 (_70583 : int) : (term357 _70583) = (term358 _70583).
Proof. exact (@lem1982792 (real_of_int _70583) term318). Qed.
Lemma lem5473273 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473274 : term318 = term360.
Proof. exact (@lem5473273 (NUMERAL 0)). Qed.
Lemma lem5473276 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473277 : term363 = term364.
Proof. exact (@lem5473276 term332). Qed.
Lemma lem5473278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473279 : term365 = term366.
Proof. exact (MK_COMB (@lem5473278) (@lem5473277)). Qed.
Lemma lem5473280 : term367 = term368.
Proof. exact (MK_COMB (@lem5473279) (@lem5473274)). Qed.
Lemma lem5473281 : term368 = term369.
Proof. exact (@lem1981613 term363 term318 term331 term331). Qed.
Lemma lem5473283 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473284 : term372 = term373.
Proof. exact (@lem5473283 term332 term332). Qed.
Lemma lem5473285 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473286 : term375 = term332.
Proof. exact (EQ_MP (@lem5473285) (@lem940073)). Qed.
Lemma lem5473287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473288 : term373 = term331.
Proof. exact (MK_COMB (@lem5473287) (@lem5473286)). Qed.
Lemma lem5473289 : term372 = term331.
Proof. exact (TRANS (@lem5473284) (@lem5473288)). Qed.
Lemma lem5473291 (x : nat) : (term376 x) = term318.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5473292 : term367 = term318.
Proof. exact (@lem5473291 term332). Qed.
Lemma lem5473293 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473294 : term377 = term378.
Proof. exact (MK_COMB (@lem5473293) (@lem5473292)). Qed.
Lemma lem5473295 : term369 = term360.
Proof. exact (MK_COMB (@lem5473294) (@lem5473289)). Qed.
Lemma lem5473296 : term368 = term360.
Proof. exact (TRANS (@lem5473281) (@lem5473295)). Qed.
Lemma lem5473297 : term367 = term360.
Proof. exact (TRANS (@lem5473280) (@lem5473296)). Qed.
Lemma lem5473299 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473300 : term360 = term318.
Proof. exact (@lem5473299 term318). Qed.
Lemma lem5473301 : term367 = term318.
Proof. exact (TRANS (@lem5473297) (@lem5473300)). Qed.
Lemma lem5473302 (_70583 : int) : (term333 _70583) = (term333 _70583).
Proof. exact (eq_refl (term333 _70583)). Qed.
Lemma lem5473303 (_70583 : int) : (term358 _70583) = (term380 _70583).
Proof. exact (MK_COMB (@lem5473302 _70583) (@lem5473301)). Qed.
Lemma lem5473304 (_70583 : int) : (term380 _70583) = (real_of_int _70583).
Proof. exact (@lem1982723 (real_of_int _70583)). Qed.
Lemma lem5473305 (_70583 : int) : (term358 _70583) = (real_of_int _70583).
Proof. exact (TRANS (@lem5473303 _70583) (@lem5473304 _70583)). Qed.
Lemma lem5473307 (_70583 : int) : (term357 _70583) = (real_of_int _70583).
Proof. exact (TRANS (@lem5473271 _70583) (@lem5473305 _70583)). Qed.
Lemma lem5473308 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473309 (_70583 : int) : (term381 _70583) = (term382 _70583).
Proof. exact (MK_COMB (@lem5473308) (@lem5473307 _70583)). Qed.
Lemma lem5473310 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473311 (_70583 : int) : (term356 _70583) = (term383 _70583).
Proof. exact (MK_COMB (@lem5473309 _70583) (@lem5473310)). Qed.
Lemma lem5473312 (_70583 : int) : (term321 _70583) = (term383 _70583).
Proof. exact (TRANS (@lem5473265 _70583) (@lem5473311 _70583)). Qed.
Lemma lem5473313 (_70584 : int) : (term321 _70584) = (term356 _70584).
Proof. exact (@lem1988287 (real_of_int _70584) term318). Qed.
Lemma lem5473319 (_70584 : int) : (term357 _70584) = (term358 _70584).
Proof. exact (@lem1982792 (real_of_int _70584) term318). Qed.
Lemma lem5473321 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473322 : term318 = term360.
Proof. exact (@lem5473321 (NUMERAL 0)). Qed.
Lemma lem5473324 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473325 : term363 = term364.
Proof. exact (@lem5473324 term332). Qed.
Lemma lem5473326 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473327 : term365 = term366.
Proof. exact (MK_COMB (@lem5473326) (@lem5473325)). Qed.
Lemma lem5473328 : term367 = term368.
Proof. exact (MK_COMB (@lem5473327) (@lem5473322)). Qed.
Lemma lem5473329 : term368 = term369.
Proof. exact (@lem1981613 term363 term318 term331 term331). Qed.
Lemma lem5473331 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473332 : term372 = term373.
Proof. exact (@lem5473331 term332 term332). Qed.
Lemma lem5473333 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473334 : term375 = term332.
Proof. exact (EQ_MP (@lem5473333) (@lem940073)). Qed.
Lemma lem5473335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473336 : term373 = term331.
Proof. exact (MK_COMB (@lem5473335) (@lem5473334)). Qed.
Lemma lem5473337 : term372 = term331.
Proof. exact (TRANS (@lem5473332) (@lem5473336)). Qed.
Lemma lem5473339 (x : nat) : (term376 x) = term318.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5473340 : term367 = term318.
Proof. exact (@lem5473339 term332). Qed.
Lemma lem5473341 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473342 : term377 = term378.
Proof. exact (MK_COMB (@lem5473341) (@lem5473340)). Qed.
Lemma lem5473343 : term369 = term360.
Proof. exact (MK_COMB (@lem5473342) (@lem5473337)). Qed.
Lemma lem5473344 : term368 = term360.
Proof. exact (TRANS (@lem5473329) (@lem5473343)). Qed.
Lemma lem5473345 : term367 = term360.
Proof. exact (TRANS (@lem5473328) (@lem5473344)). Qed.
Lemma lem5473347 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473348 : term360 = term318.
Proof. exact (@lem5473347 term318). Qed.
Lemma lem5473349 : term367 = term318.
Proof. exact (TRANS (@lem5473345) (@lem5473348)). Qed.
Lemma lem5473350 (_70584 : int) : (term333 _70584) = (term333 _70584).
Proof. exact (eq_refl (term333 _70584)). Qed.
Lemma lem5473351 (_70584 : int) : (term358 _70584) = (term380 _70584).
Proof. exact (MK_COMB (@lem5473350 _70584) (@lem5473349)). Qed.
Lemma lem5473352 (_70584 : int) : (term380 _70584) = (real_of_int _70584).
Proof. exact (@lem1982723 (real_of_int _70584)). Qed.
Lemma lem5473353 (_70584 : int) : (term358 _70584) = (real_of_int _70584).
Proof. exact (TRANS (@lem5473351 _70584) (@lem5473352 _70584)). Qed.
Lemma lem5473355 (_70584 : int) : (term357 _70584) = (real_of_int _70584).
Proof. exact (TRANS (@lem5473319 _70584) (@lem5473353 _70584)). Qed.
Lemma lem5473356 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473357 (_70584 : int) : (term381 _70584) = (term382 _70584).
Proof. exact (MK_COMB (@lem5473356) (@lem5473355 _70584)). Qed.
Lemma lem5473358 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473359 (_70584 : int) : (term356 _70584) = (term383 _70584).
Proof. exact (MK_COMB (@lem5473357 _70584) (@lem5473358)). Qed.
Lemma lem5473360 (_70584 : int) : (term321 _70584) = (term383 _70584).
Proof. exact (TRANS (@lem5473313 _70584) (@lem5473359 _70584)). Qed.
Lemma lem5473361 (_70580 : int) (_70581 : int) : (term337 _70581 _70580) = (term384 _70580 _70581).
Proof. exact (@lem1988287 (real_of_int _70580) (term334 _70581)). Qed.
Lemma lem5473373 (_70580 : int) (_70581 : int) : (term385 _70580 _70581) = (term386 _70580 _70581).
Proof. exact (@lem1982792 (real_of_int _70580) (term334 _70581)). Qed.
Lemma lem5473374 (_70581 : int) : (term387 _70581) = (term388 _70581).
Proof. exact (@lem1982781 (real_of_int _70581) term363 term331). Qed.
Lemma lem5473376 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473377 : term331 = term389.
Proof. exact (@lem5473376 term332). Qed.
Lemma lem5473379 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473380 : term363 = term364.
Proof. exact (@lem5473379 term332). Qed.
Lemma lem5473381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473382 : term365 = term366.
Proof. exact (MK_COMB (@lem5473381) (@lem5473380)). Qed.
Lemma lem5473383 : term390 = term391.
Proof. exact (MK_COMB (@lem5473382) (@lem5473377)). Qed.
Lemma lem5473384 : term391 = term392.
Proof. exact (@lem1981613 term363 term331 term331 term331). Qed.
Lemma lem5473386 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473387 : term372 = term373.
Proof. exact (@lem5473386 term332 term332). Qed.
Lemma lem5473388 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473389 : term375 = term332.
Proof. exact (EQ_MP (@lem5473388) (@lem940073)). Qed.
Lemma lem5473390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473391 : term373 = term331.
Proof. exact (MK_COMB (@lem5473390) (@lem5473389)). Qed.
Lemma lem5473392 : term372 = term331.
Proof. exact (TRANS (@lem5473387) (@lem5473391)). Qed.
Lemma lem5473394 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5473395 : term390 = term395.
Proof. exact (@lem5473394 term332 term332). Qed.
Lemma lem5473396 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473397 : term375 = term332.
Proof. exact (EQ_MP (@lem5473396) (@lem940073)). Qed.
Lemma lem5473398 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473399 : term373 = term331.
Proof. exact (MK_COMB (@lem5473398) (@lem5473397)). Qed.
Lemma lem5473400 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5473401 : term395 = term363.
Proof. exact (MK_COMB (@lem5473400) (@lem5473399)). Qed.
Lemma lem5473402 : term390 = term363.
Proof. exact (TRANS (@lem5473395) (@lem5473401)). Qed.
Lemma lem5473403 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473404 : term396 = term397.
Proof. exact (MK_COMB (@lem5473403) (@lem5473402)). Qed.
Lemma lem5473405 : term392 = term364.
Proof. exact (MK_COMB (@lem5473404) (@lem5473392)). Qed.
Lemma lem5473406 : term391 = term364.
Proof. exact (TRANS (@lem5473384) (@lem5473405)). Qed.
Lemma lem5473407 : term390 = term364.
Proof. exact (TRANS (@lem5473383) (@lem5473406)). Qed.
Lemma lem5473409 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473410 : term364 = term363.
Proof. exact (@lem5473409 term363). Qed.
Lemma lem5473411 : term390 = term363.
Proof. exact (TRANS (@lem5473407) (@lem5473410)). Qed.
Lemma lem5473414 (_70581 : int) : (term398 _70581) = (term398 _70581).
Proof. exact (eq_refl (term398 _70581)). Qed.
Lemma lem5473415 (_70581 : int) : (term388 _70581) = (term399 _70581).
Proof. exact (MK_COMB (@lem5473414 _70581) (@lem5473411)). Qed.
Lemma lem5473416 (_70581 : int) : (term387 _70581) = (term399 _70581).
Proof. exact (TRANS (@lem5473374 _70581) (@lem5473415 _70581)). Qed.
Lemma lem5473417 (_70580 : int) : (term333 _70580) = (term333 _70580).
Proof. exact (eq_refl (term333 _70580)). Qed.
Lemma lem5473420 (_70580 : int) (_70581 : int) : (term386 _70580 _70581) = (term400 _70580 _70581).
Proof. exact (MK_COMB (@lem5473417 _70580) (@lem5473416 _70581)). Qed.
Lemma lem5473422 (_70580 : int) (_70581 : int) : (term385 _70580 _70581) = (term400 _70580 _70581).
Proof. exact (TRANS (@lem5473373 _70580 _70581) (@lem5473420 _70580 _70581)). Qed.
Lemma lem5473423 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473424 (_70580 : int) (_70581 : int) : (term401 _70580 _70581) = (term402 _70580 _70581).
Proof. exact (MK_COMB (@lem5473423) (@lem5473422 _70580 _70581)). Qed.
Lemma lem5473425 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473426 (_70580 : int) (_70581 : int) : (term384 _70580 _70581) = (term403 _70580 _70581).
Proof. exact (MK_COMB (@lem5473424 _70580 _70581) (@lem5473425)). Qed.
Lemma lem5473427 (_70580 : int) (_70581 : int) : (term337 _70581 _70580) = (term403 _70580 _70581).
Proof. exact (TRANS (@lem5473361 _70580 _70581) (@lem5473426 _70580 _70581)). Qed.
Lemma lem5473428 (_70580 : int) (_70582 : int) : (term313 _70582 _70580) = (term404 _70580 _70582).
Proof. exact (@lem1988287 (real_of_int _70580) (real_of_int _70582)). Qed.
Lemma lem5473441 (_70580 : int) (_70582 : int) : (term405 _70580 _70582) = (term406 _70580 _70582).
Proof. exact (@lem1982792 (real_of_int _70580) (real_of_int _70582)). Qed.
Lemma lem5473442 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473443 (_70580 : int) (_70582 : int) : (term407 _70580 _70582) = (term408 _70580 _70582).
Proof. exact (MK_COMB (@lem5473442) (@lem5473441 _70580 _70582)). Qed.
Lemma lem5473444 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473445 (_70580 : int) (_70582 : int) : (term404 _70580 _70582) = (term409 _70580 _70582).
Proof. exact (MK_COMB (@lem5473443 _70580 _70582) (@lem5473444)). Qed.
Lemma lem5473446 (_70580 : int) (_70582 : int) : (term313 _70582 _70580) = (term409 _70580 _70582).
Proof. exact (TRANS (@lem5473428 _70580 _70582) (@lem5473445 _70580 _70582)). Qed.
Lemma lem5473447 (_70583 : int) (_70581 : int) : (term313 _70581 _70583) = (term404 _70583 _70581).
Proof. exact (@lem1988287 (real_of_int _70583) (real_of_int _70581)). Qed.
Lemma lem5473453 (_70583 : int) (_70581 : int) : (term405 _70583 _70581) = (term406 _70583 _70581).
Proof. exact (@lem1982792 (real_of_int _70583) (real_of_int _70581)). Qed.
Lemma lem5473458 (_70581 : int) (_70583 : int) : (term406 _70583 _70581) = (term410 _70581 _70583).
Proof. exact (@lem1982761 (term411 _70581) (real_of_int _70583)). Qed.
Lemma lem5473460 (_70581 : int) (_70583 : int) : (term405 _70583 _70581) = (term410 _70581 _70583).
Proof. exact (TRANS (@lem5473453 _70583 _70581) (@lem5473458 _70581 _70583)). Qed.
Lemma lem5473461 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473462 (_70581 : int) (_70583 : int) : (term407 _70583 _70581) = (term412 _70581 _70583).
Proof. exact (MK_COMB (@lem5473461) (@lem5473460 _70581 _70583)). Qed.
Lemma lem5473463 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473464 (_70581 : int) (_70583 : int) : (term404 _70583 _70581) = (term413 _70581 _70583).
Proof. exact (MK_COMB (@lem5473462 _70581 _70583) (@lem5473463)). Qed.
Lemma lem5473465 (_70581 : int) (_70583 : int) : (term313 _70581 _70583) = (term413 _70581 _70583).
Proof. exact (TRANS (@lem5473447 _70583 _70581) (@lem5473464 _70581 _70583)). Qed.
Lemma lem5473466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473467 (_70580 : int) (_70582 : int) : (term338 _70582 _70580) = (term414 _70580 _70582).
Proof. exact (MK_COMB (@lem5473466) (@lem5473446 _70580 _70582)). Qed.
Lemma lem5473468 (_70580 : int) (_70582 : int) (_70581 : int) (_70583 : int) : (term339 _70582 _70580 _70581 _70583) = (term415 _70580 _70582 _70581 _70583).
Proof. exact (MK_COMB (@lem5473467 _70580 _70582) (@lem5473465 _70581 _70583)). Qed.
Lemma lem5473469 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473470 (_70580 : int) (_70581 : int) : (term340 _70581 _70580) = (term416 _70580 _70581).
Proof. exact (MK_COMB (@lem5473469) (@lem5473427 _70580 _70581)). Qed.
Lemma lem5473471 (_70580 : int) (_70582 : int) (_70581 : int) (_70583 : int) : (term341 _70582 _70580 _70581 _70583) = (term417 _70580 _70582 _70581 _70583).
Proof. exact (MK_COMB (@lem5473470 _70580 _70581) (@lem5473468 _70580 _70582 _70581 _70583)). Qed.
Lemma lem5473472 (_70584 : int) (_70580 : int) : (term313 _70580 _70584) = (term404 _70584 _70580).
Proof. exact (@lem1988287 (real_of_int _70584) (real_of_int _70580)). Qed.
Lemma lem5473478 (_70584 : int) (_70580 : int) : (term405 _70584 _70580) = (term406 _70584 _70580).
Proof. exact (@lem1982792 (real_of_int _70584) (real_of_int _70580)). Qed.
Lemma lem5473483 (_70580 : int) (_70584 : int) : (term406 _70584 _70580) = (term410 _70580 _70584).
Proof. exact (@lem1982761 (term411 _70580) (real_of_int _70584)). Qed.
Lemma lem5473485 (_70580 : int) (_70584 : int) : (term405 _70584 _70580) = (term410 _70580 _70584).
Proof. exact (TRANS (@lem5473478 _70584 _70580) (@lem5473483 _70580 _70584)). Qed.
Lemma lem5473486 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473487 (_70580 : int) (_70584 : int) : (term407 _70584 _70580) = (term412 _70580 _70584).
Proof. exact (MK_COMB (@lem5473486) (@lem5473485 _70580 _70584)). Qed.
Lemma lem5473488 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473489 (_70580 : int) (_70584 : int) : (term404 _70584 _70580) = (term413 _70580 _70584).
Proof. exact (MK_COMB (@lem5473487 _70580 _70584) (@lem5473488)). Qed.
Lemma lem5473490 (_70580 : int) (_70584 : int) : (term313 _70580 _70584) = (term413 _70580 _70584).
Proof. exact (TRANS (@lem5473472 _70584 _70580) (@lem5473489 _70580 _70584)). Qed.
Lemma lem5473491 (_70581 : int) (_70584 : int) : (term313 _70584 _70581) = (term404 _70581 _70584).
Proof. exact (@lem1988287 (real_of_int _70581) (real_of_int _70584)). Qed.
Lemma lem5473504 (_70581 : int) (_70584 : int) : (term405 _70581 _70584) = (term406 _70581 _70584).
Proof. exact (@lem1982792 (real_of_int _70581) (real_of_int _70584)). Qed.
Lemma lem5473505 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473506 (_70581 : int) (_70584 : int) : (term407 _70581 _70584) = (term408 _70581 _70584).
Proof. exact (MK_COMB (@lem5473505) (@lem5473504 _70581 _70584)). Qed.
Lemma lem5473507 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473508 (_70581 : int) (_70584 : int) : (term404 _70581 _70584) = (term409 _70581 _70584).
Proof. exact (MK_COMB (@lem5473506 _70581 _70584) (@lem5473507)). Qed.
Lemma lem5473509 (_70581 : int) (_70584 : int) : (term313 _70584 _70581) = (term409 _70581 _70584).
Proof. exact (TRANS (@lem5473491 _70581 _70584) (@lem5473508 _70581 _70584)). Qed.
Lemma lem5473510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473511 (_70580 : int) (_70584 : int) : (term338 _70580 _70584) = (term418 _70580 _70584).
Proof. exact (MK_COMB (@lem5473510) (@lem5473490 _70580 _70584)). Qed.
Lemma lem5473512 (_70580 : int) (_70581 : int) (_70584 : int) : (term342 _70580 _70584 _70581) = (term419 _70580 _70581 _70584).
Proof. exact (MK_COMB (@lem5473511 _70580 _70584) (@lem5473509 _70581 _70584)). Qed.
Lemma lem5473513 (_70582 : int) (_70584 : int) : (term337 _70584 _70582) = (term384 _70582 _70584).
Proof. exact (@lem1988287 (real_of_int _70582) (term334 _70584)). Qed.
Lemma lem5473525 (_70582 : int) (_70584 : int) : (term385 _70582 _70584) = (term386 _70582 _70584).
Proof. exact (@lem1982792 (real_of_int _70582) (term334 _70584)). Qed.
Lemma lem5473526 (_70584 : int) : (term387 _70584) = (term388 _70584).
Proof. exact (@lem1982781 (real_of_int _70584) term363 term331). Qed.
Lemma lem5473528 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473529 : term331 = term389.
Proof. exact (@lem5473528 term332). Qed.
Lemma lem5473531 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473532 : term363 = term364.
Proof. exact (@lem5473531 term332). Qed.
Lemma lem5473533 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473534 : term365 = term366.
Proof. exact (MK_COMB (@lem5473533) (@lem5473532)). Qed.
Lemma lem5473535 : term390 = term391.
Proof. exact (MK_COMB (@lem5473534) (@lem5473529)). Qed.
Lemma lem5473536 : term391 = term392.
Proof. exact (@lem1981613 term363 term331 term331 term331). Qed.
Lemma lem5473538 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473539 : term372 = term373.
Proof. exact (@lem5473538 term332 term332). Qed.
Lemma lem5473540 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473541 : term375 = term332.
Proof. exact (EQ_MP (@lem5473540) (@lem940073)). Qed.
Lemma lem5473542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473543 : term373 = term331.
Proof. exact (MK_COMB (@lem5473542) (@lem5473541)). Qed.
Lemma lem5473544 : term372 = term331.
Proof. exact (TRANS (@lem5473539) (@lem5473543)). Qed.
Lemma lem5473546 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5473547 : term390 = term395.
Proof. exact (@lem5473546 term332 term332). Qed.
Lemma lem5473548 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473549 : term375 = term332.
Proof. exact (EQ_MP (@lem5473548) (@lem940073)). Qed.
Lemma lem5473550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473551 : term373 = term331.
Proof. exact (MK_COMB (@lem5473550) (@lem5473549)). Qed.
Lemma lem5473552 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5473553 : term395 = term363.
Proof. exact (MK_COMB (@lem5473552) (@lem5473551)). Qed.
Lemma lem5473554 : term390 = term363.
Proof. exact (TRANS (@lem5473547) (@lem5473553)). Qed.
Lemma lem5473555 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473556 : term396 = term397.
Proof. exact (MK_COMB (@lem5473555) (@lem5473554)). Qed.
Lemma lem5473557 : term392 = term364.
Proof. exact (MK_COMB (@lem5473556) (@lem5473544)). Qed.
Lemma lem5473558 : term391 = term364.
Proof. exact (TRANS (@lem5473536) (@lem5473557)). Qed.
Lemma lem5473559 : term390 = term364.
Proof. exact (TRANS (@lem5473535) (@lem5473558)). Qed.
Lemma lem5473561 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473562 : term364 = term363.
Proof. exact (@lem5473561 term363). Qed.
Lemma lem5473563 : term390 = term363.
Proof. exact (TRANS (@lem5473559) (@lem5473562)). Qed.
Lemma lem5473566 (_70584 : int) : (term398 _70584) = (term398 _70584).
Proof. exact (eq_refl (term398 _70584)). Qed.
Lemma lem5473567 (_70584 : int) : (term388 _70584) = (term399 _70584).
Proof. exact (MK_COMB (@lem5473566 _70584) (@lem5473563)). Qed.
Lemma lem5473568 (_70584 : int) : (term387 _70584) = (term399 _70584).
Proof. exact (TRANS (@lem5473526 _70584) (@lem5473567 _70584)). Qed.
Lemma lem5473569 (_70582 : int) : (term333 _70582) = (term333 _70582).
Proof. exact (eq_refl (term333 _70582)). Qed.
Lemma lem5473572 (_70582 : int) (_70584 : int) : (term386 _70582 _70584) = (term400 _70582 _70584).
Proof. exact (MK_COMB (@lem5473569 _70582) (@lem5473568 _70584)). Qed.
Lemma lem5473574 (_70582 : int) (_70584 : int) : (term385 _70582 _70584) = (term400 _70582 _70584).
Proof. exact (TRANS (@lem5473525 _70582 _70584) (@lem5473572 _70582 _70584)). Qed.
Lemma lem5473575 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473576 (_70582 : int) (_70584 : int) : (term401 _70582 _70584) = (term402 _70582 _70584).
Proof. exact (MK_COMB (@lem5473575) (@lem5473574 _70582 _70584)). Qed.
Lemma lem5473577 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473578 (_70582 : int) (_70584 : int) : (term384 _70582 _70584) = (term403 _70582 _70584).
Proof. exact (MK_COMB (@lem5473576 _70582 _70584) (@lem5473577)). Qed.
Lemma lem5473579 (_70582 : int) (_70584 : int) : (term337 _70584 _70582) = (term403 _70582 _70584).
Proof. exact (TRANS (@lem5473513 _70582 _70584) (@lem5473578 _70582 _70584)). Qed.
Lemma lem5473580 (_70584 : int) (_70583 : int) : (term337 _70583 _70584) = (term384 _70584 _70583).
Proof. exact (@lem1988287 (real_of_int _70584) (term334 _70583)). Qed.
Lemma lem5473592 (_70584 : int) (_70583 : int) : (term385 _70584 _70583) = (term386 _70584 _70583).
Proof. exact (@lem1982792 (real_of_int _70584) (term334 _70583)). Qed.
Lemma lem5473593 (_70583 : int) : (term387 _70583) = (term388 _70583).
Proof. exact (@lem1982781 (real_of_int _70583) term363 term331). Qed.
Lemma lem5473595 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473596 : term331 = term389.
Proof. exact (@lem5473595 term332). Qed.
Lemma lem5473598 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5473599 : term363 = term364.
Proof. exact (@lem5473598 term332). Qed.
Lemma lem5473600 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5473601 : term365 = term366.
Proof. exact (MK_COMB (@lem5473600) (@lem5473599)). Qed.
Lemma lem5473602 : term390 = term391.
Proof. exact (MK_COMB (@lem5473601) (@lem5473596)). Qed.
Lemma lem5473603 : term391 = term392.
Proof. exact (@lem1981613 term363 term331 term331 term331). Qed.
Lemma lem5473605 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473606 : term372 = term373.
Proof. exact (@lem5473605 term332 term332). Qed.
Lemma lem5473607 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473608 : term375 = term332.
Proof. exact (EQ_MP (@lem5473607) (@lem940073)). Qed.
Lemma lem5473609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473610 : term373 = term331.
Proof. exact (MK_COMB (@lem5473609) (@lem5473608)). Qed.
Lemma lem5473611 : term372 = term331.
Proof. exact (TRANS (@lem5473606) (@lem5473610)). Qed.
Lemma lem5473613 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5473614 : term390 = term395.
Proof. exact (@lem5473613 term332 term332). Qed.
Lemma lem5473615 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473616 : term375 = term332.
Proof. exact (EQ_MP (@lem5473615) (@lem940073)). Qed.
Lemma lem5473617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473618 : term373 = term331.
Proof. exact (MK_COMB (@lem5473617) (@lem5473616)). Qed.
Lemma lem5473619 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5473620 : term395 = term363.
Proof. exact (MK_COMB (@lem5473619) (@lem5473618)). Qed.
Lemma lem5473621 : term390 = term363.
Proof. exact (TRANS (@lem5473614) (@lem5473620)). Qed.
Lemma lem5473622 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5473623 : term396 = term397.
Proof. exact (MK_COMB (@lem5473622) (@lem5473621)). Qed.
Lemma lem5473624 : term392 = term364.
Proof. exact (MK_COMB (@lem5473623) (@lem5473611)). Qed.
Lemma lem5473625 : term391 = term364.
Proof. exact (TRANS (@lem5473603) (@lem5473624)). Qed.
Lemma lem5473626 : term390 = term364.
Proof. exact (TRANS (@lem5473602) (@lem5473625)). Qed.
Lemma lem5473628 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5473629 : term364 = term363.
Proof. exact (@lem5473628 term363). Qed.
Lemma lem5473630 : term390 = term363.
Proof. exact (TRANS (@lem5473626) (@lem5473629)). Qed.
Lemma lem5473633 (_70583 : int) : (term398 _70583) = (term398 _70583).
Proof. exact (eq_refl (term398 _70583)). Qed.
Lemma lem5473634 (_70583 : int) : (term388 _70583) = (term399 _70583).
Proof. exact (MK_COMB (@lem5473633 _70583) (@lem5473630)). Qed.
Lemma lem5473635 (_70583 : int) : (term387 _70583) = (term399 _70583).
Proof. exact (TRANS (@lem5473593 _70583) (@lem5473634 _70583)). Qed.
Lemma lem5473636 (_70584 : int) : (term333 _70584) = (term333 _70584).
Proof. exact (eq_refl (term333 _70584)). Qed.
Lemma lem5473637 (_70584 : int) (_70583 : int) : (term386 _70584 _70583) = (term400 _70584 _70583).
Proof. exact (MK_COMB (@lem5473636 _70584) (@lem5473635 _70583)). Qed.
Lemma lem5473642 (_70583 : int) (_70584 : int) : (term400 _70584 _70583) = (term420 _70583 _70584).
Proof. exact (@lem1982757 (term411 _70583) (real_of_int _70584) term363). Qed.
Lemma lem5473643 (_70583 : int) (_70584 : int) : (term386 _70584 _70583) = (term420 _70583 _70584).
Proof. exact (TRANS (@lem5473637 _70584 _70583) (@lem5473642 _70583 _70584)). Qed.
Lemma lem5473645 (_70583 : int) (_70584 : int) : (term385 _70584 _70583) = (term420 _70583 _70584).
Proof. exact (TRANS (@lem5473592 _70584 _70583) (@lem5473643 _70583 _70584)). Qed.
Lemma lem5473646 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473647 (_70583 : int) (_70584 : int) : (term401 _70584 _70583) = (term421 _70583 _70584).
Proof. exact (MK_COMB (@lem5473646) (@lem5473645 _70583 _70584)). Qed.
Lemma lem5473648 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473649 (_70583 : int) (_70584 : int) : (term384 _70584 _70583) = (term422 _70583 _70584).
Proof. exact (MK_COMB (@lem5473647 _70583 _70584) (@lem5473648)). Qed.
Lemma lem5473650 (_70583 : int) (_70584 : int) : (term337 _70583 _70584) = (term422 _70583 _70584).
Proof. exact (TRANS (@lem5473580 _70584 _70583) (@lem5473649 _70583 _70584)). Qed.
Lemma lem5473651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473652 (_70582 : int) (_70584 : int) : (term340 _70584 _70582) = (term416 _70582 _70584).
Proof. exact (MK_COMB (@lem5473651) (@lem5473579 _70582 _70584)). Qed.
Lemma lem5473653 (_70582 : int) (_70583 : int) (_70584 : int) : (term344 _70582 _70583 _70584) = (term423 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473652 _70582 _70584) (@lem5473650 _70583 _70584)). Qed.
Lemma lem5473654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473655 (_70580 : int) (_70581 : int) (_70584 : int) : (term345 _70580 _70584 _70581) = (term424 _70580 _70581 _70584).
Proof. exact (MK_COMB (@lem5473654) (@lem5473512 _70580 _70581 _70584)). Qed.
Lemma lem5473656 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term346 _70580 _70581 _70582 _70583 _70584) = (term425 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473655 _70580 _70581 _70584) (@lem5473653 _70582 _70583 _70584)). Qed.
Lemma lem5473657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473658 (_70580 : int) (_70582 : int) (_70581 : int) (_70583 : int) : (term347 _70582 _70580 _70581 _70583) = (term426 _70580 _70582 _70581 _70583).
Proof. exact (MK_COMB (@lem5473657) (@lem5473471 _70580 _70582 _70581 _70583)). Qed.
Lemma lem5473659 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term348 _70580 _70581 _70582 _70583 _70584) = (term427 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473658 _70580 _70582 _70581 _70583) (@lem5473656 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473661 (_70584 : int) : (term349 _70584) = (term428 _70584).
Proof. exact (MK_COMB (@lem5473660) (@lem5473360 _70584)). Qed.
Lemma lem5473662 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term350 _70580 _70581 _70582 _70583 _70584) = (term429 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473661 _70584) (@lem5473659 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473664 (_70583 : int) : (term349 _70583) = (term428 _70583).
Proof. exact (MK_COMB (@lem5473663) (@lem5473312 _70583)). Qed.
Lemma lem5473665 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term351 _70580 _70581 _70582 _70583 _70584) = (term430 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473664 _70583) (@lem5473662 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473667 (_70582 : int) : (term349 _70582) = (term428 _70582).
Proof. exact (MK_COMB (@lem5473666) (@lem5473264 _70582)). Qed.
Lemma lem5473668 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term352 _70580 _70581 _70582 _70583 _70584) = (term431 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473667 _70582) (@lem5473665 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473670 (_70581 : int) : (term349 _70581) = (term428 _70581).
Proof. exact (MK_COMB (@lem5473669) (@lem5473216 _70581)). Qed.
Lemma lem5473671 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term353 _70580 _70581 _70582 _70583 _70584) = (term432 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473670 _70581) (@lem5473668 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5473673 (_70580 : int) : (term349 _70580) = (term428 _70580).
Proof. exact (MK_COMB (@lem5473672) (@lem5473168 _70580)). Qed.
Lemma lem5473674 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term354 _70580 _70581 _70582 _70583 _70584) = (term433 _70580 _70581 _70582 _70583 _70584).
Proof. exact (MK_COMB (@lem5473673 _70580) (@lem5473671 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473681 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : (term355 _70580 _70581 _70582 _70583 _70584) = (term433 _70580 _70581 _70582 _70583 _70584).
Proof. exact (TRANS (@lem5473120 _70580 _70581 _70582 _70583 _70584) (@lem5473674 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5473704 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term425 _70580 _70581 _70582 _70583 _70584) = (term434 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term403 _70582 _70584) (term419 _70580 _70581 _70584) (term422 _70583 _70584)). Qed.
Lemma lem5473717 (_70580 : int) (_70582 : int) (_70581 : int) (_70583 : int) : (term426 _70580 _70582 _70581 _70583) = (term426 _70580 _70582 _70581 _70583).
Proof. exact (eq_refl (term426 _70580 _70582 _70581 _70583)). Qed.
Lemma lem5473718 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term427 _70580 _70581 _70582 _70583 _70584) = (term435 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473717 _70580 _70582 _70581 _70583) (@lem5473704 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473719 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term435 _70582 _70580 _70581 _70583 _70584) = (term436 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term437 _70580 _70581 _70582 _70584) (term417 _70580 _70582 _70581 _70583) (term438 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473726 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term439 _70582 _70580 _70581 _70583 _70584) = (term440 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19367 (term403 _70580 _70581) (term415 _70580 _70582 _70581 _70583) (term438 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473733 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term441 _70583 _70580 _70581 _70582 _70584) = (term442 _70583 _70580 _70581 _70582 _70584).
Proof. exact (@lem19367 (term403 _70580 _70581) (term415 _70580 _70582 _70581 _70583) (term437 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473735 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term443 _70583 _70580 _70581 _70582 _70584) = (term444 _70583 _70580 _70581 _70582 _70584).
Proof. exact (MK_COMB (@lem5473734) (@lem5473733 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473736 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term436 _70582 _70580 _70581 _70583 _70584) = (term445 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473735 _70583 _70580 _70581 _70582 _70584) (@lem5473726 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473737 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term435 _70582 _70580 _70581 _70583 _70584) = (term445 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473719 _70582 _70580 _70581 _70583 _70584) (@lem5473736 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473738 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term427 _70580 _70581 _70582 _70583 _70584) = (term445 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473718 _70582 _70580 _70581 _70583 _70584) (@lem5473737 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473741 (_70584 : int) : (term428 _70584) = (term428 _70584).
Proof. exact (eq_refl (term428 _70584)). Qed.
Lemma lem5473742 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term429 _70580 _70581 _70582 _70583 _70584) = (term446 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473741 _70584) (@lem5473738 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473743 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term446 _70582 _70580 _70581 _70583 _70584) = (term447 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term442 _70583 _70580 _70581 _70582 _70584) (term383 _70584) (term440 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473750 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term448 _70582 _70580 _70581 _70583 _70584) = (term449 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term450 _70580 _70581 _70583 _70584) (term383 _70584) (term451 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473757 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term452 _70583 _70580 _70581 _70582 _70584) = (term453 _70583 _70580 _70581 _70582 _70584).
Proof. exact (@lem19158 (term454 _70580 _70581 _70582 _70584) (term383 _70584) (term455 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473759 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term456 _70583 _70580 _70581 _70582 _70584) = (term457 _70583 _70580 _70581 _70582 _70584).
Proof. exact (MK_COMB (@lem5473758) (@lem5473757 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473760 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term447 _70582 _70580 _70581 _70583 _70584) = (term458 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473759 _70583 _70580 _70581 _70582 _70584) (@lem5473750 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473761 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term446 _70582 _70580 _70581 _70583 _70584) = (term458 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473743 _70582 _70580 _70581 _70583 _70584) (@lem5473760 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473762 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term429 _70580 _70581 _70582 _70583 _70584) = (term458 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473742 _70582 _70580 _70581 _70583 _70584) (@lem5473761 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473765 (_70583 : int) : (term428 _70583) = (term428 _70583).
Proof. exact (eq_refl (term428 _70583)). Qed.
Lemma lem5473766 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term430 _70580 _70581 _70582 _70583 _70584) = (term459 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473765 _70583) (@lem5473762 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473767 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term459 _70582 _70580 _70581 _70583 _70584) = (term460 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term453 _70583 _70580 _70581 _70582 _70584) (term383 _70583) (term449 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473774 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term461 _70582 _70580 _70581 _70583 _70584) = (term462 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term463 _70580 _70581 _70583 _70584) (term383 _70583) (term464 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473781 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term465 _70583 _70580 _70581 _70582 _70584) = (term466 _70583 _70580 _70581 _70582 _70584).
Proof. exact (@lem19158 (term467 _70580 _70581 _70582 _70584) (term383 _70583) (term468 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473783 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term469 _70583 _70580 _70581 _70582 _70584) = (term470 _70583 _70580 _70581 _70582 _70584).
Proof. exact (MK_COMB (@lem5473782) (@lem5473781 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473784 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term460 _70582 _70580 _70581 _70583 _70584) = (term471 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473783 _70583 _70580 _70581 _70582 _70584) (@lem5473774 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473785 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term459 _70582 _70580 _70581 _70583 _70584) = (term471 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473767 _70582 _70580 _70581 _70583 _70584) (@lem5473784 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473786 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term430 _70580 _70581 _70582 _70583 _70584) = (term471 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473766 _70582 _70580 _70581 _70583 _70584) (@lem5473785 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473789 (_70582 : int) : (term428 _70582) = (term428 _70582).
Proof. exact (eq_refl (term428 _70582)). Qed.
Lemma lem5473790 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term431 _70580 _70581 _70582 _70583 _70584) = (term472 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473789 _70582) (@lem5473786 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473791 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term472 _70582 _70580 _70581 _70583 _70584) = (term473 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term466 _70583 _70580 _70581 _70582 _70584) (term383 _70582) (term462 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473798 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term474 _70582 _70580 _70581 _70583 _70584) = (term475 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term476 _70580 _70581 _70583 _70584) (term383 _70582) (term477 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473805 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term478 _70583 _70580 _70581 _70582 _70584) = (term479 _70583 _70580 _70581 _70582 _70584).
Proof. exact (@lem19158 (term480 _70583 _70580 _70581 _70582 _70584) (term383 _70582) (term481 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473807 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term482 _70583 _70580 _70581 _70582 _70584) = (term483 _70583 _70580 _70581 _70582 _70584).
Proof. exact (MK_COMB (@lem5473806) (@lem5473805 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473808 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term473 _70582 _70580 _70581 _70583 _70584) = (term484 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473807 _70583 _70580 _70581 _70582 _70584) (@lem5473798 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473809 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term472 _70582 _70580 _70581 _70583 _70584) = (term484 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473791 _70582 _70580 _70581 _70583 _70584) (@lem5473808 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473810 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term431 _70580 _70581 _70582 _70583 _70584) = (term484 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473790 _70582 _70580 _70581 _70583 _70584) (@lem5473809 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473813 (_70581 : int) : (term428 _70581) = (term428 _70581).
Proof. exact (eq_refl (term428 _70581)). Qed.
Lemma lem5473814 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term432 _70580 _70581 _70582 _70583 _70584) = (term485 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473813 _70581) (@lem5473810 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473815 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term485 _70582 _70580 _70581 _70583 _70584) = (term486 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term479 _70583 _70580 _70581 _70582 _70584) (term383 _70581) (term475 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473822 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term487 _70582 _70580 _70581 _70583 _70584) = (term488 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term489 _70582 _70580 _70581 _70583 _70584) (term383 _70581) (term490 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473829 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term491 _70583 _70580 _70581 _70582 _70584) = (term492 _70583 _70580 _70581 _70582 _70584).
Proof. exact (@lem19158 (term493 _70583 _70580 _70581 _70582 _70584) (term383 _70581) (term494 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473831 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term495 _70583 _70580 _70581 _70582 _70584) = (term496 _70583 _70580 _70581 _70582 _70584).
Proof. exact (MK_COMB (@lem5473830) (@lem5473829 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473832 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term486 _70582 _70580 _70581 _70583 _70584) = (term497 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473831 _70583 _70580 _70581 _70582 _70584) (@lem5473822 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473833 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term485 _70582 _70580 _70581 _70583 _70584) = (term497 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473815 _70582 _70580 _70581 _70583 _70584) (@lem5473832 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473834 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term432 _70580 _70581 _70582 _70583 _70584) = (term497 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473814 _70582 _70580 _70581 _70583 _70584) (@lem5473833 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473837 (_70580 : int) : (term428 _70580) = (term428 _70580).
Proof. exact (eq_refl (term428 _70580)). Qed.
Lemma lem5473838 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term433 _70580 _70581 _70582 _70583 _70584) = (term498 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473837 _70580) (@lem5473834 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473839 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term498 _70582 _70580 _70581 _70583 _70584) = (term499 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term492 _70583 _70580 _70581 _70582 _70584) (term383 _70580) (term488 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473846 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term500 _70582 _70580 _70581 _70583 _70584) = (term501 _70582 _70580 _70581 _70583 _70584).
Proof. exact (@lem19158 (term502 _70582 _70580 _70581 _70583 _70584) (term383 _70580) (term503 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473853 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term504 _70583 _70580 _70581 _70582 _70584) = (term505 _70583 _70580 _70581 _70582 _70584).
Proof. exact (@lem19158 (term506 _70583 _70580 _70581 _70582 _70584) (term383 _70580) (term507 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5473855 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) : (term508 _70583 _70580 _70581 _70582 _70584) = (term509 _70583 _70580 _70581 _70582 _70584).
Proof. exact (MK_COMB (@lem5473854) (@lem5473853 _70583 _70580 _70581 _70582 _70584)). Qed.
Lemma lem5473856 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term499 _70582 _70580 _70581 _70583 _70584) = (term510 _70582 _70580 _70581 _70583 _70584).
Proof. exact (MK_COMB (@lem5473855 _70583 _70580 _70581 _70582 _70584) (@lem5473846 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473857 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term498 _70582 _70580 _70581 _70583 _70584) = (term510 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473839 _70582 _70580 _70581 _70583 _70584) (@lem5473856 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473858 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term433 _70580 _70581 _70582 _70583 _70584) = (term510 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473838 _70582 _70580 _70581 _70583 _70584) (@lem5473857 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473859 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) : (term355 _70580 _70581 _70582 _70583 _70584) = (term510 _70582 _70580 _70581 _70583 _70584).
Proof. exact (TRANS (@lem5473681 _70580 _70581 _70582 _70583 _70584) (@lem5473858 _70582 _70580 _70581 _70583 _70584)). Qed.
Lemma lem5473881 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term510 _70582 _70580 _70581 _70583 _70584) : term510 _70582 _70580 _70581 _70583 _70584.
Proof. exact (h1). Qed.
Lemma lem5473882 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term505 _70583 _70580 _70581 _70582 _70584) : term505 _70583 _70580 _70581 _70582 _70584.
Proof. exact (h1). Qed.
Lemma lem5473883 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term511 _70583 _70580 _70581 _70582 _70584.
Proof. exact (h1). Qed.
Lemma lem5473884 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term506 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5473883 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473886 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term493 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5473884 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473888 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term480 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5473886 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473890 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term467 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5473888 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473892 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term454 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5473890 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473894 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term437 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5473892 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473895 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term403 _70580 _70581.
Proof. exact (proj1 (@lem5473892 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473897 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term419 _70580 _70581 _70584.
Proof. exact (proj1 (@lem5473894 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473898 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term409 _70581 _70584.
Proof. exact (proj2 (@lem5473897 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473899 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term413 _70580 _70584.
Proof. exact (proj1 (@lem5473897 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473901 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5473902 : term512 = term513.
Proof. exact (@lem5473901 term318 term331). Qed.
Lemma lem5473904 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473905 : term331 = term389.
Proof. exact (@lem5473904 term332). Qed.
Lemma lem5473907 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473908 : term318 = term360.
Proof. exact (@lem5473907 (NUMERAL 0)). Qed.
Lemma lem5473909 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5473910 : term514 = term515.
Proof. exact (MK_COMB (@lem5473909) (@lem5473908)). Qed.
Lemma lem5473911 : term513 = term516.
Proof. exact (MK_COMB (@lem5473910) (@lem5473905)). Qed.
Lemma lem5473912 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5473914 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5473915 : term513 = term519.
Proof. exact (@lem5473914 (NUMERAL 0) term332). Qed.
Lemma lem5473916 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5473917 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5473918 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5473917 h1) (fun h1 : term519 = True => @lem5473916)). Qed.
Lemma lem5473919 : term519 = True.
Proof. exact (EQ_MP (@lem5473918) (@lem5473916)). Qed.
Lemma lem5473920 : term513 = True.
Proof. exact (TRANS (@lem5473915) (@lem5473919)). Qed.
Lemma lem5473921 : True = term513.
Proof. exact (SYM (@lem5473920)). Qed.
Lemma lem5473922 : term513.
Proof. exact (EQ_MP (@lem5473921) (@lem0)). Qed.
Lemma lem5473923 : term521.
Proof. exact (@lem5473912 (@lem5473922)). Qed.
Lemma lem5473925 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5473926 : term513 = term519.
Proof. exact (@lem5473925 (NUMERAL 0) term332). Qed.
Lemma lem5473927 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5473928 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5473929 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5473928 h1) (fun h1 : term519 = True => @lem5473927)). Qed.
Lemma lem5473930 : term519 = True.
Proof. exact (EQ_MP (@lem5473929) (@lem5473927)). Qed.
Lemma lem5473931 : term513 = True.
Proof. exact (TRANS (@lem5473926) (@lem5473930)). Qed.
Lemma lem5473932 : True = term513.
Proof. exact (SYM (@lem5473931)). Qed.
Lemma lem5473933 : term513.
Proof. exact (EQ_MP (@lem5473932) (@lem0)). Qed.
Lemma lem5473934 : term516 = term522.
Proof. exact (@lem5473923 (@lem5473933)). Qed.
Lemma lem5473936 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5473937 : term372 = term373.
Proof. exact (@lem5473936 term332 term332). Qed.
Lemma lem5473938 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5473939 : term375 = term332.
Proof. exact (EQ_MP (@lem5473938) (@lem940073)). Qed.
Lemma lem5473940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5473941 : term373 = term331.
Proof. exact (MK_COMB (@lem5473940) (@lem5473939)). Qed.
Lemma lem5473942 : term372 = term331.
Proof. exact (TRANS (@lem5473937) (@lem5473941)). Qed.
Lemma lem5473944 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5473945 : term524 = term318.
Proof. exact (@lem5473944 term332). Qed.
Lemma lem5473946 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5473947 : term525 = term514.
Proof. exact (MK_COMB (@lem5473946) (@lem5473945)). Qed.
Lemma lem5473948 : term522 = term513.
Proof. exact (MK_COMB (@lem5473947) (@lem5473942)). Qed.
Lemma lem5473950 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5473951 : term513 = term519.
Proof. exact (@lem5473950 (NUMERAL 0) term332). Qed.
Lemma lem5473952 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5473953 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5473954 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5473953 h1) (fun h1 : term519 = True => @lem5473952)). Qed.
Lemma lem5473955 : term519 = True.
Proof. exact (EQ_MP (@lem5473954) (@lem5473952)). Qed.
Lemma lem5473956 : term513 = True.
Proof. exact (TRANS (@lem5473951) (@lem5473955)). Qed.
Lemma lem5473957 : term522 = True.
Proof. exact (TRANS (@lem5473948) (@lem5473956)). Qed.
Lemma lem5473958 : term516 = True.
Proof. exact (TRANS (@lem5473934) (@lem5473957)). Qed.
Lemma lem5473959 : term513 = True.
Proof. exact (TRANS (@lem5473911) (@lem5473958)). Qed.
Lemma lem5473960 : term512 = True.
Proof. exact (TRANS (@lem5473902) (@lem5473959)). Qed.
Lemma lem5473961 : True = term512.
Proof. exact (SYM (@lem5473960)). Qed.
Lemma lem5473962 : term512.
Proof. exact (EQ_MP (@lem5473961) (@lem0)). Qed.
Lemma lem5473963 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term526 _70581 _70584.
Proof. exact (conj (@lem5473962) (@lem5473898 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473965 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5473966 (_70581 : int) (_70584 : int) : term528 _70581 _70584.
Proof. exact (@lem5473965 term331 (term406 _70581 _70584)). Qed.
Lemma lem5473967 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term529 _70581 _70584.
Proof. exact (@lem5473966 _70581 _70584 (@lem5473963 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473968 (_70581 : int) (_70584 : int) : (term530 _70581 _70584) = (term406 _70581 _70584).
Proof. exact (@lem1982733 (term406 _70581 _70584)). Qed.
Lemma lem5473969 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5473970 (_70581 : int) (_70584 : int) : (term531 _70581 _70584) = (term408 _70581 _70584).
Proof. exact (MK_COMB (@lem5473969) (@lem5473968 _70581 _70584)). Qed.
Lemma lem5473971 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5473972 (_70581 : int) (_70584 : int) : (term529 _70581 _70584) = (term409 _70581 _70584).
Proof. exact (MK_COMB (@lem5473970 _70581 _70584) (@lem5473971)). Qed.
Lemma lem5473973 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term409 _70581 _70584.
Proof. exact (EQ_MP (@lem5473972 _70581 _70584) (@lem5473967 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5473975 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5473976 : term512 = term513.
Proof. exact (@lem5473975 term318 term331). Qed.
Lemma lem5473978 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473979 : term331 = term389.
Proof. exact (@lem5473978 term332). Qed.
Lemma lem5473981 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5473982 : term318 = term360.
Proof. exact (@lem5473981 (NUMERAL 0)). Qed.
Lemma lem5473983 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5473984 : term514 = term515.
Proof. exact (MK_COMB (@lem5473983) (@lem5473982)). Qed.
Lemma lem5473985 : term513 = term516.
Proof. exact (MK_COMB (@lem5473984) (@lem5473979)). Qed.
Lemma lem5473986 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5473988 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5473989 : term513 = term519.
Proof. exact (@lem5473988 (NUMERAL 0) term332). Qed.
Lemma lem5473990 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5473991 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5473992 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5473991 h1) (fun h1 : term519 = True => @lem5473990)). Qed.
Lemma lem5473993 : term519 = True.
Proof. exact (EQ_MP (@lem5473992) (@lem5473990)). Qed.
Lemma lem5473994 : term513 = True.
Proof. exact (TRANS (@lem5473989) (@lem5473993)). Qed.
Lemma lem5473995 : True = term513.
Proof. exact (SYM (@lem5473994)). Qed.
Lemma lem5473996 : term513.
Proof. exact (EQ_MP (@lem5473995) (@lem0)). Qed.
Lemma lem5473997 : term521.
Proof. exact (@lem5473986 (@lem5473996)). Qed.
Lemma lem5473999 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474000 : term513 = term519.
Proof. exact (@lem5473999 (NUMERAL 0) term332). Qed.
Lemma lem5474001 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474002 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474003 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474002 h1) (fun h1 : term519 = True => @lem5474001)). Qed.
Lemma lem5474004 : term519 = True.
Proof. exact (EQ_MP (@lem5474003) (@lem5474001)). Qed.
Lemma lem5474005 : term513 = True.
Proof. exact (TRANS (@lem5474000) (@lem5474004)). Qed.
Lemma lem5474006 : True = term513.
Proof. exact (SYM (@lem5474005)). Qed.
Lemma lem5474007 : term513.
Proof. exact (EQ_MP (@lem5474006) (@lem0)). Qed.
Lemma lem5474008 : term516 = term522.
Proof. exact (@lem5473997 (@lem5474007)). Qed.
Lemma lem5474010 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474011 : term372 = term373.
Proof. exact (@lem5474010 term332 term332). Qed.
Lemma lem5474012 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474013 : term375 = term332.
Proof. exact (EQ_MP (@lem5474012) (@lem940073)). Qed.
Lemma lem5474014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474015 : term373 = term331.
Proof. exact (MK_COMB (@lem5474014) (@lem5474013)). Qed.
Lemma lem5474016 : term372 = term331.
Proof. exact (TRANS (@lem5474011) (@lem5474015)). Qed.
Lemma lem5474018 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474019 : term524 = term318.
Proof. exact (@lem5474018 term332). Qed.
Lemma lem5474020 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474021 : term525 = term514.
Proof. exact (MK_COMB (@lem5474020) (@lem5474019)). Qed.
Lemma lem5474022 : term522 = term513.
Proof. exact (MK_COMB (@lem5474021) (@lem5474016)). Qed.
Lemma lem5474024 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474025 : term513 = term519.
Proof. exact (@lem5474024 (NUMERAL 0) term332). Qed.
Lemma lem5474026 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474027 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474028 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474027 h1) (fun h1 : term519 = True => @lem5474026)). Qed.
Lemma lem5474029 : term519 = True.
Proof. exact (EQ_MP (@lem5474028) (@lem5474026)). Qed.
Lemma lem5474030 : term513 = True.
Proof. exact (TRANS (@lem5474025) (@lem5474029)). Qed.
Lemma lem5474031 : term522 = True.
Proof. exact (TRANS (@lem5474022) (@lem5474030)). Qed.
Lemma lem5474032 : term516 = True.
Proof. exact (TRANS (@lem5474008) (@lem5474031)). Qed.
Lemma lem5474033 : term513 = True.
Proof. exact (TRANS (@lem5473985) (@lem5474032)). Qed.
Lemma lem5474034 : term512 = True.
Proof. exact (TRANS (@lem5473976) (@lem5474033)). Qed.
Lemma lem5474035 : True = term512.
Proof. exact (SYM (@lem5474034)). Qed.
Lemma lem5474036 : term512.
Proof. exact (EQ_MP (@lem5474035) (@lem0)). Qed.
Lemma lem5474037 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term532 _70580 _70581.
Proof. exact (conj (@lem5474036) (@lem5473895 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474039 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5474040 (_70580 : int) (_70581 : int) : term533 _70580 _70581.
Proof. exact (@lem5474039 term331 (term400 _70580 _70581)). Qed.
Lemma lem5474041 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term534 _70580 _70581.
Proof. exact (@lem5474040 _70580 _70581 (@lem5474037 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474042 (_70580 : int) (_70581 : int) : (term535 _70580 _70581) = (term400 _70580 _70581).
Proof. exact (@lem1982733 (term400 _70580 _70581)). Qed.
Lemma lem5474043 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474044 (_70580 : int) (_70581 : int) : (term536 _70580 _70581) = (term402 _70580 _70581).
Proof. exact (MK_COMB (@lem5474043) (@lem5474042 _70580 _70581)). Qed.
Lemma lem5474045 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474046 (_70580 : int) (_70581 : int) : (term534 _70580 _70581) = (term403 _70580 _70581).
Proof. exact (MK_COMB (@lem5474044 _70580 _70581) (@lem5474045)). Qed.
Lemma lem5474047 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term403 _70580 _70581.
Proof. exact (EQ_MP (@lem5474046 _70580 _70581) (@lem5474041 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474049 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5474050 : term512 = term513.
Proof. exact (@lem5474049 term318 term331). Qed.
Lemma lem5474052 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474053 : term331 = term389.
Proof. exact (@lem5474052 term332). Qed.
Lemma lem5474055 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474056 : term318 = term360.
Proof. exact (@lem5474055 (NUMERAL 0)). Qed.
Lemma lem5474057 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474058 : term514 = term515.
Proof. exact (MK_COMB (@lem5474057) (@lem5474056)). Qed.
Lemma lem5474059 : term513 = term516.
Proof. exact (MK_COMB (@lem5474058) (@lem5474053)). Qed.
Lemma lem5474060 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5474062 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474063 : term513 = term519.
Proof. exact (@lem5474062 (NUMERAL 0) term332). Qed.
Lemma lem5474064 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474065 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474066 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474065 h1) (fun h1 : term519 = True => @lem5474064)). Qed.
Lemma lem5474067 : term519 = True.
Proof. exact (EQ_MP (@lem5474066) (@lem5474064)). Qed.
Lemma lem5474068 : term513 = True.
Proof. exact (TRANS (@lem5474063) (@lem5474067)). Qed.
Lemma lem5474069 : True = term513.
Proof. exact (SYM (@lem5474068)). Qed.
Lemma lem5474070 : term513.
Proof. exact (EQ_MP (@lem5474069) (@lem0)). Qed.
Lemma lem5474071 : term521.
Proof. exact (@lem5474060 (@lem5474070)). Qed.
Lemma lem5474073 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474074 : term513 = term519.
Proof. exact (@lem5474073 (NUMERAL 0) term332). Qed.
Lemma lem5474075 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474076 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474077 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474076 h1) (fun h1 : term519 = True => @lem5474075)). Qed.
Lemma lem5474078 : term519 = True.
Proof. exact (EQ_MP (@lem5474077) (@lem5474075)). Qed.
Lemma lem5474079 : term513 = True.
Proof. exact (TRANS (@lem5474074) (@lem5474078)). Qed.
Lemma lem5474080 : True = term513.
Proof. exact (SYM (@lem5474079)). Qed.
Lemma lem5474081 : term513.
Proof. exact (EQ_MP (@lem5474080) (@lem0)). Qed.
Lemma lem5474082 : term516 = term522.
Proof. exact (@lem5474071 (@lem5474081)). Qed.
Lemma lem5474084 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474085 : term372 = term373.
Proof. exact (@lem5474084 term332 term332). Qed.
Lemma lem5474086 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474087 : term375 = term332.
Proof. exact (EQ_MP (@lem5474086) (@lem940073)). Qed.
Lemma lem5474088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474089 : term373 = term331.
Proof. exact (MK_COMB (@lem5474088) (@lem5474087)). Qed.
Lemma lem5474090 : term372 = term331.
Proof. exact (TRANS (@lem5474085) (@lem5474089)). Qed.
Lemma lem5474092 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474093 : term524 = term318.
Proof. exact (@lem5474092 term332). Qed.
Lemma lem5474094 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474095 : term525 = term514.
Proof. exact (MK_COMB (@lem5474094) (@lem5474093)). Qed.
Lemma lem5474096 : term522 = term513.
Proof. exact (MK_COMB (@lem5474095) (@lem5474090)). Qed.
Lemma lem5474098 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474099 : term513 = term519.
Proof. exact (@lem5474098 (NUMERAL 0) term332). Qed.
Lemma lem5474100 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474101 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474102 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474101 h1) (fun h1 : term519 = True => @lem5474100)). Qed.
Lemma lem5474103 : term519 = True.
Proof. exact (EQ_MP (@lem5474102) (@lem5474100)). Qed.
Lemma lem5474104 : term513 = True.
Proof. exact (TRANS (@lem5474099) (@lem5474103)). Qed.
Lemma lem5474105 : term522 = True.
Proof. exact (TRANS (@lem5474096) (@lem5474104)). Qed.
Lemma lem5474106 : term516 = True.
Proof. exact (TRANS (@lem5474082) (@lem5474105)). Qed.
Lemma lem5474107 : term513 = True.
Proof. exact (TRANS (@lem5474059) (@lem5474106)). Qed.
Lemma lem5474108 : term512 = True.
Proof. exact (TRANS (@lem5474050) (@lem5474107)). Qed.
Lemma lem5474109 : True = term512.
Proof. exact (SYM (@lem5474108)). Qed.
Lemma lem5474110 : term512.
Proof. exact (EQ_MP (@lem5474109) (@lem0)). Qed.
Lemma lem5474111 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term537 _70580 _70584.
Proof. exact (conj (@lem5474110) (@lem5473899 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474113 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5474114 (_70580 : int) (_70584 : int) : term538 _70580 _70584.
Proof. exact (@lem5474113 term331 (term410 _70580 _70584)). Qed.
Lemma lem5474115 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term539 _70580 _70584.
Proof. exact (@lem5474114 _70580 _70584 (@lem5474111 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474116 (_70580 : int) (_70584 : int) : (term540 _70580 _70584) = (term410 _70580 _70584).
Proof. exact (@lem1982733 (term410 _70580 _70584)). Qed.
Lemma lem5474117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474118 (_70580 : int) (_70584 : int) : (term541 _70580 _70584) = (term412 _70580 _70584).
Proof. exact (MK_COMB (@lem5474117) (@lem5474116 _70580 _70584)). Qed.
Lemma lem5474119 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474120 (_70580 : int) (_70584 : int) : (term539 _70580 _70584) = (term413 _70580 _70584).
Proof. exact (MK_COMB (@lem5474118 _70580 _70584) (@lem5474119)). Qed.
Lemma lem5474121 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term413 _70580 _70584.
Proof. exact (EQ_MP (@lem5474120 _70580 _70584) (@lem5474115 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474122 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term542 _70584 _70580 _70581.
Proof. exact (conj (@lem5474121 _70583 _70580 _70581 _70582 _70584 h1) (@lem5474047 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474124 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5474125 (_70584 : int) (_70580 : int) (_70581 : int) : term544 _70584 _70580 _70581.
Proof. exact (@lem5474124 (term410 _70580 _70584) (term400 _70580 _70581)). Qed.
Lemma lem5474126 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term545 _70584 _70580 _70581.
Proof. exact (@lem5474125 _70584 _70580 _70581 (@lem5474122 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474127 (_70580 : int) (_70584 : int) (_70581 : int) : (term546 _70584 _70580 _70581) = (term547 _70580 _70584 _70581).
Proof. exact (@lem1982753 (term411 _70580) (real_of_int _70580) (real_of_int _70584) (term399 _70581)). Qed.
Lemma lem5474128 (_70580 : int) : (term548 _70580) = (term549 _70580).
Proof. exact (@lem1982713 term363 (real_of_int _70580)). Qed.
Lemma lem5474130 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474131 : term331 = term389.
Proof. exact (@lem5474130 term332). Qed.
Lemma lem5474133 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5474134 : term363 = term364.
Proof. exact (@lem5474133 term332). Qed.
Lemma lem5474135 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474136 : term550 = term551.
Proof. exact (MK_COMB (@lem5474135) (@lem5474134)). Qed.
Lemma lem5474137 : term552 = term553.
Proof. exact (MK_COMB (@lem5474136) (@lem5474131)). Qed.
Lemma lem5474138 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5474140 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474141 : term513 = term519.
Proof. exact (@lem5474140 (NUMERAL 0) term332). Qed.
Lemma lem5474142 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474143 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474144 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474143 h1) (fun h1 : term519 = True => @lem5474142)). Qed.
Lemma lem5474145 : term519 = True.
Proof. exact (EQ_MP (@lem5474144) (@lem5474142)). Qed.
Lemma lem5474146 : term513 = True.
Proof. exact (TRANS (@lem5474141) (@lem5474145)). Qed.
Lemma lem5474147 : True = term513.
Proof. exact (SYM (@lem5474146)). Qed.
Lemma lem5474148 : term513.
Proof. exact (EQ_MP (@lem5474147) (@lem0)). Qed.
Lemma lem5474149 : term555.
Proof. exact (@lem5474138 (@lem5474148)). Qed.
Lemma lem5474151 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474152 : term513 = term519.
Proof. exact (@lem5474151 (NUMERAL 0) term332). Qed.
Lemma lem5474153 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474154 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474155 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474154 h1) (fun h1 : term519 = True => @lem5474153)). Qed.
Lemma lem5474156 : term519 = True.
Proof. exact (EQ_MP (@lem5474155) (@lem5474153)). Qed.
Lemma lem5474157 : term513 = True.
Proof. exact (TRANS (@lem5474152) (@lem5474156)). Qed.
Lemma lem5474158 : True = term513.
Proof. exact (SYM (@lem5474157)). Qed.
Lemma lem5474159 : term513.
Proof. exact (EQ_MP (@lem5474158) (@lem0)). Qed.
Lemma lem5474160 : term556.
Proof. exact (@lem5474149 (@lem5474159)). Qed.
Lemma lem5474162 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474163 : term513 = term519.
Proof. exact (@lem5474162 (NUMERAL 0) term332). Qed.
Lemma lem5474164 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474165 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474166 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474165 h1) (fun h1 : term519 = True => @lem5474164)). Qed.
Lemma lem5474167 : term519 = True.
Proof. exact (EQ_MP (@lem5474166) (@lem5474164)). Qed.
Lemma lem5474168 : term513 = True.
Proof. exact (TRANS (@lem5474163) (@lem5474167)). Qed.
Lemma lem5474169 : True = term513.
Proof. exact (SYM (@lem5474168)). Qed.
Lemma lem5474170 : term513.
Proof. exact (EQ_MP (@lem5474169) (@lem0)). Qed.
Lemma lem5474171 : term557.
Proof. exact (@lem5474160 (@lem5474170)). Qed.
Lemma lem5474173 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474174 : term372 = term373.
Proof. exact (@lem5474173 term332 term332). Qed.
Lemma lem5474175 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474176 : term375 = term332.
Proof. exact (EQ_MP (@lem5474175) (@lem940073)). Qed.
Lemma lem5474177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474178 : term373 = term331.
Proof. exact (MK_COMB (@lem5474177) (@lem5474176)). Qed.
Lemma lem5474179 : term372 = term331.
Proof. exact (TRANS (@lem5474174) (@lem5474178)). Qed.
Lemma lem5474181 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5474182 : term390 = term395.
Proof. exact (@lem5474181 term332 term332). Qed.
Lemma lem5474183 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474184 : term375 = term332.
Proof. exact (EQ_MP (@lem5474183) (@lem940073)). Qed.
Lemma lem5474185 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474186 : term373 = term331.
Proof. exact (MK_COMB (@lem5474185) (@lem5474184)). Qed.
Lemma lem5474187 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5474188 : term395 = term363.
Proof. exact (MK_COMB (@lem5474187) (@lem5474186)). Qed.
Lemma lem5474189 : term390 = term363.
Proof. exact (TRANS (@lem5474182) (@lem5474188)). Qed.
Lemma lem5474190 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474191 : term558 = term550.
Proof. exact (MK_COMB (@lem5474190) (@lem5474189)). Qed.
Lemma lem5474192 : term559 = term552.
Proof. exact (MK_COMB (@lem5474191) (@lem5474179)). Qed.
Lemma lem5474194 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5474195 : term552 = term318.
Proof. exact (@lem5474194 term332). Qed.
Lemma lem5474196 : term559 = term318.
Proof. exact (TRANS (@lem5474192) (@lem5474195)). Qed.
Lemma lem5474197 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474198 : term561 = term562.
Proof. exact (MK_COMB (@lem5474197) (@lem5474196)). Qed.
Lemma lem5474199 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5474200 : term563 = term524.
Proof. exact (MK_COMB (@lem5474198) (@lem5474199)). Qed.
Lemma lem5474202 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474203 : term524 = term318.
Proof. exact (@lem5474202 term332). Qed.
Lemma lem5474204 : term563 = term318.
Proof. exact (TRANS (@lem5474200) (@lem5474203)). Qed.
Lemma lem5474206 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474207 : term372 = term373.
Proof. exact (@lem5474206 term332 term332). Qed.
Lemma lem5474208 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474209 : term375 = term332.
Proof. exact (EQ_MP (@lem5474208) (@lem940073)). Qed.
Lemma lem5474210 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474211 : term373 = term331.
Proof. exact (MK_COMB (@lem5474210) (@lem5474209)). Qed.
Lemma lem5474212 : term372 = term331.
Proof. exact (TRANS (@lem5474207) (@lem5474211)). Qed.
Lemma lem5474213 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5474214 : term564 = term524.
Proof. exact (MK_COMB (@lem5474213) (@lem5474212)). Qed.
Lemma lem5474216 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474217 : term524 = term318.
Proof. exact (@lem5474216 term332). Qed.
Lemma lem5474218 : term564 = term318.
Proof. exact (TRANS (@lem5474214) (@lem5474217)). Qed.
Lemma lem5474219 : term318 = term564.
Proof. exact (SYM (@lem5474218)). Qed.
Lemma lem5474220 : term563 = term564.
Proof. exact (TRANS (@lem5474204) (@lem5474219)). Qed.
Lemma lem5474221 : term553 = term360.
Proof. exact (@lem5474171 (@lem5474220)). Qed.
Lemma lem5474222 : term552 = term360.
Proof. exact (TRANS (@lem5474137) (@lem5474221)). Qed.
Lemma lem5474224 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5474225 : term360 = term318.
Proof. exact (@lem5474224 term318). Qed.
Lemma lem5474226 : term552 = term318.
Proof. exact (TRANS (@lem5474222) (@lem5474225)). Qed.
Lemma lem5474227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474228 : term565 = term562.
Proof. exact (MK_COMB (@lem5474227) (@lem5474226)). Qed.
Lemma lem5474229 (_70580 : int) : (real_of_int _70580) = (real_of_int _70580).
Proof. exact (eq_refl (real_of_int _70580)). Qed.
Lemma lem5474230 (_70580 : int) : (term549 _70580) = (term566 _70580).
Proof. exact (MK_COMB (@lem5474228) (@lem5474229 _70580)). Qed.
Lemma lem5474231 (_70580 : int) : (term548 _70580) = (term566 _70580).
Proof. exact (TRANS (@lem5474128 _70580) (@lem5474230 _70580)). Qed.
Lemma lem5474232 (_70580 : int) : (term566 _70580) = term318.
Proof. exact (@lem1982719 (real_of_int _70580)). Qed.
Lemma lem5474233 (_70580 : int) : (term548 _70580) = term318.
Proof. exact (TRANS (@lem5474231 _70580) (@lem5474232 _70580)). Qed.
Lemma lem5474234 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474235 (_70580 : int) : (term567 _70580) = term568.
Proof. exact (MK_COMB (@lem5474234) (@lem5474233 _70580)). Qed.
Lemma lem5474240 (_70581 : int) (_70584 : int) : (term400 _70584 _70581) = (term420 _70581 _70584).
Proof. exact (@lem1982757 (term411 _70581) (real_of_int _70584) term363). Qed.
Lemma lem5474241 (_70580 : int) (_70581 : int) (_70584 : int) : (term547 _70580 _70584 _70581) = (term569 _70581 _70584).
Proof. exact (MK_COMB (@lem5474235 _70580) (@lem5474240 _70581 _70584)). Qed.
Lemma lem5474242 (_70580 : int) (_70581 : int) (_70584 : int) : (term546 _70584 _70580 _70581) = (term569 _70581 _70584).
Proof. exact (TRANS (@lem5474127 _70580 _70584 _70581) (@lem5474241 _70580 _70581 _70584)). Qed.
Lemma lem5474243 (_70581 : int) (_70584 : int) : (term569 _70581 _70584) = (term420 _70581 _70584).
Proof. exact (@lem1982721 (term420 _70581 _70584)). Qed.
Lemma lem5474244 (_70580 : int) (_70581 : int) (_70584 : int) : (term546 _70584 _70580 _70581) = (term420 _70581 _70584).
Proof. exact (TRANS (@lem5474242 _70580 _70581 _70584) (@lem5474243 _70581 _70584)). Qed.
Lemma lem5474245 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474246 (_70580 : int) (_70581 : int) (_70584 : int) : (term570 _70584 _70580 _70581) = (term421 _70581 _70584).
Proof. exact (MK_COMB (@lem5474245) (@lem5474244 _70580 _70581 _70584)). Qed.
Lemma lem5474247 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474248 (_70580 : int) (_70581 : int) (_70584 : int) : (term545 _70584 _70580 _70581) = (term422 _70581 _70584).
Proof. exact (MK_COMB (@lem5474246 _70580 _70581 _70584) (@lem5474247)). Qed.
Lemma lem5474249 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term422 _70581 _70584.
Proof. exact (EQ_MP (@lem5474248 _70580 _70581 _70584) (@lem5474126 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474251 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5474252 : term512 = term513.
Proof. exact (@lem5474251 term318 term331). Qed.
Lemma lem5474254 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474255 : term331 = term389.
Proof. exact (@lem5474254 term332). Qed.
Lemma lem5474257 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474258 : term318 = term360.
Proof. exact (@lem5474257 (NUMERAL 0)). Qed.
Lemma lem5474259 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474260 : term514 = term515.
Proof. exact (MK_COMB (@lem5474259) (@lem5474258)). Qed.
Lemma lem5474261 : term513 = term516.
Proof. exact (MK_COMB (@lem5474260) (@lem5474255)). Qed.
Lemma lem5474262 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5474264 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474265 : term513 = term519.
Proof. exact (@lem5474264 (NUMERAL 0) term332). Qed.
Lemma lem5474266 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474267 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474268 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474267 h1) (fun h1 : term519 = True => @lem5474266)). Qed.
Lemma lem5474269 : term519 = True.
Proof. exact (EQ_MP (@lem5474268) (@lem5474266)). Qed.
Lemma lem5474270 : term513 = True.
Proof. exact (TRANS (@lem5474265) (@lem5474269)). Qed.
Lemma lem5474271 : True = term513.
Proof. exact (SYM (@lem5474270)). Qed.
Lemma lem5474272 : term513.
Proof. exact (EQ_MP (@lem5474271) (@lem0)). Qed.
Lemma lem5474273 : term521.
Proof. exact (@lem5474262 (@lem5474272)). Qed.
Lemma lem5474275 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474276 : term513 = term519.
Proof. exact (@lem5474275 (NUMERAL 0) term332). Qed.
Lemma lem5474277 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474278 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474279 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474278 h1) (fun h1 : term519 = True => @lem5474277)). Qed.
Lemma lem5474280 : term519 = True.
Proof. exact (EQ_MP (@lem5474279) (@lem5474277)). Qed.
Lemma lem5474281 : term513 = True.
Proof. exact (TRANS (@lem5474276) (@lem5474280)). Qed.
Lemma lem5474282 : True = term513.
Proof. exact (SYM (@lem5474281)). Qed.
Lemma lem5474283 : term513.
Proof. exact (EQ_MP (@lem5474282) (@lem0)). Qed.
Lemma lem5474284 : term516 = term522.
Proof. exact (@lem5474273 (@lem5474283)). Qed.
Lemma lem5474286 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474287 : term372 = term373.
Proof. exact (@lem5474286 term332 term332). Qed.
Lemma lem5474288 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474289 : term375 = term332.
Proof. exact (EQ_MP (@lem5474288) (@lem940073)). Qed.
Lemma lem5474290 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474291 : term373 = term331.
Proof. exact (MK_COMB (@lem5474290) (@lem5474289)). Qed.
Lemma lem5474292 : term372 = term331.
Proof. exact (TRANS (@lem5474287) (@lem5474291)). Qed.
Lemma lem5474294 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474295 : term524 = term318.
Proof. exact (@lem5474294 term332). Qed.
Lemma lem5474296 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474297 : term525 = term514.
Proof. exact (MK_COMB (@lem5474296) (@lem5474295)). Qed.
Lemma lem5474298 : term522 = term513.
Proof. exact (MK_COMB (@lem5474297) (@lem5474292)). Qed.
Lemma lem5474300 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474301 : term513 = term519.
Proof. exact (@lem5474300 (NUMERAL 0) term332). Qed.
Lemma lem5474302 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474303 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474304 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474303 h1) (fun h1 : term519 = True => @lem5474302)). Qed.
Lemma lem5474305 : term519 = True.
Proof. exact (EQ_MP (@lem5474304) (@lem5474302)). Qed.
Lemma lem5474306 : term513 = True.
Proof. exact (TRANS (@lem5474301) (@lem5474305)). Qed.
Lemma lem5474307 : term522 = True.
Proof. exact (TRANS (@lem5474298) (@lem5474306)). Qed.
Lemma lem5474308 : term516 = True.
Proof. exact (TRANS (@lem5474284) (@lem5474307)). Qed.
Lemma lem5474309 : term513 = True.
Proof. exact (TRANS (@lem5474261) (@lem5474308)). Qed.
Lemma lem5474310 : term512 = True.
Proof. exact (TRANS (@lem5474252) (@lem5474309)). Qed.
Lemma lem5474311 : True = term512.
Proof. exact (SYM (@lem5474310)). Qed.
Lemma lem5474312 : term512.
Proof. exact (EQ_MP (@lem5474311) (@lem0)). Qed.
Lemma lem5474313 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term571 _70581 _70584.
Proof. exact (conj (@lem5474312) (@lem5474249 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474315 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5474316 (_70581 : int) (_70584 : int) : term572 _70581 _70584.
Proof. exact (@lem5474315 term331 (term420 _70581 _70584)). Qed.
Lemma lem5474317 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term573 _70581 _70584.
Proof. exact (@lem5474316 _70581 _70584 (@lem5474313 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474318 (_70581 : int) (_70584 : int) : (term574 _70581 _70584) = (term420 _70581 _70584).
Proof. exact (@lem1982733 (term420 _70581 _70584)). Qed.
Lemma lem5474319 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474320 (_70581 : int) (_70584 : int) : (term575 _70581 _70584) = (term421 _70581 _70584).
Proof. exact (MK_COMB (@lem5474319) (@lem5474318 _70581 _70584)). Qed.
Lemma lem5474321 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474322 (_70581 : int) (_70584 : int) : (term573 _70581 _70584) = (term422 _70581 _70584).
Proof. exact (MK_COMB (@lem5474320 _70581 _70584) (@lem5474321)). Qed.
Lemma lem5474323 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term422 _70581 _70584.
Proof. exact (EQ_MP (@lem5474322 _70581 _70584) (@lem5474317 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474324 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term576 _70581 _70584.
Proof. exact (conj (@lem5474323 _70583 _70580 _70581 _70582 _70584 h1) (@lem5473973 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474326 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5474327 (_70581 : int) (_70584 : int) : term577 _70581 _70584.
Proof. exact (@lem5474326 (term420 _70581 _70584) (term406 _70581 _70584)). Qed.
Lemma lem5474328 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term578 _70581 _70584.
Proof. exact (@lem5474327 _70581 _70584 (@lem5474324 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474329 (_70581 : int) (_70584 : int) : (term579 _70581 _70584) = (term580 _70581 _70584).
Proof. exact (@lem1982753 (term411 _70581) (real_of_int _70581) (term581 _70584) (term411 _70584)). Qed.
Lemma lem5474330 (_70581 : int) : (term548 _70581) = (term549 _70581).
Proof. exact (@lem1982713 term363 (real_of_int _70581)). Qed.
Lemma lem5474332 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474333 : term331 = term389.
Proof. exact (@lem5474332 term332). Qed.
Lemma lem5474335 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5474336 : term363 = term364.
Proof. exact (@lem5474335 term332). Qed.
Lemma lem5474337 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474338 : term550 = term551.
Proof. exact (MK_COMB (@lem5474337) (@lem5474336)). Qed.
Lemma lem5474339 : term552 = term553.
Proof. exact (MK_COMB (@lem5474338) (@lem5474333)). Qed.
Lemma lem5474340 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5474342 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474343 : term513 = term519.
Proof. exact (@lem5474342 (NUMERAL 0) term332). Qed.
Lemma lem5474344 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474345 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474346 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474345 h1) (fun h1 : term519 = True => @lem5474344)). Qed.
Lemma lem5474347 : term519 = True.
Proof. exact (EQ_MP (@lem5474346) (@lem5474344)). Qed.
Lemma lem5474348 : term513 = True.
Proof. exact (TRANS (@lem5474343) (@lem5474347)). Qed.
Lemma lem5474349 : True = term513.
Proof. exact (SYM (@lem5474348)). Qed.
Lemma lem5474350 : term513.
Proof. exact (EQ_MP (@lem5474349) (@lem0)). Qed.
Lemma lem5474351 : term555.
Proof. exact (@lem5474340 (@lem5474350)). Qed.
Lemma lem5474353 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474354 : term513 = term519.
Proof. exact (@lem5474353 (NUMERAL 0) term332). Qed.
Lemma lem5474355 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474356 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474357 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474356 h1) (fun h1 : term519 = True => @lem5474355)). Qed.
Lemma lem5474358 : term519 = True.
Proof. exact (EQ_MP (@lem5474357) (@lem5474355)). Qed.
Lemma lem5474359 : term513 = True.
Proof. exact (TRANS (@lem5474354) (@lem5474358)). Qed.
Lemma lem5474360 : True = term513.
Proof. exact (SYM (@lem5474359)). Qed.
Lemma lem5474361 : term513.
Proof. exact (EQ_MP (@lem5474360) (@lem0)). Qed.
Lemma lem5474362 : term556.
Proof. exact (@lem5474351 (@lem5474361)). Qed.
Lemma lem5474364 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474365 : term513 = term519.
Proof. exact (@lem5474364 (NUMERAL 0) term332). Qed.
Lemma lem5474366 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474367 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474368 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474367 h1) (fun h1 : term519 = True => @lem5474366)). Qed.
Lemma lem5474369 : term519 = True.
Proof. exact (EQ_MP (@lem5474368) (@lem5474366)). Qed.
Lemma lem5474370 : term513 = True.
Proof. exact (TRANS (@lem5474365) (@lem5474369)). Qed.
Lemma lem5474371 : True = term513.
Proof. exact (SYM (@lem5474370)). Qed.
Lemma lem5474372 : term513.
Proof. exact (EQ_MP (@lem5474371) (@lem0)). Qed.
Lemma lem5474373 : term557.
Proof. exact (@lem5474362 (@lem5474372)). Qed.
Lemma lem5474375 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474376 : term372 = term373.
Proof. exact (@lem5474375 term332 term332). Qed.
Lemma lem5474377 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474378 : term375 = term332.
Proof. exact (EQ_MP (@lem5474377) (@lem940073)). Qed.
Lemma lem5474379 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474380 : term373 = term331.
Proof. exact (MK_COMB (@lem5474379) (@lem5474378)). Qed.
Lemma lem5474381 : term372 = term331.
Proof. exact (TRANS (@lem5474376) (@lem5474380)). Qed.
Lemma lem5474383 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5474384 : term390 = term395.
Proof. exact (@lem5474383 term332 term332). Qed.
Lemma lem5474385 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474386 : term375 = term332.
Proof. exact (EQ_MP (@lem5474385) (@lem940073)). Qed.
Lemma lem5474387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474388 : term373 = term331.
Proof. exact (MK_COMB (@lem5474387) (@lem5474386)). Qed.
Lemma lem5474389 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5474390 : term395 = term363.
Proof. exact (MK_COMB (@lem5474389) (@lem5474388)). Qed.
Lemma lem5474391 : term390 = term363.
Proof. exact (TRANS (@lem5474384) (@lem5474390)). Qed.
Lemma lem5474392 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474393 : term558 = term550.
Proof. exact (MK_COMB (@lem5474392) (@lem5474391)). Qed.
Lemma lem5474394 : term559 = term552.
Proof. exact (MK_COMB (@lem5474393) (@lem5474381)). Qed.
Lemma lem5474396 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5474397 : term552 = term318.
Proof. exact (@lem5474396 term332). Qed.
Lemma lem5474398 : term559 = term318.
Proof. exact (TRANS (@lem5474394) (@lem5474397)). Qed.
Lemma lem5474399 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474400 : term561 = term562.
Proof. exact (MK_COMB (@lem5474399) (@lem5474398)). Qed.
Lemma lem5474401 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5474402 : term563 = term524.
Proof. exact (MK_COMB (@lem5474400) (@lem5474401)). Qed.
Lemma lem5474404 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474405 : term524 = term318.
Proof. exact (@lem5474404 term332). Qed.
Lemma lem5474406 : term563 = term318.
Proof. exact (TRANS (@lem5474402) (@lem5474405)). Qed.
Lemma lem5474408 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474409 : term372 = term373.
Proof. exact (@lem5474408 term332 term332). Qed.
Lemma lem5474410 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474411 : term375 = term332.
Proof. exact (EQ_MP (@lem5474410) (@lem940073)). Qed.
Lemma lem5474412 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474413 : term373 = term331.
Proof. exact (MK_COMB (@lem5474412) (@lem5474411)). Qed.
Lemma lem5474414 : term372 = term331.
Proof. exact (TRANS (@lem5474409) (@lem5474413)). Qed.
Lemma lem5474415 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5474416 : term564 = term524.
Proof. exact (MK_COMB (@lem5474415) (@lem5474414)). Qed.
Lemma lem5474418 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474419 : term524 = term318.
Proof. exact (@lem5474418 term332). Qed.
Lemma lem5474420 : term564 = term318.
Proof. exact (TRANS (@lem5474416) (@lem5474419)). Qed.
Lemma lem5474421 : term318 = term564.
Proof. exact (SYM (@lem5474420)). Qed.
Lemma lem5474422 : term563 = term564.
Proof. exact (TRANS (@lem5474406) (@lem5474421)). Qed.
Lemma lem5474423 : term553 = term360.
Proof. exact (@lem5474373 (@lem5474422)). Qed.
Lemma lem5474424 : term552 = term360.
Proof. exact (TRANS (@lem5474339) (@lem5474423)). Qed.
Lemma lem5474426 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5474427 : term360 = term318.
Proof. exact (@lem5474426 term318). Qed.
Lemma lem5474428 : term552 = term318.
Proof. exact (TRANS (@lem5474424) (@lem5474427)). Qed.
Lemma lem5474429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474430 : term565 = term562.
Proof. exact (MK_COMB (@lem5474429) (@lem5474428)). Qed.
Lemma lem5474431 (_70581 : int) : (real_of_int _70581) = (real_of_int _70581).
Proof. exact (eq_refl (real_of_int _70581)). Qed.
Lemma lem5474432 (_70581 : int) : (term549 _70581) = (term566 _70581).
Proof. exact (MK_COMB (@lem5474430) (@lem5474431 _70581)). Qed.
Lemma lem5474433 (_70581 : int) : (term548 _70581) = (term566 _70581).
Proof. exact (TRANS (@lem5474330 _70581) (@lem5474432 _70581)). Qed.
Lemma lem5474434 (_70581 : int) : (term566 _70581) = term318.
Proof. exact (@lem1982719 (real_of_int _70581)). Qed.
Lemma lem5474435 (_70581 : int) : (term548 _70581) = term318.
Proof. exact (TRANS (@lem5474433 _70581) (@lem5474434 _70581)). Qed.
Lemma lem5474436 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474437 (_70581 : int) : (term567 _70581) = term568.
Proof. exact (MK_COMB (@lem5474436) (@lem5474435 _70581)). Qed.
Lemma lem5474438 (_70584 : int) : (term582 _70584) = (term583 _70584).
Proof. exact (@lem1982759 (real_of_int _70584) (term411 _70584) term363). Qed.
Lemma lem5474439 (_70584 : int) : (term584 _70584) = (term549 _70584).
Proof. exact (@lem1982715 term363 (real_of_int _70584)). Qed.
Lemma lem5474441 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474442 : term331 = term389.
Proof. exact (@lem5474441 term332). Qed.
Lemma lem5474444 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5474445 : term363 = term364.
Proof. exact (@lem5474444 term332). Qed.
Lemma lem5474446 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474447 : term550 = term551.
Proof. exact (MK_COMB (@lem5474446) (@lem5474445)). Qed.
Lemma lem5474448 : term552 = term553.
Proof. exact (MK_COMB (@lem5474447) (@lem5474442)). Qed.
Lemma lem5474449 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5474451 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474452 : term513 = term519.
Proof. exact (@lem5474451 (NUMERAL 0) term332). Qed.
Lemma lem5474453 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474454 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474455 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474454 h1) (fun h1 : term519 = True => @lem5474453)). Qed.
Lemma lem5474456 : term519 = True.
Proof. exact (EQ_MP (@lem5474455) (@lem5474453)). Qed.
Lemma lem5474457 : term513 = True.
Proof. exact (TRANS (@lem5474452) (@lem5474456)). Qed.
Lemma lem5474458 : True = term513.
Proof. exact (SYM (@lem5474457)). Qed.
Lemma lem5474459 : term513.
Proof. exact (EQ_MP (@lem5474458) (@lem0)). Qed.
Lemma lem5474460 : term555.
Proof. exact (@lem5474449 (@lem5474459)). Qed.
Lemma lem5474462 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474463 : term513 = term519.
Proof. exact (@lem5474462 (NUMERAL 0) term332). Qed.
Lemma lem5474464 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474465 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474466 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474465 h1) (fun h1 : term519 = True => @lem5474464)). Qed.
Lemma lem5474467 : term519 = True.
Proof. exact (EQ_MP (@lem5474466) (@lem5474464)). Qed.
Lemma lem5474468 : term513 = True.
Proof. exact (TRANS (@lem5474463) (@lem5474467)). Qed.
Lemma lem5474469 : True = term513.
Proof. exact (SYM (@lem5474468)). Qed.
Lemma lem5474470 : term513.
Proof. exact (EQ_MP (@lem5474469) (@lem0)). Qed.
Lemma lem5474471 : term556.
Proof. exact (@lem5474460 (@lem5474470)). Qed.
Lemma lem5474473 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474474 : term513 = term519.
Proof. exact (@lem5474473 (NUMERAL 0) term332). Qed.
Lemma lem5474475 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474476 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474477 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474476 h1) (fun h1 : term519 = True => @lem5474475)). Qed.
Lemma lem5474478 : term519 = True.
Proof. exact (EQ_MP (@lem5474477) (@lem5474475)). Qed.
Lemma lem5474479 : term513 = True.
Proof. exact (TRANS (@lem5474474) (@lem5474478)). Qed.
Lemma lem5474480 : True = term513.
Proof. exact (SYM (@lem5474479)). Qed.
Lemma lem5474481 : term513.
Proof. exact (EQ_MP (@lem5474480) (@lem0)). Qed.
Lemma lem5474482 : term557.
Proof. exact (@lem5474471 (@lem5474481)). Qed.
Lemma lem5474484 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474485 : term372 = term373.
Proof. exact (@lem5474484 term332 term332). Qed.
Lemma lem5474486 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474487 : term375 = term332.
Proof. exact (EQ_MP (@lem5474486) (@lem940073)). Qed.
Lemma lem5474488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474489 : term373 = term331.
Proof. exact (MK_COMB (@lem5474488) (@lem5474487)). Qed.
Lemma lem5474490 : term372 = term331.
Proof. exact (TRANS (@lem5474485) (@lem5474489)). Qed.
Lemma lem5474492 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5474493 : term390 = term395.
Proof. exact (@lem5474492 term332 term332). Qed.
Lemma lem5474494 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474495 : term375 = term332.
Proof. exact (EQ_MP (@lem5474494) (@lem940073)). Qed.
Lemma lem5474496 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474497 : term373 = term331.
Proof. exact (MK_COMB (@lem5474496) (@lem5474495)). Qed.
Lemma lem5474498 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5474499 : term395 = term363.
Proof. exact (MK_COMB (@lem5474498) (@lem5474497)). Qed.
Lemma lem5474500 : term390 = term363.
Proof. exact (TRANS (@lem5474493) (@lem5474499)). Qed.
Lemma lem5474501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474502 : term558 = term550.
Proof. exact (MK_COMB (@lem5474501) (@lem5474500)). Qed.
Lemma lem5474503 : term559 = term552.
Proof. exact (MK_COMB (@lem5474502) (@lem5474490)). Qed.
Lemma lem5474505 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5474506 : term552 = term318.
Proof. exact (@lem5474505 term332). Qed.
Lemma lem5474507 : term559 = term318.
Proof. exact (TRANS (@lem5474503) (@lem5474506)). Qed.
Lemma lem5474508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474509 : term561 = term562.
Proof. exact (MK_COMB (@lem5474508) (@lem5474507)). Qed.
Lemma lem5474510 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5474511 : term563 = term524.
Proof. exact (MK_COMB (@lem5474509) (@lem5474510)). Qed.
Lemma lem5474513 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474514 : term524 = term318.
Proof. exact (@lem5474513 term332). Qed.
Lemma lem5474515 : term563 = term318.
Proof. exact (TRANS (@lem5474511) (@lem5474514)). Qed.
Lemma lem5474517 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474518 : term372 = term373.
Proof. exact (@lem5474517 term332 term332). Qed.
Lemma lem5474519 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474520 : term375 = term332.
Proof. exact (EQ_MP (@lem5474519) (@lem940073)). Qed.
Lemma lem5474521 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474522 : term373 = term331.
Proof. exact (MK_COMB (@lem5474521) (@lem5474520)). Qed.
Lemma lem5474523 : term372 = term331.
Proof. exact (TRANS (@lem5474518) (@lem5474522)). Qed.
Lemma lem5474524 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5474525 : term564 = term524.
Proof. exact (MK_COMB (@lem5474524) (@lem5474523)). Qed.
Lemma lem5474527 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474528 : term524 = term318.
Proof. exact (@lem5474527 term332). Qed.
Lemma lem5474529 : term564 = term318.
Proof. exact (TRANS (@lem5474525) (@lem5474528)). Qed.
Lemma lem5474530 : term318 = term564.
Proof. exact (SYM (@lem5474529)). Qed.
Lemma lem5474531 : term563 = term564.
Proof. exact (TRANS (@lem5474515) (@lem5474530)). Qed.
Lemma lem5474532 : term553 = term360.
Proof. exact (@lem5474482 (@lem5474531)). Qed.
Lemma lem5474533 : term552 = term360.
Proof. exact (TRANS (@lem5474448) (@lem5474532)). Qed.
Lemma lem5474535 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5474536 : term360 = term318.
Proof. exact (@lem5474535 term318). Qed.
Lemma lem5474537 : term552 = term318.
Proof. exact (TRANS (@lem5474533) (@lem5474536)). Qed.
Lemma lem5474538 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474539 : term565 = term562.
Proof. exact (MK_COMB (@lem5474538) (@lem5474537)). Qed.
Lemma lem5474540 (_70584 : int) : (real_of_int _70584) = (real_of_int _70584).
Proof. exact (eq_refl (real_of_int _70584)). Qed.
Lemma lem5474541 (_70584 : int) : (term549 _70584) = (term566 _70584).
Proof. exact (MK_COMB (@lem5474539) (@lem5474540 _70584)). Qed.
Lemma lem5474542 (_70584 : int) : (term584 _70584) = (term566 _70584).
Proof. exact (TRANS (@lem5474439 _70584) (@lem5474541 _70584)). Qed.
Lemma lem5474543 (_70584 : int) : (term566 _70584) = term318.
Proof. exact (@lem1982719 (real_of_int _70584)). Qed.
Lemma lem5474544 (_70584 : int) : (term584 _70584) = term318.
Proof. exact (TRANS (@lem5474542 _70584) (@lem5474543 _70584)). Qed.
Lemma lem5474545 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474546 (_70584 : int) : (term585 _70584) = term568.
Proof. exact (MK_COMB (@lem5474545) (@lem5474544 _70584)). Qed.
Lemma lem5474547 : term363 = term363.
Proof. exact (eq_refl term363). Qed.
Lemma lem5474548 (_70584 : int) : (term583 _70584) = term586.
Proof. exact (MK_COMB (@lem5474546 _70584) (@lem5474547)). Qed.
Lemma lem5474549 (_70584 : int) : (term582 _70584) = term586.
Proof. exact (TRANS (@lem5474438 _70584) (@lem5474548 _70584)). Qed.
Lemma lem5474550 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5474551 (_70584 : int) : (term582 _70584) = term363.
Proof. exact (TRANS (@lem5474549 _70584) (@lem5474550)). Qed.
Lemma lem5474552 (_70581 : int) (_70584 : int) : (term580 _70581 _70584) = term586.
Proof. exact (MK_COMB (@lem5474437 _70581) (@lem5474551 _70584)). Qed.
Lemma lem5474553 (_70581 : int) (_70584 : int) : (term579 _70581 _70584) = term586.
Proof. exact (TRANS (@lem5474329 _70581 _70584) (@lem5474552 _70581 _70584)). Qed.
Lemma lem5474554 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5474555 (_70581 : int) (_70584 : int) : (term579 _70581 _70584) = term363.
Proof. exact (TRANS (@lem5474553 _70581 _70584) (@lem5474554)). Qed.
Lemma lem5474556 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474557 (_70581 : int) (_70584 : int) : (term587 _70581 _70584) = term588.
Proof. exact (MK_COMB (@lem5474556) (@lem5474555 _70581 _70584)). Qed.
Lemma lem5474558 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474559 (_70581 : int) (_70584 : int) : (term578 _70581 _70584) = term589.
Proof. exact (MK_COMB (@lem5474557 _70581 _70584) (@lem5474558)). Qed.
Lemma lem5474560 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : term589.
Proof. exact (EQ_MP (@lem5474559 _70581 _70584) (@lem5474328 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474562 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5474563 : term589 = term590.
Proof. exact (@lem5474562 term318 term363). Qed.
Lemma lem5474565 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5474566 : term363 = term364.
Proof. exact (@lem5474565 term332). Qed.
Lemma lem5474568 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474569 : term318 = term360.
Proof. exact (@lem5474568 (NUMERAL 0)). Qed.
Lemma lem5474570 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5474571 : term320 = term591.
Proof. exact (MK_COMB (@lem5474570) (@lem5474569)). Qed.
Lemma lem5474572 : term590 = term592.
Proof. exact (MK_COMB (@lem5474571) (@lem5474566)). Qed.
Lemma lem5474573 : term593.
Proof. exact (@lem1980026 term318 term331 term363 term331). Qed.
Lemma lem5474575 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474576 : term513 = term519.
Proof. exact (@lem5474575 (NUMERAL 0) term332). Qed.
Lemma lem5474577 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474578 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474579 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474578 h1) (fun h1 : term519 = True => @lem5474577)). Qed.
Lemma lem5474580 : term519 = True.
Proof. exact (EQ_MP (@lem5474579) (@lem5474577)). Qed.
Lemma lem5474581 : term513 = True.
Proof. exact (TRANS (@lem5474576) (@lem5474580)). Qed.
Lemma lem5474582 : True = term513.
Proof. exact (SYM (@lem5474581)). Qed.
Lemma lem5474583 : term513.
Proof. exact (EQ_MP (@lem5474582) (@lem0)). Qed.
Lemma lem5474584 : term594.
Proof. exact (@lem5474573 (@lem5474583)). Qed.
Lemma lem5474586 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474587 : term513 = term519.
Proof. exact (@lem5474586 (NUMERAL 0) term332). Qed.
Lemma lem5474588 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474589 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474590 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474589 h1) (fun h1 : term519 = True => @lem5474588)). Qed.
Lemma lem5474591 : term519 = True.
Proof. exact (EQ_MP (@lem5474590) (@lem5474588)). Qed.
Lemma lem5474592 : term513 = True.
Proof. exact (TRANS (@lem5474587) (@lem5474591)). Qed.
Lemma lem5474593 : True = term513.
Proof. exact (SYM (@lem5474592)). Qed.
Lemma lem5474594 : term513.
Proof. exact (EQ_MP (@lem5474593) (@lem0)). Qed.
Lemma lem5474595 : term592 = term595.
Proof. exact (@lem5474584 (@lem5474594)). Qed.
Lemma lem5474597 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5474598 : term390 = term395.
Proof. exact (@lem5474597 term332 term332). Qed.
Lemma lem5474599 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474600 : term375 = term332.
Proof. exact (EQ_MP (@lem5474599) (@lem940073)). Qed.
Lemma lem5474601 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474602 : term373 = term331.
Proof. exact (MK_COMB (@lem5474601) (@lem5474600)). Qed.
Lemma lem5474603 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5474604 : term395 = term363.
Proof. exact (MK_COMB (@lem5474603) (@lem5474602)). Qed.
Lemma lem5474605 : term390 = term363.
Proof. exact (TRANS (@lem5474598) (@lem5474604)). Qed.
Lemma lem5474607 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474608 : term524 = term318.
Proof. exact (@lem5474607 term332). Qed.
Lemma lem5474609 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5474610 : term596 = term320.
Proof. exact (MK_COMB (@lem5474609) (@lem5474608)). Qed.
Lemma lem5474611 : term595 = term590.
Proof. exact (MK_COMB (@lem5474610) (@lem5474605)). Qed.
Lemma lem5474613 (m : nat) (n : nat) : (term597 m n) = (term598 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5474614 : term590 = term599.
Proof. exact (@lem5474613 (NUMERAL 0) term332). Qed.
Lemma lem5474615 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474616 (h1 : term520 = (BIT1 0)) : (term332 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5474617 : (term520 = (BIT1 0)) = ((term332 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474616 h1) (fun h1 : (term332 = (NUMERAL 0)) = False => @lem5474615)). Qed.
Lemma lem5474618 : (term332 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5474617) (@lem5474615)). Qed.
Lemma lem5474619 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5474620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5474621 : term600 = (and True).
Proof. exact (MK_COMB (@lem5474620) (@lem5474619)). Qed.
Lemma lem5474622 : term599 = (True /\ False).
Proof. exact (MK_COMB (@lem5474621) (@lem5474618)). Qed.
Lemma lem5474624 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5474625 : term599 = False.
Proof. exact (TRANS (@lem5474622) (@lem5474624)). Qed.
Lemma lem5474626 : term590 = False.
Proof. exact (TRANS (@lem5474614) (@lem5474625)). Qed.
Lemma lem5474627 : term595 = False.
Proof. exact (TRANS (@lem5474611) (@lem5474626)). Qed.
Lemma lem5474628 : term592 = False.
Proof. exact (TRANS (@lem5474595) (@lem5474627)). Qed.
Lemma lem5474629 : term590 = False.
Proof. exact (TRANS (@lem5474572) (@lem5474628)). Qed.
Lemma lem5474630 : term589 = False.
Proof. exact (TRANS (@lem5474563) (@lem5474629)). Qed.
Lemma lem5474631 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term511 _70583 _70580 _70581 _70582 _70584) : False.
Proof. exact (EQ_MP (@lem5474630) (@lem5474560 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474632 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term601 _70583 _70580 _70581 _70582 _70584.
Proof. exact (h1). Qed.
Lemma lem5474633 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term507 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5474632 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474635 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term494 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5474633 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474637 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term481 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5474635 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474639 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term468 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5474637 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474641 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term455 _70583 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5474639 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474643 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term437 _70580 _70581 _70582 _70584.
Proof. exact (proj2 (@lem5474641 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474644 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term415 _70580 _70582 _70581 _70583.
Proof. exact (proj1 (@lem5474641 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474646 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term409 _70580 _70582.
Proof. exact (proj1 (@lem5474644 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474647 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term403 _70582 _70584.
Proof. exact (proj2 (@lem5474643 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474648 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term419 _70580 _70581 _70584.
Proof. exact (proj1 (@lem5474643 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474650 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term413 _70580 _70584.
Proof. exact (proj1 (@lem5474648 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474652 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5474653 : term512 = term513.
Proof. exact (@lem5474652 term318 term331). Qed.
Lemma lem5474655 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474656 : term331 = term389.
Proof. exact (@lem5474655 term332). Qed.
Lemma lem5474658 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474659 : term318 = term360.
Proof. exact (@lem5474658 (NUMERAL 0)). Qed.
Lemma lem5474660 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474661 : term514 = term515.
Proof. exact (MK_COMB (@lem5474660) (@lem5474659)). Qed.
Lemma lem5474662 : term513 = term516.
Proof. exact (MK_COMB (@lem5474661) (@lem5474656)). Qed.
Lemma lem5474663 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5474665 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474666 : term513 = term519.
Proof. exact (@lem5474665 (NUMERAL 0) term332). Qed.
Lemma lem5474667 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474668 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474669 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474668 h1) (fun h1 : term519 = True => @lem5474667)). Qed.
Lemma lem5474670 : term519 = True.
Proof. exact (EQ_MP (@lem5474669) (@lem5474667)). Qed.
Lemma lem5474671 : term513 = True.
Proof. exact (TRANS (@lem5474666) (@lem5474670)). Qed.
Lemma lem5474672 : True = term513.
Proof. exact (SYM (@lem5474671)). Qed.
Lemma lem5474673 : term513.
Proof. exact (EQ_MP (@lem5474672) (@lem0)). Qed.
Lemma lem5474674 : term521.
Proof. exact (@lem5474663 (@lem5474673)). Qed.
Lemma lem5474676 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474677 : term513 = term519.
Proof. exact (@lem5474676 (NUMERAL 0) term332). Qed.
Lemma lem5474678 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474679 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474680 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474679 h1) (fun h1 : term519 = True => @lem5474678)). Qed.
Lemma lem5474681 : term519 = True.
Proof. exact (EQ_MP (@lem5474680) (@lem5474678)). Qed.
Lemma lem5474682 : term513 = True.
Proof. exact (TRANS (@lem5474677) (@lem5474681)). Qed.
Lemma lem5474683 : True = term513.
Proof. exact (SYM (@lem5474682)). Qed.
Lemma lem5474684 : term513.
Proof. exact (EQ_MP (@lem5474683) (@lem0)). Qed.
Lemma lem5474685 : term516 = term522.
Proof. exact (@lem5474674 (@lem5474684)). Qed.
Lemma lem5474687 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474688 : term372 = term373.
Proof. exact (@lem5474687 term332 term332). Qed.
Lemma lem5474689 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474690 : term375 = term332.
Proof. exact (EQ_MP (@lem5474689) (@lem940073)). Qed.
Lemma lem5474691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474692 : term373 = term331.
Proof. exact (MK_COMB (@lem5474691) (@lem5474690)). Qed.
Lemma lem5474693 : term372 = term331.
Proof. exact (TRANS (@lem5474688) (@lem5474692)). Qed.
Lemma lem5474695 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474696 : term524 = term318.
Proof. exact (@lem5474695 term332). Qed.
Lemma lem5474697 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474698 : term525 = term514.
Proof. exact (MK_COMB (@lem5474697) (@lem5474696)). Qed.
Lemma lem5474699 : term522 = term513.
Proof. exact (MK_COMB (@lem5474698) (@lem5474693)). Qed.
Lemma lem5474701 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474702 : term513 = term519.
Proof. exact (@lem5474701 (NUMERAL 0) term332). Qed.
Lemma lem5474703 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474704 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474705 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474704 h1) (fun h1 : term519 = True => @lem5474703)). Qed.
Lemma lem5474706 : term519 = True.
Proof. exact (EQ_MP (@lem5474705) (@lem5474703)). Qed.
Lemma lem5474707 : term513 = True.
Proof. exact (TRANS (@lem5474702) (@lem5474706)). Qed.
Lemma lem5474708 : term522 = True.
Proof. exact (TRANS (@lem5474699) (@lem5474707)). Qed.
Lemma lem5474709 : term516 = True.
Proof. exact (TRANS (@lem5474685) (@lem5474708)). Qed.
Lemma lem5474710 : term513 = True.
Proof. exact (TRANS (@lem5474662) (@lem5474709)). Qed.
Lemma lem5474711 : term512 = True.
Proof. exact (TRANS (@lem5474653) (@lem5474710)). Qed.
Lemma lem5474712 : True = term512.
Proof. exact (SYM (@lem5474711)). Qed.
Lemma lem5474713 : term512.
Proof. exact (EQ_MP (@lem5474712) (@lem0)). Qed.
Lemma lem5474714 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term532 _70582 _70584.
Proof. exact (conj (@lem5474713) (@lem5474647 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474716 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5474717 (_70582 : int) (_70584 : int) : term533 _70582 _70584.
Proof. exact (@lem5474716 term331 (term400 _70582 _70584)). Qed.
Lemma lem5474718 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term534 _70582 _70584.
Proof. exact (@lem5474717 _70582 _70584 (@lem5474714 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474719 (_70582 : int) (_70584 : int) : (term535 _70582 _70584) = (term400 _70582 _70584).
Proof. exact (@lem1982733 (term400 _70582 _70584)). Qed.
Lemma lem5474720 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474721 (_70582 : int) (_70584 : int) : (term536 _70582 _70584) = (term402 _70582 _70584).
Proof. exact (MK_COMB (@lem5474720) (@lem5474719 _70582 _70584)). Qed.
Lemma lem5474722 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474723 (_70582 : int) (_70584 : int) : (term534 _70582 _70584) = (term403 _70582 _70584).
Proof. exact (MK_COMB (@lem5474721 _70582 _70584) (@lem5474722)). Qed.
Lemma lem5474724 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term403 _70582 _70584.
Proof. exact (EQ_MP (@lem5474723 _70582 _70584) (@lem5474718 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474726 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5474727 : term512 = term513.
Proof. exact (@lem5474726 term318 term331). Qed.
Lemma lem5474729 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474730 : term331 = term389.
Proof. exact (@lem5474729 term332). Qed.
Lemma lem5474732 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474733 : term318 = term360.
Proof. exact (@lem5474732 (NUMERAL 0)). Qed.
Lemma lem5474734 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474735 : term514 = term515.
Proof. exact (MK_COMB (@lem5474734) (@lem5474733)). Qed.
Lemma lem5474736 : term513 = term516.
Proof. exact (MK_COMB (@lem5474735) (@lem5474730)). Qed.
Lemma lem5474737 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5474739 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474740 : term513 = term519.
Proof. exact (@lem5474739 (NUMERAL 0) term332). Qed.
Lemma lem5474741 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474742 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474743 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474742 h1) (fun h1 : term519 = True => @lem5474741)). Qed.
Lemma lem5474744 : term519 = True.
Proof. exact (EQ_MP (@lem5474743) (@lem5474741)). Qed.
Lemma lem5474745 : term513 = True.
Proof. exact (TRANS (@lem5474740) (@lem5474744)). Qed.
Lemma lem5474746 : True = term513.
Proof. exact (SYM (@lem5474745)). Qed.
Lemma lem5474747 : term513.
Proof. exact (EQ_MP (@lem5474746) (@lem0)). Qed.
Lemma lem5474748 : term521.
Proof. exact (@lem5474737 (@lem5474747)). Qed.
Lemma lem5474750 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474751 : term513 = term519.
Proof. exact (@lem5474750 (NUMERAL 0) term332). Qed.
Lemma lem5474752 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474753 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474754 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474753 h1) (fun h1 : term519 = True => @lem5474752)). Qed.
Lemma lem5474755 : term519 = True.
Proof. exact (EQ_MP (@lem5474754) (@lem5474752)). Qed.
Lemma lem5474756 : term513 = True.
Proof. exact (TRANS (@lem5474751) (@lem5474755)). Qed.
Lemma lem5474757 : True = term513.
Proof. exact (SYM (@lem5474756)). Qed.
Lemma lem5474758 : term513.
Proof. exact (EQ_MP (@lem5474757) (@lem0)). Qed.
Lemma lem5474759 : term516 = term522.
Proof. exact (@lem5474748 (@lem5474758)). Qed.
Lemma lem5474761 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474762 : term372 = term373.
Proof. exact (@lem5474761 term332 term332). Qed.
Lemma lem5474763 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474764 : term375 = term332.
Proof. exact (EQ_MP (@lem5474763) (@lem940073)). Qed.
Lemma lem5474765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474766 : term373 = term331.
Proof. exact (MK_COMB (@lem5474765) (@lem5474764)). Qed.
Lemma lem5474767 : term372 = term331.
Proof. exact (TRANS (@lem5474762) (@lem5474766)). Qed.
Lemma lem5474769 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474770 : term524 = term318.
Proof. exact (@lem5474769 term332). Qed.
Lemma lem5474771 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474772 : term525 = term514.
Proof. exact (MK_COMB (@lem5474771) (@lem5474770)). Qed.
Lemma lem5474773 : term522 = term513.
Proof. exact (MK_COMB (@lem5474772) (@lem5474767)). Qed.
Lemma lem5474775 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474776 : term513 = term519.
Proof. exact (@lem5474775 (NUMERAL 0) term332). Qed.
Lemma lem5474777 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474778 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474779 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474778 h1) (fun h1 : term519 = True => @lem5474777)). Qed.
Lemma lem5474780 : term519 = True.
Proof. exact (EQ_MP (@lem5474779) (@lem5474777)). Qed.
Lemma lem5474781 : term513 = True.
Proof. exact (TRANS (@lem5474776) (@lem5474780)). Qed.
Lemma lem5474782 : term522 = True.
Proof. exact (TRANS (@lem5474773) (@lem5474781)). Qed.
Lemma lem5474783 : term516 = True.
Proof. exact (TRANS (@lem5474759) (@lem5474782)). Qed.
Lemma lem5474784 : term513 = True.
Proof. exact (TRANS (@lem5474736) (@lem5474783)). Qed.
Lemma lem5474785 : term512 = True.
Proof. exact (TRANS (@lem5474727) (@lem5474784)). Qed.
Lemma lem5474786 : True = term512.
Proof. exact (SYM (@lem5474785)). Qed.
Lemma lem5474787 : term512.
Proof. exact (EQ_MP (@lem5474786) (@lem0)). Qed.
Lemma lem5474788 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term526 _70580 _70582.
Proof. exact (conj (@lem5474787) (@lem5474646 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474790 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5474791 (_70580 : int) (_70582 : int) : term528 _70580 _70582.
Proof. exact (@lem5474790 term331 (term406 _70580 _70582)). Qed.
Lemma lem5474792 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term529 _70580 _70582.
Proof. exact (@lem5474791 _70580 _70582 (@lem5474788 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474793 (_70580 : int) (_70582 : int) : (term530 _70580 _70582) = (term406 _70580 _70582).
Proof. exact (@lem1982733 (term406 _70580 _70582)). Qed.
Lemma lem5474794 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474795 (_70580 : int) (_70582 : int) : (term531 _70580 _70582) = (term408 _70580 _70582).
Proof. exact (MK_COMB (@lem5474794) (@lem5474793 _70580 _70582)). Qed.
Lemma lem5474796 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474797 (_70580 : int) (_70582 : int) : (term529 _70580 _70582) = (term409 _70580 _70582).
Proof. exact (MK_COMB (@lem5474795 _70580 _70582) (@lem5474796)). Qed.
Lemma lem5474798 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term409 _70580 _70582.
Proof. exact (EQ_MP (@lem5474797 _70580 _70582) (@lem5474792 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474800 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5474801 : term512 = term513.
Proof. exact (@lem5474800 term318 term331). Qed.
Lemma lem5474803 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474804 : term331 = term389.
Proof. exact (@lem5474803 term332). Qed.
Lemma lem5474806 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474807 : term318 = term360.
Proof. exact (@lem5474806 (NUMERAL 0)). Qed.
Lemma lem5474808 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474809 : term514 = term515.
Proof. exact (MK_COMB (@lem5474808) (@lem5474807)). Qed.
Lemma lem5474810 : term513 = term516.
Proof. exact (MK_COMB (@lem5474809) (@lem5474804)). Qed.
Lemma lem5474811 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5474813 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474814 : term513 = term519.
Proof. exact (@lem5474813 (NUMERAL 0) term332). Qed.
Lemma lem5474815 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474816 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474817 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474816 h1) (fun h1 : term519 = True => @lem5474815)). Qed.
Lemma lem5474818 : term519 = True.
Proof. exact (EQ_MP (@lem5474817) (@lem5474815)). Qed.
Lemma lem5474819 : term513 = True.
Proof. exact (TRANS (@lem5474814) (@lem5474818)). Qed.
Lemma lem5474820 : True = term513.
Proof. exact (SYM (@lem5474819)). Qed.
Lemma lem5474821 : term513.
Proof. exact (EQ_MP (@lem5474820) (@lem0)). Qed.
Lemma lem5474822 : term521.
Proof. exact (@lem5474811 (@lem5474821)). Qed.
Lemma lem5474824 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474825 : term513 = term519.
Proof. exact (@lem5474824 (NUMERAL 0) term332). Qed.
Lemma lem5474826 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474827 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474828 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474827 h1) (fun h1 : term519 = True => @lem5474826)). Qed.
Lemma lem5474829 : term519 = True.
Proof. exact (EQ_MP (@lem5474828) (@lem5474826)). Qed.
Lemma lem5474830 : term513 = True.
Proof. exact (TRANS (@lem5474825) (@lem5474829)). Qed.
Lemma lem5474831 : True = term513.
Proof. exact (SYM (@lem5474830)). Qed.
Lemma lem5474832 : term513.
Proof. exact (EQ_MP (@lem5474831) (@lem0)). Qed.
Lemma lem5474833 : term516 = term522.
Proof. exact (@lem5474822 (@lem5474832)). Qed.
Lemma lem5474835 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474836 : term372 = term373.
Proof. exact (@lem5474835 term332 term332). Qed.
Lemma lem5474837 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474838 : term375 = term332.
Proof. exact (EQ_MP (@lem5474837) (@lem940073)). Qed.
Lemma lem5474839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474840 : term373 = term331.
Proof. exact (MK_COMB (@lem5474839) (@lem5474838)). Qed.
Lemma lem5474841 : term372 = term331.
Proof. exact (TRANS (@lem5474836) (@lem5474840)). Qed.
Lemma lem5474843 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474844 : term524 = term318.
Proof. exact (@lem5474843 term332). Qed.
Lemma lem5474845 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5474846 : term525 = term514.
Proof. exact (MK_COMB (@lem5474845) (@lem5474844)). Qed.
Lemma lem5474847 : term522 = term513.
Proof. exact (MK_COMB (@lem5474846) (@lem5474841)). Qed.
Lemma lem5474849 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474850 : term513 = term519.
Proof. exact (@lem5474849 (NUMERAL 0) term332). Qed.
Lemma lem5474851 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474852 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474853 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474852 h1) (fun h1 : term519 = True => @lem5474851)). Qed.
Lemma lem5474854 : term519 = True.
Proof. exact (EQ_MP (@lem5474853) (@lem5474851)). Qed.
Lemma lem5474855 : term513 = True.
Proof. exact (TRANS (@lem5474850) (@lem5474854)). Qed.
Lemma lem5474856 : term522 = True.
Proof. exact (TRANS (@lem5474847) (@lem5474855)). Qed.
Lemma lem5474857 : term516 = True.
Proof. exact (TRANS (@lem5474833) (@lem5474856)). Qed.
Lemma lem5474858 : term513 = True.
Proof. exact (TRANS (@lem5474810) (@lem5474857)). Qed.
Lemma lem5474859 : term512 = True.
Proof. exact (TRANS (@lem5474801) (@lem5474858)). Qed.
Lemma lem5474860 : True = term512.
Proof. exact (SYM (@lem5474859)). Qed.
Lemma lem5474861 : term512.
Proof. exact (EQ_MP (@lem5474860) (@lem0)). Qed.
Lemma lem5474862 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term537 _70580 _70584.
Proof. exact (conj (@lem5474861) (@lem5474650 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474864 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5474865 (_70580 : int) (_70584 : int) : term538 _70580 _70584.
Proof. exact (@lem5474864 term331 (term410 _70580 _70584)). Qed.
Lemma lem5474866 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term539 _70580 _70584.
Proof. exact (@lem5474865 _70580 _70584 (@lem5474862 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474867 (_70580 : int) (_70584 : int) : (term540 _70580 _70584) = (term410 _70580 _70584).
Proof. exact (@lem1982733 (term410 _70580 _70584)). Qed.
Lemma lem5474868 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474869 (_70580 : int) (_70584 : int) : (term541 _70580 _70584) = (term412 _70580 _70584).
Proof. exact (MK_COMB (@lem5474868) (@lem5474867 _70580 _70584)). Qed.
Lemma lem5474870 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474871 (_70580 : int) (_70584 : int) : (term539 _70580 _70584) = (term413 _70580 _70584).
Proof. exact (MK_COMB (@lem5474869 _70580 _70584) (@lem5474870)). Qed.
Lemma lem5474872 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term413 _70580 _70584.
Proof. exact (EQ_MP (@lem5474871 _70580 _70584) (@lem5474866 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474873 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term602 _70584 _70580 _70582.
Proof. exact (conj (@lem5474872 _70583 _70580 _70581 _70582 _70584 h1) (@lem5474798 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474875 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5474876 (_70584 : int) (_70580 : int) (_70582 : int) : term603 _70584 _70580 _70582.
Proof. exact (@lem5474875 (term410 _70580 _70584) (term406 _70580 _70582)). Qed.
Lemma lem5474877 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term604 _70584 _70580 _70582.
Proof. exact (@lem5474876 _70584 _70580 _70582 (@lem5474873 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474878 (_70580 : int) (_70584 : int) (_70582 : int) : (term605 _70584 _70580 _70582) = (term606 _70580 _70584 _70582).
Proof. exact (@lem1982753 (term411 _70580) (real_of_int _70580) (real_of_int _70584) (term411 _70582)). Qed.
Lemma lem5474879 (_70580 : int) : (term548 _70580) = (term549 _70580).
Proof. exact (@lem1982713 term363 (real_of_int _70580)). Qed.
Lemma lem5474881 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5474882 : term331 = term389.
Proof. exact (@lem5474881 term332). Qed.
Lemma lem5474884 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5474885 : term363 = term364.
Proof. exact (@lem5474884 term332). Qed.
Lemma lem5474886 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474887 : term550 = term551.
Proof. exact (MK_COMB (@lem5474886) (@lem5474885)). Qed.
Lemma lem5474888 : term552 = term553.
Proof. exact (MK_COMB (@lem5474887) (@lem5474882)). Qed.
Lemma lem5474889 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5474891 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474892 : term513 = term519.
Proof. exact (@lem5474891 (NUMERAL 0) term332). Qed.
Lemma lem5474893 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474894 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474895 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474894 h1) (fun h1 : term519 = True => @lem5474893)). Qed.
Lemma lem5474896 : term519 = True.
Proof. exact (EQ_MP (@lem5474895) (@lem5474893)). Qed.
Lemma lem5474897 : term513 = True.
Proof. exact (TRANS (@lem5474892) (@lem5474896)). Qed.
Lemma lem5474898 : True = term513.
Proof. exact (SYM (@lem5474897)). Qed.
Lemma lem5474899 : term513.
Proof. exact (EQ_MP (@lem5474898) (@lem0)). Qed.
Lemma lem5474900 : term555.
Proof. exact (@lem5474889 (@lem5474899)). Qed.
Lemma lem5474902 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474903 : term513 = term519.
Proof. exact (@lem5474902 (NUMERAL 0) term332). Qed.
Lemma lem5474904 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474905 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474906 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474905 h1) (fun h1 : term519 = True => @lem5474904)). Qed.
Lemma lem5474907 : term519 = True.
Proof. exact (EQ_MP (@lem5474906) (@lem5474904)). Qed.
Lemma lem5474908 : term513 = True.
Proof. exact (TRANS (@lem5474903) (@lem5474907)). Qed.
Lemma lem5474909 : True = term513.
Proof. exact (SYM (@lem5474908)). Qed.
Lemma lem5474910 : term513.
Proof. exact (EQ_MP (@lem5474909) (@lem0)). Qed.
Lemma lem5474911 : term556.
Proof. exact (@lem5474900 (@lem5474910)). Qed.
Lemma lem5474913 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5474914 : term513 = term519.
Proof. exact (@lem5474913 (NUMERAL 0) term332). Qed.
Lemma lem5474915 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5474916 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5474917 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5474916 h1) (fun h1 : term519 = True => @lem5474915)). Qed.
Lemma lem5474918 : term519 = True.
Proof. exact (EQ_MP (@lem5474917) (@lem5474915)). Qed.
Lemma lem5474919 : term513 = True.
Proof. exact (TRANS (@lem5474914) (@lem5474918)). Qed.
Lemma lem5474920 : True = term513.
Proof. exact (SYM (@lem5474919)). Qed.
Lemma lem5474921 : term513.
Proof. exact (EQ_MP (@lem5474920) (@lem0)). Qed.
Lemma lem5474922 : term557.
Proof. exact (@lem5474911 (@lem5474921)). Qed.
Lemma lem5474924 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474925 : term372 = term373.
Proof. exact (@lem5474924 term332 term332). Qed.
Lemma lem5474926 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474927 : term375 = term332.
Proof. exact (EQ_MP (@lem5474926) (@lem940073)). Qed.
Lemma lem5474928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474929 : term373 = term331.
Proof. exact (MK_COMB (@lem5474928) (@lem5474927)). Qed.
Lemma lem5474930 : term372 = term331.
Proof. exact (TRANS (@lem5474925) (@lem5474929)). Qed.
Lemma lem5474932 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5474933 : term390 = term395.
Proof. exact (@lem5474932 term332 term332). Qed.
Lemma lem5474934 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474935 : term375 = term332.
Proof. exact (EQ_MP (@lem5474934) (@lem940073)). Qed.
Lemma lem5474936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474937 : term373 = term331.
Proof. exact (MK_COMB (@lem5474936) (@lem5474935)). Qed.
Lemma lem5474938 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5474939 : term395 = term363.
Proof. exact (MK_COMB (@lem5474938) (@lem5474937)). Qed.
Lemma lem5474940 : term390 = term363.
Proof. exact (TRANS (@lem5474933) (@lem5474939)). Qed.
Lemma lem5474941 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474942 : term558 = term550.
Proof. exact (MK_COMB (@lem5474941) (@lem5474940)). Qed.
Lemma lem5474943 : term559 = term552.
Proof. exact (MK_COMB (@lem5474942) (@lem5474930)). Qed.
Lemma lem5474945 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5474946 : term552 = term318.
Proof. exact (@lem5474945 term332). Qed.
Lemma lem5474947 : term559 = term318.
Proof. exact (TRANS (@lem5474943) (@lem5474946)). Qed.
Lemma lem5474948 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474949 : term561 = term562.
Proof. exact (MK_COMB (@lem5474948) (@lem5474947)). Qed.
Lemma lem5474950 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5474951 : term563 = term524.
Proof. exact (MK_COMB (@lem5474949) (@lem5474950)). Qed.
Lemma lem5474953 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474954 : term524 = term318.
Proof. exact (@lem5474953 term332). Qed.
Lemma lem5474955 : term563 = term318.
Proof. exact (TRANS (@lem5474951) (@lem5474954)). Qed.
Lemma lem5474957 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5474958 : term372 = term373.
Proof. exact (@lem5474957 term332 term332). Qed.
Lemma lem5474959 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5474960 : term375 = term332.
Proof. exact (EQ_MP (@lem5474959) (@lem940073)). Qed.
Lemma lem5474961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5474962 : term373 = term331.
Proof. exact (MK_COMB (@lem5474961) (@lem5474960)). Qed.
Lemma lem5474963 : term372 = term331.
Proof. exact (TRANS (@lem5474958) (@lem5474962)). Qed.
Lemma lem5474964 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5474965 : term564 = term524.
Proof. exact (MK_COMB (@lem5474964) (@lem5474963)). Qed.
Lemma lem5474967 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5474968 : term524 = term318.
Proof. exact (@lem5474967 term332). Qed.
Lemma lem5474969 : term564 = term318.
Proof. exact (TRANS (@lem5474965) (@lem5474968)). Qed.
Lemma lem5474970 : term318 = term564.
Proof. exact (SYM (@lem5474969)). Qed.
Lemma lem5474971 : term563 = term564.
Proof. exact (TRANS (@lem5474955) (@lem5474970)). Qed.
Lemma lem5474972 : term553 = term360.
Proof. exact (@lem5474922 (@lem5474971)). Qed.
Lemma lem5474973 : term552 = term360.
Proof. exact (TRANS (@lem5474888) (@lem5474972)). Qed.
Lemma lem5474975 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5474976 : term360 = term318.
Proof. exact (@lem5474975 term318). Qed.
Lemma lem5474977 : term552 = term318.
Proof. exact (TRANS (@lem5474973) (@lem5474976)). Qed.
Lemma lem5474978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5474979 : term565 = term562.
Proof. exact (MK_COMB (@lem5474978) (@lem5474977)). Qed.
Lemma lem5474980 (_70580 : int) : (real_of_int _70580) = (real_of_int _70580).
Proof. exact (eq_refl (real_of_int _70580)). Qed.
Lemma lem5474981 (_70580 : int) : (term549 _70580) = (term566 _70580).
Proof. exact (MK_COMB (@lem5474979) (@lem5474980 _70580)). Qed.
Lemma lem5474982 (_70580 : int) : (term548 _70580) = (term566 _70580).
Proof. exact (TRANS (@lem5474879 _70580) (@lem5474981 _70580)). Qed.
Lemma lem5474983 (_70580 : int) : (term566 _70580) = term318.
Proof. exact (@lem1982719 (real_of_int _70580)). Qed.
Lemma lem5474984 (_70580 : int) : (term548 _70580) = term318.
Proof. exact (TRANS (@lem5474982 _70580) (@lem5474983 _70580)). Qed.
Lemma lem5474985 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5474986 (_70580 : int) : (term567 _70580) = term568.
Proof. exact (MK_COMB (@lem5474985) (@lem5474984 _70580)). Qed.
Lemma lem5474987 (_70582 : int) (_70584 : int) : (term406 _70584 _70582) = (term410 _70582 _70584).
Proof. exact (@lem1982761 (term411 _70582) (real_of_int _70584)). Qed.
Lemma lem5474988 (_70580 : int) (_70582 : int) (_70584 : int) : (term606 _70580 _70584 _70582) = (term607 _70582 _70584).
Proof. exact (MK_COMB (@lem5474986 _70580) (@lem5474987 _70582 _70584)). Qed.
Lemma lem5474989 (_70580 : int) (_70582 : int) (_70584 : int) : (term605 _70584 _70580 _70582) = (term607 _70582 _70584).
Proof. exact (TRANS (@lem5474878 _70580 _70584 _70582) (@lem5474988 _70580 _70582 _70584)). Qed.
Lemma lem5474990 (_70582 : int) (_70584 : int) : (term607 _70582 _70584) = (term410 _70582 _70584).
Proof. exact (@lem1982721 (term410 _70582 _70584)). Qed.
Lemma lem5474991 (_70580 : int) (_70582 : int) (_70584 : int) : (term605 _70584 _70580 _70582) = (term410 _70582 _70584).
Proof. exact (TRANS (@lem5474989 _70580 _70582 _70584) (@lem5474990 _70582 _70584)). Qed.
Lemma lem5474992 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5474993 (_70580 : int) (_70582 : int) (_70584 : int) : (term608 _70584 _70580 _70582) = (term412 _70582 _70584).
Proof. exact (MK_COMB (@lem5474992) (@lem5474991 _70580 _70582 _70584)). Qed.
Lemma lem5474994 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5474995 (_70580 : int) (_70582 : int) (_70584 : int) : (term604 _70584 _70580 _70582) = (term413 _70582 _70584).
Proof. exact (MK_COMB (@lem5474993 _70580 _70582 _70584) (@lem5474994)). Qed.
Lemma lem5474996 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term413 _70582 _70584.
Proof. exact (EQ_MP (@lem5474995 _70580 _70582 _70584) (@lem5474877 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5474998 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5474999 : term512 = term513.
Proof. exact (@lem5474998 term318 term331). Qed.
Lemma lem5475001 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475002 : term331 = term389.
Proof. exact (@lem5475001 term332). Qed.
Lemma lem5475004 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475005 : term318 = term360.
Proof. exact (@lem5475004 (NUMERAL 0)). Qed.
Lemma lem5475006 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475007 : term514 = term515.
Proof. exact (MK_COMB (@lem5475006) (@lem5475005)). Qed.
Lemma lem5475008 : term513 = term516.
Proof. exact (MK_COMB (@lem5475007) (@lem5475002)). Qed.
Lemma lem5475009 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5475011 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475012 : term513 = term519.
Proof. exact (@lem5475011 (NUMERAL 0) term332). Qed.
Lemma lem5475013 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475014 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475015 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475014 h1) (fun h1 : term519 = True => @lem5475013)). Qed.
Lemma lem5475016 : term519 = True.
Proof. exact (EQ_MP (@lem5475015) (@lem5475013)). Qed.
Lemma lem5475017 : term513 = True.
Proof. exact (TRANS (@lem5475012) (@lem5475016)). Qed.
Lemma lem5475018 : True = term513.
Proof. exact (SYM (@lem5475017)). Qed.
Lemma lem5475019 : term513.
Proof. exact (EQ_MP (@lem5475018) (@lem0)). Qed.
Lemma lem5475020 : term521.
Proof. exact (@lem5475009 (@lem5475019)). Qed.
Lemma lem5475022 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475023 : term513 = term519.
Proof. exact (@lem5475022 (NUMERAL 0) term332). Qed.
Lemma lem5475024 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475025 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475026 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475025 h1) (fun h1 : term519 = True => @lem5475024)). Qed.
Lemma lem5475027 : term519 = True.
Proof. exact (EQ_MP (@lem5475026) (@lem5475024)). Qed.
Lemma lem5475028 : term513 = True.
Proof. exact (TRANS (@lem5475023) (@lem5475027)). Qed.
Lemma lem5475029 : True = term513.
Proof. exact (SYM (@lem5475028)). Qed.
Lemma lem5475030 : term513.
Proof. exact (EQ_MP (@lem5475029) (@lem0)). Qed.
Lemma lem5475031 : term516 = term522.
Proof. exact (@lem5475020 (@lem5475030)). Qed.
Lemma lem5475033 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475034 : term372 = term373.
Proof. exact (@lem5475033 term332 term332). Qed.
Lemma lem5475035 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475036 : term375 = term332.
Proof. exact (EQ_MP (@lem5475035) (@lem940073)). Qed.
Lemma lem5475037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475038 : term373 = term331.
Proof. exact (MK_COMB (@lem5475037) (@lem5475036)). Qed.
Lemma lem5475039 : term372 = term331.
Proof. exact (TRANS (@lem5475034) (@lem5475038)). Qed.
Lemma lem5475041 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475042 : term524 = term318.
Proof. exact (@lem5475041 term332). Qed.
Lemma lem5475043 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475044 : term525 = term514.
Proof. exact (MK_COMB (@lem5475043) (@lem5475042)). Qed.
Lemma lem5475045 : term522 = term513.
Proof. exact (MK_COMB (@lem5475044) (@lem5475039)). Qed.
Lemma lem5475047 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475048 : term513 = term519.
Proof. exact (@lem5475047 (NUMERAL 0) term332). Qed.
Lemma lem5475049 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475050 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475051 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475050 h1) (fun h1 : term519 = True => @lem5475049)). Qed.
Lemma lem5475052 : term519 = True.
Proof. exact (EQ_MP (@lem5475051) (@lem5475049)). Qed.
Lemma lem5475053 : term513 = True.
Proof. exact (TRANS (@lem5475048) (@lem5475052)). Qed.
Lemma lem5475054 : term522 = True.
Proof. exact (TRANS (@lem5475045) (@lem5475053)). Qed.
Lemma lem5475055 : term516 = True.
Proof. exact (TRANS (@lem5475031) (@lem5475054)). Qed.
Lemma lem5475056 : term513 = True.
Proof. exact (TRANS (@lem5475008) (@lem5475055)). Qed.
Lemma lem5475057 : term512 = True.
Proof. exact (TRANS (@lem5474999) (@lem5475056)). Qed.
Lemma lem5475058 : True = term512.
Proof. exact (SYM (@lem5475057)). Qed.
Lemma lem5475059 : term512.
Proof. exact (EQ_MP (@lem5475058) (@lem0)). Qed.
Lemma lem5475060 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term537 _70582 _70584.
Proof. exact (conj (@lem5475059) (@lem5474996 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5475062 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5475063 (_70582 : int) (_70584 : int) : term538 _70582 _70584.
Proof. exact (@lem5475062 term331 (term410 _70582 _70584)). Qed.
Lemma lem5475064 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term539 _70582 _70584.
Proof. exact (@lem5475063 _70582 _70584 (@lem5475060 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5475065 (_70582 : int) (_70584 : int) : (term540 _70582 _70584) = (term410 _70582 _70584).
Proof. exact (@lem1982733 (term410 _70582 _70584)). Qed.
Lemma lem5475066 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5475067 (_70582 : int) (_70584 : int) : (term541 _70582 _70584) = (term412 _70582 _70584).
Proof. exact (MK_COMB (@lem5475066) (@lem5475065 _70582 _70584)). Qed.
Lemma lem5475068 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5475069 (_70582 : int) (_70584 : int) : (term539 _70582 _70584) = (term413 _70582 _70584).
Proof. exact (MK_COMB (@lem5475067 _70582 _70584) (@lem5475068)). Qed.
Lemma lem5475070 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term413 _70582 _70584.
Proof. exact (EQ_MP (@lem5475069 _70582 _70584) (@lem5475064 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5475071 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term609 _70582 _70584.
Proof. exact (conj (@lem5475070 _70583 _70580 _70581 _70582 _70584 h1) (@lem5474724 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5475073 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5475074 (_70582 : int) (_70584 : int) : term610 _70582 _70584.
Proof. exact (@lem5475073 (term410 _70582 _70584) (term400 _70582 _70584)). Qed.
Lemma lem5475075 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term611 _70582 _70584.
Proof. exact (@lem5475074 _70582 _70584 (@lem5475071 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5475076 (_70582 : int) (_70584 : int) : (term612 _70582 _70584) = (term613 _70582 _70584).
Proof. exact (@lem1982753 (term411 _70582) (real_of_int _70582) (real_of_int _70584) (term399 _70584)). Qed.
Lemma lem5475077 (_70582 : int) : (term548 _70582) = (term549 _70582).
Proof. exact (@lem1982713 term363 (real_of_int _70582)). Qed.
Lemma lem5475079 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475080 : term331 = term389.
Proof. exact (@lem5475079 term332). Qed.
Lemma lem5475082 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5475083 : term363 = term364.
Proof. exact (@lem5475082 term332). Qed.
Lemma lem5475084 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475085 : term550 = term551.
Proof. exact (MK_COMB (@lem5475084) (@lem5475083)). Qed.
Lemma lem5475086 : term552 = term553.
Proof. exact (MK_COMB (@lem5475085) (@lem5475080)). Qed.
Lemma lem5475087 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5475089 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475090 : term513 = term519.
Proof. exact (@lem5475089 (NUMERAL 0) term332). Qed.
Lemma lem5475091 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475092 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475093 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475092 h1) (fun h1 : term519 = True => @lem5475091)). Qed.
Lemma lem5475094 : term519 = True.
Proof. exact (EQ_MP (@lem5475093) (@lem5475091)). Qed.
Lemma lem5475095 : term513 = True.
Proof. exact (TRANS (@lem5475090) (@lem5475094)). Qed.
Lemma lem5475096 : True = term513.
Proof. exact (SYM (@lem5475095)). Qed.
Lemma lem5475097 : term513.
Proof. exact (EQ_MP (@lem5475096) (@lem0)). Qed.
Lemma lem5475098 : term555.
Proof. exact (@lem5475087 (@lem5475097)). Qed.
Lemma lem5475100 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475101 : term513 = term519.
Proof. exact (@lem5475100 (NUMERAL 0) term332). Qed.
Lemma lem5475102 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475103 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475104 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475103 h1) (fun h1 : term519 = True => @lem5475102)). Qed.
Lemma lem5475105 : term519 = True.
Proof. exact (EQ_MP (@lem5475104) (@lem5475102)). Qed.
Lemma lem5475106 : term513 = True.
Proof. exact (TRANS (@lem5475101) (@lem5475105)). Qed.
Lemma lem5475107 : True = term513.
Proof. exact (SYM (@lem5475106)). Qed.
Lemma lem5475108 : term513.
Proof. exact (EQ_MP (@lem5475107) (@lem0)). Qed.
Lemma lem5475109 : term556.
Proof. exact (@lem5475098 (@lem5475108)). Qed.
Lemma lem5475111 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475112 : term513 = term519.
Proof. exact (@lem5475111 (NUMERAL 0) term332). Qed.
Lemma lem5475113 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475114 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475115 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475114 h1) (fun h1 : term519 = True => @lem5475113)). Qed.
Lemma lem5475116 : term519 = True.
Proof. exact (EQ_MP (@lem5475115) (@lem5475113)). Qed.
Lemma lem5475117 : term513 = True.
Proof. exact (TRANS (@lem5475112) (@lem5475116)). Qed.
Lemma lem5475118 : True = term513.
Proof. exact (SYM (@lem5475117)). Qed.
Lemma lem5475119 : term513.
Proof. exact (EQ_MP (@lem5475118) (@lem0)). Qed.
Lemma lem5475120 : term557.
Proof. exact (@lem5475109 (@lem5475119)). Qed.
Lemma lem5475122 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475123 : term372 = term373.
Proof. exact (@lem5475122 term332 term332). Qed.
Lemma lem5475124 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475125 : term375 = term332.
Proof. exact (EQ_MP (@lem5475124) (@lem940073)). Qed.
Lemma lem5475126 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475127 : term373 = term331.
Proof. exact (MK_COMB (@lem5475126) (@lem5475125)). Qed.
Lemma lem5475128 : term372 = term331.
Proof. exact (TRANS (@lem5475123) (@lem5475127)). Qed.
Lemma lem5475130 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5475131 : term390 = term395.
Proof. exact (@lem5475130 term332 term332). Qed.
Lemma lem5475132 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475133 : term375 = term332.
Proof. exact (EQ_MP (@lem5475132) (@lem940073)). Qed.
Lemma lem5475134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475135 : term373 = term331.
Proof. exact (MK_COMB (@lem5475134) (@lem5475133)). Qed.
Lemma lem5475136 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5475137 : term395 = term363.
Proof. exact (MK_COMB (@lem5475136) (@lem5475135)). Qed.
Lemma lem5475138 : term390 = term363.
Proof. exact (TRANS (@lem5475131) (@lem5475137)). Qed.
Lemma lem5475139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475140 : term558 = term550.
Proof. exact (MK_COMB (@lem5475139) (@lem5475138)). Qed.
Lemma lem5475141 : term559 = term552.
Proof. exact (MK_COMB (@lem5475140) (@lem5475128)). Qed.
Lemma lem5475143 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5475144 : term552 = term318.
Proof. exact (@lem5475143 term332). Qed.
Lemma lem5475145 : term559 = term318.
Proof. exact (TRANS (@lem5475141) (@lem5475144)). Qed.
Lemma lem5475146 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475147 : term561 = term562.
Proof. exact (MK_COMB (@lem5475146) (@lem5475145)). Qed.
Lemma lem5475148 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5475149 : term563 = term524.
Proof. exact (MK_COMB (@lem5475147) (@lem5475148)). Qed.
Lemma lem5475151 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475152 : term524 = term318.
Proof. exact (@lem5475151 term332). Qed.
Lemma lem5475153 : term563 = term318.
Proof. exact (TRANS (@lem5475149) (@lem5475152)). Qed.
Lemma lem5475155 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475156 : term372 = term373.
Proof. exact (@lem5475155 term332 term332). Qed.
Lemma lem5475157 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475158 : term375 = term332.
Proof. exact (EQ_MP (@lem5475157) (@lem940073)). Qed.
Lemma lem5475159 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475160 : term373 = term331.
Proof. exact (MK_COMB (@lem5475159) (@lem5475158)). Qed.
Lemma lem5475161 : term372 = term331.
Proof. exact (TRANS (@lem5475156) (@lem5475160)). Qed.
Lemma lem5475162 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5475163 : term564 = term524.
Proof. exact (MK_COMB (@lem5475162) (@lem5475161)). Qed.
Lemma lem5475165 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475166 : term524 = term318.
Proof. exact (@lem5475165 term332). Qed.
Lemma lem5475167 : term564 = term318.
Proof. exact (TRANS (@lem5475163) (@lem5475166)). Qed.
Lemma lem5475168 : term318 = term564.
Proof. exact (SYM (@lem5475167)). Qed.
Lemma lem5475169 : term563 = term564.
Proof. exact (TRANS (@lem5475153) (@lem5475168)). Qed.
Lemma lem5475170 : term553 = term360.
Proof. exact (@lem5475120 (@lem5475169)). Qed.
Lemma lem5475171 : term552 = term360.
Proof. exact (TRANS (@lem5475086) (@lem5475170)). Qed.
Lemma lem5475173 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5475174 : term360 = term318.
Proof. exact (@lem5475173 term318). Qed.
Lemma lem5475175 : term552 = term318.
Proof. exact (TRANS (@lem5475171) (@lem5475174)). Qed.
Lemma lem5475176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475177 : term565 = term562.
Proof. exact (MK_COMB (@lem5475176) (@lem5475175)). Qed.
Lemma lem5475178 (_70582 : int) : (real_of_int _70582) = (real_of_int _70582).
Proof. exact (eq_refl (real_of_int _70582)). Qed.
Lemma lem5475179 (_70582 : int) : (term549 _70582) = (term566 _70582).
Proof. exact (MK_COMB (@lem5475177) (@lem5475178 _70582)). Qed.
Lemma lem5475180 (_70582 : int) : (term548 _70582) = (term566 _70582).
Proof. exact (TRANS (@lem5475077 _70582) (@lem5475179 _70582)). Qed.
Lemma lem5475181 (_70582 : int) : (term566 _70582) = term318.
Proof. exact (@lem1982719 (real_of_int _70582)). Qed.
Lemma lem5475182 (_70582 : int) : (term548 _70582) = term318.
Proof. exact (TRANS (@lem5475180 _70582) (@lem5475181 _70582)). Qed.
Lemma lem5475183 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475184 (_70582 : int) : (term567 _70582) = term568.
Proof. exact (MK_COMB (@lem5475183) (@lem5475182 _70582)). Qed.
Lemma lem5475185 (_70584 : int) : (term614 _70584) = (term583 _70584).
Proof. exact (@lem1982763 (real_of_int _70584) (term411 _70584) term363). Qed.
Lemma lem5475186 (_70584 : int) : (term584 _70584) = (term549 _70584).
Proof. exact (@lem1982715 term363 (real_of_int _70584)). Qed.
Lemma lem5475188 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475189 : term331 = term389.
Proof. exact (@lem5475188 term332). Qed.
Lemma lem5475191 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5475192 : term363 = term364.
Proof. exact (@lem5475191 term332). Qed.
Lemma lem5475193 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475194 : term550 = term551.
Proof. exact (MK_COMB (@lem5475193) (@lem5475192)). Qed.
Lemma lem5475195 : term552 = term553.
Proof. exact (MK_COMB (@lem5475194) (@lem5475189)). Qed.
Lemma lem5475196 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5475198 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475199 : term513 = term519.
Proof. exact (@lem5475198 (NUMERAL 0) term332). Qed.
Lemma lem5475200 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475201 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475202 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475201 h1) (fun h1 : term519 = True => @lem5475200)). Qed.
Lemma lem5475203 : term519 = True.
Proof. exact (EQ_MP (@lem5475202) (@lem5475200)). Qed.
Lemma lem5475204 : term513 = True.
Proof. exact (TRANS (@lem5475199) (@lem5475203)). Qed.
Lemma lem5475205 : True = term513.
Proof. exact (SYM (@lem5475204)). Qed.
Lemma lem5475206 : term513.
Proof. exact (EQ_MP (@lem5475205) (@lem0)). Qed.
Lemma lem5475207 : term555.
Proof. exact (@lem5475196 (@lem5475206)). Qed.
Lemma lem5475209 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475210 : term513 = term519.
Proof. exact (@lem5475209 (NUMERAL 0) term332). Qed.
Lemma lem5475211 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475212 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475213 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475212 h1) (fun h1 : term519 = True => @lem5475211)). Qed.
Lemma lem5475214 : term519 = True.
Proof. exact (EQ_MP (@lem5475213) (@lem5475211)). Qed.
Lemma lem5475215 : term513 = True.
Proof. exact (TRANS (@lem5475210) (@lem5475214)). Qed.
Lemma lem5475216 : True = term513.
Proof. exact (SYM (@lem5475215)). Qed.
Lemma lem5475217 : term513.
Proof. exact (EQ_MP (@lem5475216) (@lem0)). Qed.
Lemma lem5475218 : term556.
Proof. exact (@lem5475207 (@lem5475217)). Qed.
Lemma lem5475220 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475221 : term513 = term519.
Proof. exact (@lem5475220 (NUMERAL 0) term332). Qed.
Lemma lem5475222 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475223 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475224 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475223 h1) (fun h1 : term519 = True => @lem5475222)). Qed.
Lemma lem5475225 : term519 = True.
Proof. exact (EQ_MP (@lem5475224) (@lem5475222)). Qed.
Lemma lem5475226 : term513 = True.
Proof. exact (TRANS (@lem5475221) (@lem5475225)). Qed.
Lemma lem5475227 : True = term513.
Proof. exact (SYM (@lem5475226)). Qed.
Lemma lem5475228 : term513.
Proof. exact (EQ_MP (@lem5475227) (@lem0)). Qed.
Lemma lem5475229 : term557.
Proof. exact (@lem5475218 (@lem5475228)). Qed.
Lemma lem5475231 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475232 : term372 = term373.
Proof. exact (@lem5475231 term332 term332). Qed.
Lemma lem5475233 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475234 : term375 = term332.
Proof. exact (EQ_MP (@lem5475233) (@lem940073)). Qed.
Lemma lem5475235 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475236 : term373 = term331.
Proof. exact (MK_COMB (@lem5475235) (@lem5475234)). Qed.
Lemma lem5475237 : term372 = term331.
Proof. exact (TRANS (@lem5475232) (@lem5475236)). Qed.
Lemma lem5475239 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5475240 : term390 = term395.
Proof. exact (@lem5475239 term332 term332). Qed.
Lemma lem5475241 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475242 : term375 = term332.
Proof. exact (EQ_MP (@lem5475241) (@lem940073)). Qed.
Lemma lem5475243 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475244 : term373 = term331.
Proof. exact (MK_COMB (@lem5475243) (@lem5475242)). Qed.
Lemma lem5475245 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5475246 : term395 = term363.
Proof. exact (MK_COMB (@lem5475245) (@lem5475244)). Qed.
Lemma lem5475247 : term390 = term363.
Proof. exact (TRANS (@lem5475240) (@lem5475246)). Qed.
Lemma lem5475248 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475249 : term558 = term550.
Proof. exact (MK_COMB (@lem5475248) (@lem5475247)). Qed.
Lemma lem5475250 : term559 = term552.
Proof. exact (MK_COMB (@lem5475249) (@lem5475237)). Qed.
Lemma lem5475252 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5475253 : term552 = term318.
Proof. exact (@lem5475252 term332). Qed.
Lemma lem5475254 : term559 = term318.
Proof. exact (TRANS (@lem5475250) (@lem5475253)). Qed.
Lemma lem5475255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475256 : term561 = term562.
Proof. exact (MK_COMB (@lem5475255) (@lem5475254)). Qed.
Lemma lem5475257 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5475258 : term563 = term524.
Proof. exact (MK_COMB (@lem5475256) (@lem5475257)). Qed.
Lemma lem5475260 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475261 : term524 = term318.
Proof. exact (@lem5475260 term332). Qed.
Lemma lem5475262 : term563 = term318.
Proof. exact (TRANS (@lem5475258) (@lem5475261)). Qed.
Lemma lem5475264 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475265 : term372 = term373.
Proof. exact (@lem5475264 term332 term332). Qed.
Lemma lem5475266 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475267 : term375 = term332.
Proof. exact (EQ_MP (@lem5475266) (@lem940073)). Qed.
Lemma lem5475268 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475269 : term373 = term331.
Proof. exact (MK_COMB (@lem5475268) (@lem5475267)). Qed.
Lemma lem5475270 : term372 = term331.
Proof. exact (TRANS (@lem5475265) (@lem5475269)). Qed.
Lemma lem5475271 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5475272 : term564 = term524.
Proof. exact (MK_COMB (@lem5475271) (@lem5475270)). Qed.
Lemma lem5475274 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475275 : term524 = term318.
Proof. exact (@lem5475274 term332). Qed.
Lemma lem5475276 : term564 = term318.
Proof. exact (TRANS (@lem5475272) (@lem5475275)). Qed.
Lemma lem5475277 : term318 = term564.
Proof. exact (SYM (@lem5475276)). Qed.
Lemma lem5475278 : term563 = term564.
Proof. exact (TRANS (@lem5475262) (@lem5475277)). Qed.
Lemma lem5475279 : term553 = term360.
Proof. exact (@lem5475229 (@lem5475278)). Qed.
Lemma lem5475280 : term552 = term360.
Proof. exact (TRANS (@lem5475195) (@lem5475279)). Qed.
Lemma lem5475282 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5475283 : term360 = term318.
Proof. exact (@lem5475282 term318). Qed.
Lemma lem5475284 : term552 = term318.
Proof. exact (TRANS (@lem5475280) (@lem5475283)). Qed.
Lemma lem5475285 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475286 : term565 = term562.
Proof. exact (MK_COMB (@lem5475285) (@lem5475284)). Qed.
Lemma lem5475287 (_70584 : int) : (real_of_int _70584) = (real_of_int _70584).
Proof. exact (eq_refl (real_of_int _70584)). Qed.
Lemma lem5475288 (_70584 : int) : (term549 _70584) = (term566 _70584).
Proof. exact (MK_COMB (@lem5475286) (@lem5475287 _70584)). Qed.
Lemma lem5475289 (_70584 : int) : (term584 _70584) = (term566 _70584).
Proof. exact (TRANS (@lem5475186 _70584) (@lem5475288 _70584)). Qed.
Lemma lem5475290 (_70584 : int) : (term566 _70584) = term318.
Proof. exact (@lem1982719 (real_of_int _70584)). Qed.
Lemma lem5475291 (_70584 : int) : (term584 _70584) = term318.
Proof. exact (TRANS (@lem5475289 _70584) (@lem5475290 _70584)). Qed.
Lemma lem5475292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475293 (_70584 : int) : (term585 _70584) = term568.
Proof. exact (MK_COMB (@lem5475292) (@lem5475291 _70584)). Qed.
Lemma lem5475294 : term363 = term363.
Proof. exact (eq_refl term363). Qed.
Lemma lem5475295 (_70584 : int) : (term583 _70584) = term586.
Proof. exact (MK_COMB (@lem5475293 _70584) (@lem5475294)). Qed.
Lemma lem5475296 (_70584 : int) : (term614 _70584) = term586.
Proof. exact (TRANS (@lem5475185 _70584) (@lem5475295 _70584)). Qed.
Lemma lem5475297 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5475298 (_70584 : int) : (term614 _70584) = term363.
Proof. exact (TRANS (@lem5475296 _70584) (@lem5475297)). Qed.
Lemma lem5475299 (_70582 : int) (_70584 : int) : (term613 _70582 _70584) = term586.
Proof. exact (MK_COMB (@lem5475184 _70582) (@lem5475298 _70584)). Qed.
Lemma lem5475300 (_70582 : int) (_70584 : int) : (term612 _70582 _70584) = term586.
Proof. exact (TRANS (@lem5475076 _70582 _70584) (@lem5475299 _70582 _70584)). Qed.
Lemma lem5475301 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5475302 (_70582 : int) (_70584 : int) : (term612 _70582 _70584) = term363.
Proof. exact (TRANS (@lem5475300 _70582 _70584) (@lem5475301)). Qed.
Lemma lem5475303 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5475304 (_70582 : int) (_70584 : int) : (term615 _70582 _70584) = term588.
Proof. exact (MK_COMB (@lem5475303) (@lem5475302 _70582 _70584)). Qed.
Lemma lem5475305 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5475306 (_70582 : int) (_70584 : int) : (term611 _70582 _70584) = term589.
Proof. exact (MK_COMB (@lem5475304 _70582 _70584) (@lem5475305)). Qed.
Lemma lem5475307 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : term589.
Proof. exact (EQ_MP (@lem5475306 _70582 _70584) (@lem5475075 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5475309 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5475310 : term589 = term590.
Proof. exact (@lem5475309 term318 term363). Qed.
Lemma lem5475312 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5475313 : term363 = term364.
Proof. exact (@lem5475312 term332). Qed.
Lemma lem5475315 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475316 : term318 = term360.
Proof. exact (@lem5475315 (NUMERAL 0)). Qed.
Lemma lem5475317 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5475318 : term320 = term591.
Proof. exact (MK_COMB (@lem5475317) (@lem5475316)). Qed.
Lemma lem5475319 : term590 = term592.
Proof. exact (MK_COMB (@lem5475318) (@lem5475313)). Qed.
Lemma lem5475320 : term593.
Proof. exact (@lem1980026 term318 term331 term363 term331). Qed.
Lemma lem5475322 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475323 : term513 = term519.
Proof. exact (@lem5475322 (NUMERAL 0) term332). Qed.
Lemma lem5475324 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475325 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475326 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475325 h1) (fun h1 : term519 = True => @lem5475324)). Qed.
Lemma lem5475327 : term519 = True.
Proof. exact (EQ_MP (@lem5475326) (@lem5475324)). Qed.
Lemma lem5475328 : term513 = True.
Proof. exact (TRANS (@lem5475323) (@lem5475327)). Qed.
Lemma lem5475329 : True = term513.
Proof. exact (SYM (@lem5475328)). Qed.
Lemma lem5475330 : term513.
Proof. exact (EQ_MP (@lem5475329) (@lem0)). Qed.
Lemma lem5475331 : term594.
Proof. exact (@lem5475320 (@lem5475330)). Qed.
Lemma lem5475333 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475334 : term513 = term519.
Proof. exact (@lem5475333 (NUMERAL 0) term332). Qed.
Lemma lem5475335 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475336 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475337 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475336 h1) (fun h1 : term519 = True => @lem5475335)). Qed.
Lemma lem5475338 : term519 = True.
Proof. exact (EQ_MP (@lem5475337) (@lem5475335)). Qed.
Lemma lem5475339 : term513 = True.
Proof. exact (TRANS (@lem5475334) (@lem5475338)). Qed.
Lemma lem5475340 : True = term513.
Proof. exact (SYM (@lem5475339)). Qed.
Lemma lem5475341 : term513.
Proof. exact (EQ_MP (@lem5475340) (@lem0)). Qed.
Lemma lem5475342 : term592 = term595.
Proof. exact (@lem5475331 (@lem5475341)). Qed.
Lemma lem5475344 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5475345 : term390 = term395.
Proof. exact (@lem5475344 term332 term332). Qed.
Lemma lem5475346 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475347 : term375 = term332.
Proof. exact (EQ_MP (@lem5475346) (@lem940073)). Qed.
Lemma lem5475348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475349 : term373 = term331.
Proof. exact (MK_COMB (@lem5475348) (@lem5475347)). Qed.
Lemma lem5475350 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5475351 : term395 = term363.
Proof. exact (MK_COMB (@lem5475350) (@lem5475349)). Qed.
Lemma lem5475352 : term390 = term363.
Proof. exact (TRANS (@lem5475345) (@lem5475351)). Qed.
Lemma lem5475354 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475355 : term524 = term318.
Proof. exact (@lem5475354 term332). Qed.
Lemma lem5475356 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5475357 : term596 = term320.
Proof. exact (MK_COMB (@lem5475356) (@lem5475355)). Qed.
Lemma lem5475358 : term595 = term590.
Proof. exact (MK_COMB (@lem5475357) (@lem5475352)). Qed.
Lemma lem5475360 (m : nat) (n : nat) : (term597 m n) = (term598 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5475361 : term590 = term599.
Proof. exact (@lem5475360 (NUMERAL 0) term332). Qed.
Lemma lem5475362 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475363 (h1 : term520 = (BIT1 0)) : (term332 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5475364 : (term520 = (BIT1 0)) = ((term332 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475363 h1) (fun h1 : (term332 = (NUMERAL 0)) = False => @lem5475362)). Qed.
Lemma lem5475365 : (term332 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5475364) (@lem5475362)). Qed.
Lemma lem5475366 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5475367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5475368 : term600 = (and True).
Proof. exact (MK_COMB (@lem5475367) (@lem5475366)). Qed.
Lemma lem5475369 : term599 = (True /\ False).
Proof. exact (MK_COMB (@lem5475368) (@lem5475365)). Qed.
Lemma lem5475371 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5475372 : term599 = False.
Proof. exact (TRANS (@lem5475369) (@lem5475371)). Qed.
Lemma lem5475373 : term590 = False.
Proof. exact (TRANS (@lem5475361) (@lem5475372)). Qed.
Lemma lem5475374 : term595 = False.
Proof. exact (TRANS (@lem5475358) (@lem5475373)). Qed.
Lemma lem5475375 : term592 = False.
Proof. exact (TRANS (@lem5475342) (@lem5475374)). Qed.
Lemma lem5475376 : term590 = False.
Proof. exact (TRANS (@lem5475319) (@lem5475375)). Qed.
Lemma lem5475377 : term589 = False.
Proof. exact (TRANS (@lem5475310) (@lem5475376)). Qed.
Lemma lem5475378 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term601 _70583 _70580 _70581 _70582 _70584) : False.
Proof. exact (EQ_MP (@lem5475377) (@lem5475307 _70583 _70580 _70581 _70582 _70584 h1)). Qed.
Lemma lem5475379 (_70583 : int) (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (h1 : term505 _70583 _70580 _70581 _70582 _70584) : False.
Proof. exact (or_elim (@lem5473882 _70583 _70580 _70581 _70582 _70584 h1) (fun h0 : term511 _70583 _70580 _70581 _70582 _70584 => @lem5474631 _70583 _70580 _70581 _70582 _70584 h0) (fun h0 : term601 _70583 _70580 _70581 _70582 _70584 => @lem5475378 _70583 _70580 _70581 _70582 _70584 h0)). Qed.
Lemma lem5475380 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term501 _70582 _70580 _70581 _70583 _70584) : term501 _70582 _70580 _70581 _70583 _70584.
Proof. exact (h1). Qed.
Lemma lem5475381 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term616 _70582 _70580 _70581 _70583 _70584.
Proof. exact (h1). Qed.
Lemma lem5475382 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term502 _70582 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5475381 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475384 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term489 _70582 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5475382 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475386 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term476 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5475384 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475388 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term463 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5475386 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475390 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term450 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5475388 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475392 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term438 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5475390 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475393 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term403 _70580 _70581.
Proof. exact (proj1 (@lem5475390 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475395 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term419 _70580 _70581 _70584.
Proof. exact (proj1 (@lem5475392 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475396 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term409 _70581 _70584.
Proof. exact (proj2 (@lem5475395 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475397 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term413 _70580 _70584.
Proof. exact (proj1 (@lem5475395 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475399 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5475400 : term512 = term513.
Proof. exact (@lem5475399 term318 term331). Qed.
Lemma lem5475402 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475403 : term331 = term389.
Proof. exact (@lem5475402 term332). Qed.
Lemma lem5475405 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475406 : term318 = term360.
Proof. exact (@lem5475405 (NUMERAL 0)). Qed.
Lemma lem5475407 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475408 : term514 = term515.
Proof. exact (MK_COMB (@lem5475407) (@lem5475406)). Qed.
Lemma lem5475409 : term513 = term516.
Proof. exact (MK_COMB (@lem5475408) (@lem5475403)). Qed.
Lemma lem5475410 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5475412 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475413 : term513 = term519.
Proof. exact (@lem5475412 (NUMERAL 0) term332). Qed.
Lemma lem5475414 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475415 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475416 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475415 h1) (fun h1 : term519 = True => @lem5475414)). Qed.
Lemma lem5475417 : term519 = True.
Proof. exact (EQ_MP (@lem5475416) (@lem5475414)). Qed.
Lemma lem5475418 : term513 = True.
Proof. exact (TRANS (@lem5475413) (@lem5475417)). Qed.
Lemma lem5475419 : True = term513.
Proof. exact (SYM (@lem5475418)). Qed.
Lemma lem5475420 : term513.
Proof. exact (EQ_MP (@lem5475419) (@lem0)). Qed.
Lemma lem5475421 : term521.
Proof. exact (@lem5475410 (@lem5475420)). Qed.
Lemma lem5475423 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475424 : term513 = term519.
Proof. exact (@lem5475423 (NUMERAL 0) term332). Qed.
Lemma lem5475425 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475426 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475427 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475426 h1) (fun h1 : term519 = True => @lem5475425)). Qed.
Lemma lem5475428 : term519 = True.
Proof. exact (EQ_MP (@lem5475427) (@lem5475425)). Qed.
Lemma lem5475429 : term513 = True.
Proof. exact (TRANS (@lem5475424) (@lem5475428)). Qed.
Lemma lem5475430 : True = term513.
Proof. exact (SYM (@lem5475429)). Qed.
Lemma lem5475431 : term513.
Proof. exact (EQ_MP (@lem5475430) (@lem0)). Qed.
Lemma lem5475432 : term516 = term522.
Proof. exact (@lem5475421 (@lem5475431)). Qed.
Lemma lem5475434 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475435 : term372 = term373.
Proof. exact (@lem5475434 term332 term332). Qed.
Lemma lem5475436 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475437 : term375 = term332.
Proof. exact (EQ_MP (@lem5475436) (@lem940073)). Qed.
Lemma lem5475438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475439 : term373 = term331.
Proof. exact (MK_COMB (@lem5475438) (@lem5475437)). Qed.
Lemma lem5475440 : term372 = term331.
Proof. exact (TRANS (@lem5475435) (@lem5475439)). Qed.
Lemma lem5475442 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475443 : term524 = term318.
Proof. exact (@lem5475442 term332). Qed.
Lemma lem5475444 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475445 : term525 = term514.
Proof. exact (MK_COMB (@lem5475444) (@lem5475443)). Qed.
Lemma lem5475446 : term522 = term513.
Proof. exact (MK_COMB (@lem5475445) (@lem5475440)). Qed.
Lemma lem5475448 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475449 : term513 = term519.
Proof. exact (@lem5475448 (NUMERAL 0) term332). Qed.
Lemma lem5475450 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475451 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475452 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475451 h1) (fun h1 : term519 = True => @lem5475450)). Qed.
Lemma lem5475453 : term519 = True.
Proof. exact (EQ_MP (@lem5475452) (@lem5475450)). Qed.
Lemma lem5475454 : term513 = True.
Proof. exact (TRANS (@lem5475449) (@lem5475453)). Qed.
Lemma lem5475455 : term522 = True.
Proof. exact (TRANS (@lem5475446) (@lem5475454)). Qed.
Lemma lem5475456 : term516 = True.
Proof. exact (TRANS (@lem5475432) (@lem5475455)). Qed.
Lemma lem5475457 : term513 = True.
Proof. exact (TRANS (@lem5475409) (@lem5475456)). Qed.
Lemma lem5475458 : term512 = True.
Proof. exact (TRANS (@lem5475400) (@lem5475457)). Qed.
Lemma lem5475459 : True = term512.
Proof. exact (SYM (@lem5475458)). Qed.
Lemma lem5475460 : term512.
Proof. exact (EQ_MP (@lem5475459) (@lem0)). Qed.
Lemma lem5475461 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term526 _70581 _70584.
Proof. exact (conj (@lem5475460) (@lem5475396 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475463 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5475464 (_70581 : int) (_70584 : int) : term528 _70581 _70584.
Proof. exact (@lem5475463 term331 (term406 _70581 _70584)). Qed.
Lemma lem5475465 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term529 _70581 _70584.
Proof. exact (@lem5475464 _70581 _70584 (@lem5475461 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475466 (_70581 : int) (_70584 : int) : (term530 _70581 _70584) = (term406 _70581 _70584).
Proof. exact (@lem1982733 (term406 _70581 _70584)). Qed.
Lemma lem5475467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5475468 (_70581 : int) (_70584 : int) : (term531 _70581 _70584) = (term408 _70581 _70584).
Proof. exact (MK_COMB (@lem5475467) (@lem5475466 _70581 _70584)). Qed.
Lemma lem5475469 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5475470 (_70581 : int) (_70584 : int) : (term529 _70581 _70584) = (term409 _70581 _70584).
Proof. exact (MK_COMB (@lem5475468 _70581 _70584) (@lem5475469)). Qed.
Lemma lem5475471 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term409 _70581 _70584.
Proof. exact (EQ_MP (@lem5475470 _70581 _70584) (@lem5475465 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475473 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5475474 : term512 = term513.
Proof. exact (@lem5475473 term318 term331). Qed.
Lemma lem5475476 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475477 : term331 = term389.
Proof. exact (@lem5475476 term332). Qed.
Lemma lem5475479 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475480 : term318 = term360.
Proof. exact (@lem5475479 (NUMERAL 0)). Qed.
Lemma lem5475481 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475482 : term514 = term515.
Proof. exact (MK_COMB (@lem5475481) (@lem5475480)). Qed.
Lemma lem5475483 : term513 = term516.
Proof. exact (MK_COMB (@lem5475482) (@lem5475477)). Qed.
Lemma lem5475484 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5475486 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475487 : term513 = term519.
Proof. exact (@lem5475486 (NUMERAL 0) term332). Qed.
Lemma lem5475488 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475489 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475490 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475489 h1) (fun h1 : term519 = True => @lem5475488)). Qed.
Lemma lem5475491 : term519 = True.
Proof. exact (EQ_MP (@lem5475490) (@lem5475488)). Qed.
Lemma lem5475492 : term513 = True.
Proof. exact (TRANS (@lem5475487) (@lem5475491)). Qed.
Lemma lem5475493 : True = term513.
Proof. exact (SYM (@lem5475492)). Qed.
Lemma lem5475494 : term513.
Proof. exact (EQ_MP (@lem5475493) (@lem0)). Qed.
Lemma lem5475495 : term521.
Proof. exact (@lem5475484 (@lem5475494)). Qed.
Lemma lem5475497 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475498 : term513 = term519.
Proof. exact (@lem5475497 (NUMERAL 0) term332). Qed.
Lemma lem5475499 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475500 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475501 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475500 h1) (fun h1 : term519 = True => @lem5475499)). Qed.
Lemma lem5475502 : term519 = True.
Proof. exact (EQ_MP (@lem5475501) (@lem5475499)). Qed.
Lemma lem5475503 : term513 = True.
Proof. exact (TRANS (@lem5475498) (@lem5475502)). Qed.
Lemma lem5475504 : True = term513.
Proof. exact (SYM (@lem5475503)). Qed.
Lemma lem5475505 : term513.
Proof. exact (EQ_MP (@lem5475504) (@lem0)). Qed.
Lemma lem5475506 : term516 = term522.
Proof. exact (@lem5475495 (@lem5475505)). Qed.
Lemma lem5475508 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475509 : term372 = term373.
Proof. exact (@lem5475508 term332 term332). Qed.
Lemma lem5475510 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475511 : term375 = term332.
Proof. exact (EQ_MP (@lem5475510) (@lem940073)). Qed.
Lemma lem5475512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475513 : term373 = term331.
Proof. exact (MK_COMB (@lem5475512) (@lem5475511)). Qed.
Lemma lem5475514 : term372 = term331.
Proof. exact (TRANS (@lem5475509) (@lem5475513)). Qed.
Lemma lem5475516 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475517 : term524 = term318.
Proof. exact (@lem5475516 term332). Qed.
Lemma lem5475518 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475519 : term525 = term514.
Proof. exact (MK_COMB (@lem5475518) (@lem5475517)). Qed.
Lemma lem5475520 : term522 = term513.
Proof. exact (MK_COMB (@lem5475519) (@lem5475514)). Qed.
Lemma lem5475522 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475523 : term513 = term519.
Proof. exact (@lem5475522 (NUMERAL 0) term332). Qed.
Lemma lem5475524 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475525 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475526 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475525 h1) (fun h1 : term519 = True => @lem5475524)). Qed.
Lemma lem5475527 : term519 = True.
Proof. exact (EQ_MP (@lem5475526) (@lem5475524)). Qed.
Lemma lem5475528 : term513 = True.
Proof. exact (TRANS (@lem5475523) (@lem5475527)). Qed.
Lemma lem5475529 : term522 = True.
Proof. exact (TRANS (@lem5475520) (@lem5475528)). Qed.
Lemma lem5475530 : term516 = True.
Proof. exact (TRANS (@lem5475506) (@lem5475529)). Qed.
Lemma lem5475531 : term513 = True.
Proof. exact (TRANS (@lem5475483) (@lem5475530)). Qed.
Lemma lem5475532 : term512 = True.
Proof. exact (TRANS (@lem5475474) (@lem5475531)). Qed.
Lemma lem5475533 : True = term512.
Proof. exact (SYM (@lem5475532)). Qed.
Lemma lem5475534 : term512.
Proof. exact (EQ_MP (@lem5475533) (@lem0)). Qed.
Lemma lem5475535 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term532 _70580 _70581.
Proof. exact (conj (@lem5475534) (@lem5475393 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475537 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5475538 (_70580 : int) (_70581 : int) : term533 _70580 _70581.
Proof. exact (@lem5475537 term331 (term400 _70580 _70581)). Qed.
Lemma lem5475539 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term534 _70580 _70581.
Proof. exact (@lem5475538 _70580 _70581 (@lem5475535 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475540 (_70580 : int) (_70581 : int) : (term535 _70580 _70581) = (term400 _70580 _70581).
Proof. exact (@lem1982733 (term400 _70580 _70581)). Qed.
Lemma lem5475541 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5475542 (_70580 : int) (_70581 : int) : (term536 _70580 _70581) = (term402 _70580 _70581).
Proof. exact (MK_COMB (@lem5475541) (@lem5475540 _70580 _70581)). Qed.
Lemma lem5475543 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5475544 (_70580 : int) (_70581 : int) : (term534 _70580 _70581) = (term403 _70580 _70581).
Proof. exact (MK_COMB (@lem5475542 _70580 _70581) (@lem5475543)). Qed.
Lemma lem5475545 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term403 _70580 _70581.
Proof. exact (EQ_MP (@lem5475544 _70580 _70581) (@lem5475539 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475547 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5475548 : term512 = term513.
Proof. exact (@lem5475547 term318 term331). Qed.
Lemma lem5475550 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475551 : term331 = term389.
Proof. exact (@lem5475550 term332). Qed.
Lemma lem5475553 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475554 : term318 = term360.
Proof. exact (@lem5475553 (NUMERAL 0)). Qed.
Lemma lem5475555 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475556 : term514 = term515.
Proof. exact (MK_COMB (@lem5475555) (@lem5475554)). Qed.
Lemma lem5475557 : term513 = term516.
Proof. exact (MK_COMB (@lem5475556) (@lem5475551)). Qed.
Lemma lem5475558 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5475560 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475561 : term513 = term519.
Proof. exact (@lem5475560 (NUMERAL 0) term332). Qed.
Lemma lem5475562 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475563 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475564 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475563 h1) (fun h1 : term519 = True => @lem5475562)). Qed.
Lemma lem5475565 : term519 = True.
Proof. exact (EQ_MP (@lem5475564) (@lem5475562)). Qed.
Lemma lem5475566 : term513 = True.
Proof. exact (TRANS (@lem5475561) (@lem5475565)). Qed.
Lemma lem5475567 : True = term513.
Proof. exact (SYM (@lem5475566)). Qed.
Lemma lem5475568 : term513.
Proof. exact (EQ_MP (@lem5475567) (@lem0)). Qed.
Lemma lem5475569 : term521.
Proof. exact (@lem5475558 (@lem5475568)). Qed.
Lemma lem5475571 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475572 : term513 = term519.
Proof. exact (@lem5475571 (NUMERAL 0) term332). Qed.
Lemma lem5475573 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475574 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475575 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475574 h1) (fun h1 : term519 = True => @lem5475573)). Qed.
Lemma lem5475576 : term519 = True.
Proof. exact (EQ_MP (@lem5475575) (@lem5475573)). Qed.
Lemma lem5475577 : term513 = True.
Proof. exact (TRANS (@lem5475572) (@lem5475576)). Qed.
Lemma lem5475578 : True = term513.
Proof. exact (SYM (@lem5475577)). Qed.
Lemma lem5475579 : term513.
Proof. exact (EQ_MP (@lem5475578) (@lem0)). Qed.
Lemma lem5475580 : term516 = term522.
Proof. exact (@lem5475569 (@lem5475579)). Qed.
Lemma lem5475582 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475583 : term372 = term373.
Proof. exact (@lem5475582 term332 term332). Qed.
Lemma lem5475584 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475585 : term375 = term332.
Proof. exact (EQ_MP (@lem5475584) (@lem940073)). Qed.
Lemma lem5475586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475587 : term373 = term331.
Proof. exact (MK_COMB (@lem5475586) (@lem5475585)). Qed.
Lemma lem5475588 : term372 = term331.
Proof. exact (TRANS (@lem5475583) (@lem5475587)). Qed.
Lemma lem5475590 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475591 : term524 = term318.
Proof. exact (@lem5475590 term332). Qed.
Lemma lem5475592 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475593 : term525 = term514.
Proof. exact (MK_COMB (@lem5475592) (@lem5475591)). Qed.
Lemma lem5475594 : term522 = term513.
Proof. exact (MK_COMB (@lem5475593) (@lem5475588)). Qed.
Lemma lem5475596 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475597 : term513 = term519.
Proof. exact (@lem5475596 (NUMERAL 0) term332). Qed.
Lemma lem5475598 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475599 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475600 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475599 h1) (fun h1 : term519 = True => @lem5475598)). Qed.
Lemma lem5475601 : term519 = True.
Proof. exact (EQ_MP (@lem5475600) (@lem5475598)). Qed.
Lemma lem5475602 : term513 = True.
Proof. exact (TRANS (@lem5475597) (@lem5475601)). Qed.
Lemma lem5475603 : term522 = True.
Proof. exact (TRANS (@lem5475594) (@lem5475602)). Qed.
Lemma lem5475604 : term516 = True.
Proof. exact (TRANS (@lem5475580) (@lem5475603)). Qed.
Lemma lem5475605 : term513 = True.
Proof. exact (TRANS (@lem5475557) (@lem5475604)). Qed.
Lemma lem5475606 : term512 = True.
Proof. exact (TRANS (@lem5475548) (@lem5475605)). Qed.
Lemma lem5475607 : True = term512.
Proof. exact (SYM (@lem5475606)). Qed.
Lemma lem5475608 : term512.
Proof. exact (EQ_MP (@lem5475607) (@lem0)). Qed.
Lemma lem5475609 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term537 _70580 _70584.
Proof. exact (conj (@lem5475608) (@lem5475397 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475611 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5475612 (_70580 : int) (_70584 : int) : term538 _70580 _70584.
Proof. exact (@lem5475611 term331 (term410 _70580 _70584)). Qed.
Lemma lem5475613 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term539 _70580 _70584.
Proof. exact (@lem5475612 _70580 _70584 (@lem5475609 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475614 (_70580 : int) (_70584 : int) : (term540 _70580 _70584) = (term410 _70580 _70584).
Proof. exact (@lem1982733 (term410 _70580 _70584)). Qed.
Lemma lem5475615 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5475616 (_70580 : int) (_70584 : int) : (term541 _70580 _70584) = (term412 _70580 _70584).
Proof. exact (MK_COMB (@lem5475615) (@lem5475614 _70580 _70584)). Qed.
Lemma lem5475617 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5475618 (_70580 : int) (_70584 : int) : (term539 _70580 _70584) = (term413 _70580 _70584).
Proof. exact (MK_COMB (@lem5475616 _70580 _70584) (@lem5475617)). Qed.
Lemma lem5475619 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term413 _70580 _70584.
Proof. exact (EQ_MP (@lem5475618 _70580 _70584) (@lem5475613 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475620 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term542 _70584 _70580 _70581.
Proof. exact (conj (@lem5475619 _70582 _70580 _70581 _70583 _70584 h1) (@lem5475545 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475622 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5475623 (_70584 : int) (_70580 : int) (_70581 : int) : term544 _70584 _70580 _70581.
Proof. exact (@lem5475622 (term410 _70580 _70584) (term400 _70580 _70581)). Qed.
Lemma lem5475624 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term545 _70584 _70580 _70581.
Proof. exact (@lem5475623 _70584 _70580 _70581 (@lem5475620 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475625 (_70580 : int) (_70584 : int) (_70581 : int) : (term546 _70584 _70580 _70581) = (term547 _70580 _70584 _70581).
Proof. exact (@lem1982753 (term411 _70580) (real_of_int _70580) (real_of_int _70584) (term399 _70581)). Qed.
Lemma lem5475626 (_70580 : int) : (term548 _70580) = (term549 _70580).
Proof. exact (@lem1982713 term363 (real_of_int _70580)). Qed.
Lemma lem5475628 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475629 : term331 = term389.
Proof. exact (@lem5475628 term332). Qed.
Lemma lem5475631 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5475632 : term363 = term364.
Proof. exact (@lem5475631 term332). Qed.
Lemma lem5475633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475634 : term550 = term551.
Proof. exact (MK_COMB (@lem5475633) (@lem5475632)). Qed.
Lemma lem5475635 : term552 = term553.
Proof. exact (MK_COMB (@lem5475634) (@lem5475629)). Qed.
Lemma lem5475636 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5475638 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475639 : term513 = term519.
Proof. exact (@lem5475638 (NUMERAL 0) term332). Qed.
Lemma lem5475640 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475641 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475642 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475641 h1) (fun h1 : term519 = True => @lem5475640)). Qed.
Lemma lem5475643 : term519 = True.
Proof. exact (EQ_MP (@lem5475642) (@lem5475640)). Qed.
Lemma lem5475644 : term513 = True.
Proof. exact (TRANS (@lem5475639) (@lem5475643)). Qed.
Lemma lem5475645 : True = term513.
Proof. exact (SYM (@lem5475644)). Qed.
Lemma lem5475646 : term513.
Proof. exact (EQ_MP (@lem5475645) (@lem0)). Qed.
Lemma lem5475647 : term555.
Proof. exact (@lem5475636 (@lem5475646)). Qed.
Lemma lem5475649 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475650 : term513 = term519.
Proof. exact (@lem5475649 (NUMERAL 0) term332). Qed.
Lemma lem5475651 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475652 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475653 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475652 h1) (fun h1 : term519 = True => @lem5475651)). Qed.
Lemma lem5475654 : term519 = True.
Proof. exact (EQ_MP (@lem5475653) (@lem5475651)). Qed.
Lemma lem5475655 : term513 = True.
Proof. exact (TRANS (@lem5475650) (@lem5475654)). Qed.
Lemma lem5475656 : True = term513.
Proof. exact (SYM (@lem5475655)). Qed.
Lemma lem5475657 : term513.
Proof. exact (EQ_MP (@lem5475656) (@lem0)). Qed.
Lemma lem5475658 : term556.
Proof. exact (@lem5475647 (@lem5475657)). Qed.
Lemma lem5475660 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475661 : term513 = term519.
Proof. exact (@lem5475660 (NUMERAL 0) term332). Qed.
Lemma lem5475662 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475663 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475664 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475663 h1) (fun h1 : term519 = True => @lem5475662)). Qed.
Lemma lem5475665 : term519 = True.
Proof. exact (EQ_MP (@lem5475664) (@lem5475662)). Qed.
Lemma lem5475666 : term513 = True.
Proof. exact (TRANS (@lem5475661) (@lem5475665)). Qed.
Lemma lem5475667 : True = term513.
Proof. exact (SYM (@lem5475666)). Qed.
Lemma lem5475668 : term513.
Proof. exact (EQ_MP (@lem5475667) (@lem0)). Qed.
Lemma lem5475669 : term557.
Proof. exact (@lem5475658 (@lem5475668)). Qed.
Lemma lem5475671 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475672 : term372 = term373.
Proof. exact (@lem5475671 term332 term332). Qed.
Lemma lem5475673 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475674 : term375 = term332.
Proof. exact (EQ_MP (@lem5475673) (@lem940073)). Qed.
Lemma lem5475675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475676 : term373 = term331.
Proof. exact (MK_COMB (@lem5475675) (@lem5475674)). Qed.
Lemma lem5475677 : term372 = term331.
Proof. exact (TRANS (@lem5475672) (@lem5475676)). Qed.
Lemma lem5475679 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5475680 : term390 = term395.
Proof. exact (@lem5475679 term332 term332). Qed.
Lemma lem5475681 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475682 : term375 = term332.
Proof. exact (EQ_MP (@lem5475681) (@lem940073)). Qed.
Lemma lem5475683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475684 : term373 = term331.
Proof. exact (MK_COMB (@lem5475683) (@lem5475682)). Qed.
Lemma lem5475685 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5475686 : term395 = term363.
Proof. exact (MK_COMB (@lem5475685) (@lem5475684)). Qed.
Lemma lem5475687 : term390 = term363.
Proof. exact (TRANS (@lem5475680) (@lem5475686)). Qed.
Lemma lem5475688 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475689 : term558 = term550.
Proof. exact (MK_COMB (@lem5475688) (@lem5475687)). Qed.
Lemma lem5475690 : term559 = term552.
Proof. exact (MK_COMB (@lem5475689) (@lem5475677)). Qed.
Lemma lem5475692 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5475693 : term552 = term318.
Proof. exact (@lem5475692 term332). Qed.
Lemma lem5475694 : term559 = term318.
Proof. exact (TRANS (@lem5475690) (@lem5475693)). Qed.
Lemma lem5475695 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475696 : term561 = term562.
Proof. exact (MK_COMB (@lem5475695) (@lem5475694)). Qed.
Lemma lem5475697 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5475698 : term563 = term524.
Proof. exact (MK_COMB (@lem5475696) (@lem5475697)). Qed.
Lemma lem5475700 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475701 : term524 = term318.
Proof. exact (@lem5475700 term332). Qed.
Lemma lem5475702 : term563 = term318.
Proof. exact (TRANS (@lem5475698) (@lem5475701)). Qed.
Lemma lem5475704 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475705 : term372 = term373.
Proof. exact (@lem5475704 term332 term332). Qed.
Lemma lem5475706 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475707 : term375 = term332.
Proof. exact (EQ_MP (@lem5475706) (@lem940073)). Qed.
Lemma lem5475708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475709 : term373 = term331.
Proof. exact (MK_COMB (@lem5475708) (@lem5475707)). Qed.
Lemma lem5475710 : term372 = term331.
Proof. exact (TRANS (@lem5475705) (@lem5475709)). Qed.
Lemma lem5475711 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5475712 : term564 = term524.
Proof. exact (MK_COMB (@lem5475711) (@lem5475710)). Qed.
Lemma lem5475714 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475715 : term524 = term318.
Proof. exact (@lem5475714 term332). Qed.
Lemma lem5475716 : term564 = term318.
Proof. exact (TRANS (@lem5475712) (@lem5475715)). Qed.
Lemma lem5475717 : term318 = term564.
Proof. exact (SYM (@lem5475716)). Qed.
Lemma lem5475718 : term563 = term564.
Proof. exact (TRANS (@lem5475702) (@lem5475717)). Qed.
Lemma lem5475719 : term553 = term360.
Proof. exact (@lem5475669 (@lem5475718)). Qed.
Lemma lem5475720 : term552 = term360.
Proof. exact (TRANS (@lem5475635) (@lem5475719)). Qed.
Lemma lem5475722 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5475723 : term360 = term318.
Proof. exact (@lem5475722 term318). Qed.
Lemma lem5475724 : term552 = term318.
Proof. exact (TRANS (@lem5475720) (@lem5475723)). Qed.
Lemma lem5475725 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475726 : term565 = term562.
Proof. exact (MK_COMB (@lem5475725) (@lem5475724)). Qed.
Lemma lem5475727 (_70580 : int) : (real_of_int _70580) = (real_of_int _70580).
Proof. exact (eq_refl (real_of_int _70580)). Qed.
Lemma lem5475728 (_70580 : int) : (term549 _70580) = (term566 _70580).
Proof. exact (MK_COMB (@lem5475726) (@lem5475727 _70580)). Qed.
Lemma lem5475729 (_70580 : int) : (term548 _70580) = (term566 _70580).
Proof. exact (TRANS (@lem5475626 _70580) (@lem5475728 _70580)). Qed.
Lemma lem5475730 (_70580 : int) : (term566 _70580) = term318.
Proof. exact (@lem1982719 (real_of_int _70580)). Qed.
Lemma lem5475731 (_70580 : int) : (term548 _70580) = term318.
Proof. exact (TRANS (@lem5475729 _70580) (@lem5475730 _70580)). Qed.
Lemma lem5475732 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475733 (_70580 : int) : (term567 _70580) = term568.
Proof. exact (MK_COMB (@lem5475732) (@lem5475731 _70580)). Qed.
Lemma lem5475738 (_70581 : int) (_70584 : int) : (term400 _70584 _70581) = (term420 _70581 _70584).
Proof. exact (@lem1982757 (term411 _70581) (real_of_int _70584) term363). Qed.
Lemma lem5475739 (_70580 : int) (_70581 : int) (_70584 : int) : (term547 _70580 _70584 _70581) = (term569 _70581 _70584).
Proof. exact (MK_COMB (@lem5475733 _70580) (@lem5475738 _70581 _70584)). Qed.
Lemma lem5475740 (_70580 : int) (_70581 : int) (_70584 : int) : (term546 _70584 _70580 _70581) = (term569 _70581 _70584).
Proof. exact (TRANS (@lem5475625 _70580 _70584 _70581) (@lem5475739 _70580 _70581 _70584)). Qed.
Lemma lem5475741 (_70581 : int) (_70584 : int) : (term569 _70581 _70584) = (term420 _70581 _70584).
Proof. exact (@lem1982721 (term420 _70581 _70584)). Qed.
Lemma lem5475742 (_70580 : int) (_70581 : int) (_70584 : int) : (term546 _70584 _70580 _70581) = (term420 _70581 _70584).
Proof. exact (TRANS (@lem5475740 _70580 _70581 _70584) (@lem5475741 _70581 _70584)). Qed.
Lemma lem5475743 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5475744 (_70580 : int) (_70581 : int) (_70584 : int) : (term570 _70584 _70580 _70581) = (term421 _70581 _70584).
Proof. exact (MK_COMB (@lem5475743) (@lem5475742 _70580 _70581 _70584)). Qed.
Lemma lem5475745 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5475746 (_70580 : int) (_70581 : int) (_70584 : int) : (term545 _70584 _70580 _70581) = (term422 _70581 _70584).
Proof. exact (MK_COMB (@lem5475744 _70580 _70581 _70584) (@lem5475745)). Qed.
Lemma lem5475747 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term422 _70581 _70584.
Proof. exact (EQ_MP (@lem5475746 _70580 _70581 _70584) (@lem5475624 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475749 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5475750 : term512 = term513.
Proof. exact (@lem5475749 term318 term331). Qed.
Lemma lem5475752 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475753 : term331 = term389.
Proof. exact (@lem5475752 term332). Qed.
Lemma lem5475755 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475756 : term318 = term360.
Proof. exact (@lem5475755 (NUMERAL 0)). Qed.
Lemma lem5475757 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475758 : term514 = term515.
Proof. exact (MK_COMB (@lem5475757) (@lem5475756)). Qed.
Lemma lem5475759 : term513 = term516.
Proof. exact (MK_COMB (@lem5475758) (@lem5475753)). Qed.
Lemma lem5475760 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5475762 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475763 : term513 = term519.
Proof. exact (@lem5475762 (NUMERAL 0) term332). Qed.
Lemma lem5475764 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475765 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475766 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475765 h1) (fun h1 : term519 = True => @lem5475764)). Qed.
Lemma lem5475767 : term519 = True.
Proof. exact (EQ_MP (@lem5475766) (@lem5475764)). Qed.
Lemma lem5475768 : term513 = True.
Proof. exact (TRANS (@lem5475763) (@lem5475767)). Qed.
Lemma lem5475769 : True = term513.
Proof. exact (SYM (@lem5475768)). Qed.
Lemma lem5475770 : term513.
Proof. exact (EQ_MP (@lem5475769) (@lem0)). Qed.
Lemma lem5475771 : term521.
Proof. exact (@lem5475760 (@lem5475770)). Qed.
Lemma lem5475773 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475774 : term513 = term519.
Proof. exact (@lem5475773 (NUMERAL 0) term332). Qed.
Lemma lem5475775 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475776 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475777 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475776 h1) (fun h1 : term519 = True => @lem5475775)). Qed.
Lemma lem5475778 : term519 = True.
Proof. exact (EQ_MP (@lem5475777) (@lem5475775)). Qed.
Lemma lem5475779 : term513 = True.
Proof. exact (TRANS (@lem5475774) (@lem5475778)). Qed.
Lemma lem5475780 : True = term513.
Proof. exact (SYM (@lem5475779)). Qed.
Lemma lem5475781 : term513.
Proof. exact (EQ_MP (@lem5475780) (@lem0)). Qed.
Lemma lem5475782 : term516 = term522.
Proof. exact (@lem5475771 (@lem5475781)). Qed.
Lemma lem5475784 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475785 : term372 = term373.
Proof. exact (@lem5475784 term332 term332). Qed.
Lemma lem5475786 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475787 : term375 = term332.
Proof. exact (EQ_MP (@lem5475786) (@lem940073)). Qed.
Lemma lem5475788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475789 : term373 = term331.
Proof. exact (MK_COMB (@lem5475788) (@lem5475787)). Qed.
Lemma lem5475790 : term372 = term331.
Proof. exact (TRANS (@lem5475785) (@lem5475789)). Qed.
Lemma lem5475792 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475793 : term524 = term318.
Proof. exact (@lem5475792 term332). Qed.
Lemma lem5475794 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5475795 : term525 = term514.
Proof. exact (MK_COMB (@lem5475794) (@lem5475793)). Qed.
Lemma lem5475796 : term522 = term513.
Proof. exact (MK_COMB (@lem5475795) (@lem5475790)). Qed.
Lemma lem5475798 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475799 : term513 = term519.
Proof. exact (@lem5475798 (NUMERAL 0) term332). Qed.
Lemma lem5475800 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475801 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475802 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475801 h1) (fun h1 : term519 = True => @lem5475800)). Qed.
Lemma lem5475803 : term519 = True.
Proof. exact (EQ_MP (@lem5475802) (@lem5475800)). Qed.
Lemma lem5475804 : term513 = True.
Proof. exact (TRANS (@lem5475799) (@lem5475803)). Qed.
Lemma lem5475805 : term522 = True.
Proof. exact (TRANS (@lem5475796) (@lem5475804)). Qed.
Lemma lem5475806 : term516 = True.
Proof. exact (TRANS (@lem5475782) (@lem5475805)). Qed.
Lemma lem5475807 : term513 = True.
Proof. exact (TRANS (@lem5475759) (@lem5475806)). Qed.
Lemma lem5475808 : term512 = True.
Proof. exact (TRANS (@lem5475750) (@lem5475807)). Qed.
Lemma lem5475809 : True = term512.
Proof. exact (SYM (@lem5475808)). Qed.
Lemma lem5475810 : term512.
Proof. exact (EQ_MP (@lem5475809) (@lem0)). Qed.
Lemma lem5475811 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term571 _70581 _70584.
Proof. exact (conj (@lem5475810) (@lem5475747 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475813 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5475814 (_70581 : int) (_70584 : int) : term572 _70581 _70584.
Proof. exact (@lem5475813 term331 (term420 _70581 _70584)). Qed.
Lemma lem5475815 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term573 _70581 _70584.
Proof. exact (@lem5475814 _70581 _70584 (@lem5475811 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475816 (_70581 : int) (_70584 : int) : (term574 _70581 _70584) = (term420 _70581 _70584).
Proof. exact (@lem1982733 (term420 _70581 _70584)). Qed.
Lemma lem5475817 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5475818 (_70581 : int) (_70584 : int) : (term575 _70581 _70584) = (term421 _70581 _70584).
Proof. exact (MK_COMB (@lem5475817) (@lem5475816 _70581 _70584)). Qed.
Lemma lem5475819 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5475820 (_70581 : int) (_70584 : int) : (term573 _70581 _70584) = (term422 _70581 _70584).
Proof. exact (MK_COMB (@lem5475818 _70581 _70584) (@lem5475819)). Qed.
Lemma lem5475821 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term422 _70581 _70584.
Proof. exact (EQ_MP (@lem5475820 _70581 _70584) (@lem5475815 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475822 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term576 _70581 _70584.
Proof. exact (conj (@lem5475821 _70582 _70580 _70581 _70583 _70584 h1) (@lem5475471 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475824 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5475825 (_70581 : int) (_70584 : int) : term577 _70581 _70584.
Proof. exact (@lem5475824 (term420 _70581 _70584) (term406 _70581 _70584)). Qed.
Lemma lem5475826 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term578 _70581 _70584.
Proof. exact (@lem5475825 _70581 _70584 (@lem5475822 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5475827 (_70581 : int) (_70584 : int) : (term579 _70581 _70584) = (term580 _70581 _70584).
Proof. exact (@lem1982753 (term411 _70581) (real_of_int _70581) (term581 _70584) (term411 _70584)). Qed.
Lemma lem5475828 (_70581 : int) : (term548 _70581) = (term549 _70581).
Proof. exact (@lem1982713 term363 (real_of_int _70581)). Qed.
Lemma lem5475830 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475831 : term331 = term389.
Proof. exact (@lem5475830 term332). Qed.
Lemma lem5475833 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5475834 : term363 = term364.
Proof. exact (@lem5475833 term332). Qed.
Lemma lem5475835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475836 : term550 = term551.
Proof. exact (MK_COMB (@lem5475835) (@lem5475834)). Qed.
Lemma lem5475837 : term552 = term553.
Proof. exact (MK_COMB (@lem5475836) (@lem5475831)). Qed.
Lemma lem5475838 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5475840 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475841 : term513 = term519.
Proof. exact (@lem5475840 (NUMERAL 0) term332). Qed.
Lemma lem5475842 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475843 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475844 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475843 h1) (fun h1 : term519 = True => @lem5475842)). Qed.
Lemma lem5475845 : term519 = True.
Proof. exact (EQ_MP (@lem5475844) (@lem5475842)). Qed.
Lemma lem5475846 : term513 = True.
Proof. exact (TRANS (@lem5475841) (@lem5475845)). Qed.
Lemma lem5475847 : True = term513.
Proof. exact (SYM (@lem5475846)). Qed.
Lemma lem5475848 : term513.
Proof. exact (EQ_MP (@lem5475847) (@lem0)). Qed.
Lemma lem5475849 : term555.
Proof. exact (@lem5475838 (@lem5475848)). Qed.
Lemma lem5475851 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475852 : term513 = term519.
Proof. exact (@lem5475851 (NUMERAL 0) term332). Qed.
Lemma lem5475853 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475854 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475855 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475854 h1) (fun h1 : term519 = True => @lem5475853)). Qed.
Lemma lem5475856 : term519 = True.
Proof. exact (EQ_MP (@lem5475855) (@lem5475853)). Qed.
Lemma lem5475857 : term513 = True.
Proof. exact (TRANS (@lem5475852) (@lem5475856)). Qed.
Lemma lem5475858 : True = term513.
Proof. exact (SYM (@lem5475857)). Qed.
Lemma lem5475859 : term513.
Proof. exact (EQ_MP (@lem5475858) (@lem0)). Qed.
Lemma lem5475860 : term556.
Proof. exact (@lem5475849 (@lem5475859)). Qed.
Lemma lem5475862 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475863 : term513 = term519.
Proof. exact (@lem5475862 (NUMERAL 0) term332). Qed.
Lemma lem5475864 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475865 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475866 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475865 h1) (fun h1 : term519 = True => @lem5475864)). Qed.
Lemma lem5475867 : term519 = True.
Proof. exact (EQ_MP (@lem5475866) (@lem5475864)). Qed.
Lemma lem5475868 : term513 = True.
Proof. exact (TRANS (@lem5475863) (@lem5475867)). Qed.
Lemma lem5475869 : True = term513.
Proof. exact (SYM (@lem5475868)). Qed.
Lemma lem5475870 : term513.
Proof. exact (EQ_MP (@lem5475869) (@lem0)). Qed.
Lemma lem5475871 : term557.
Proof. exact (@lem5475860 (@lem5475870)). Qed.
Lemma lem5475873 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475874 : term372 = term373.
Proof. exact (@lem5475873 term332 term332). Qed.
Lemma lem5475875 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475876 : term375 = term332.
Proof. exact (EQ_MP (@lem5475875) (@lem940073)). Qed.
Lemma lem5475877 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475878 : term373 = term331.
Proof. exact (MK_COMB (@lem5475877) (@lem5475876)). Qed.
Lemma lem5475879 : term372 = term331.
Proof. exact (TRANS (@lem5475874) (@lem5475878)). Qed.
Lemma lem5475881 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5475882 : term390 = term395.
Proof. exact (@lem5475881 term332 term332). Qed.
Lemma lem5475883 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475884 : term375 = term332.
Proof. exact (EQ_MP (@lem5475883) (@lem940073)). Qed.
Lemma lem5475885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475886 : term373 = term331.
Proof. exact (MK_COMB (@lem5475885) (@lem5475884)). Qed.
Lemma lem5475887 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5475888 : term395 = term363.
Proof. exact (MK_COMB (@lem5475887) (@lem5475886)). Qed.
Lemma lem5475889 : term390 = term363.
Proof. exact (TRANS (@lem5475882) (@lem5475888)). Qed.
Lemma lem5475890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475891 : term558 = term550.
Proof. exact (MK_COMB (@lem5475890) (@lem5475889)). Qed.
Lemma lem5475892 : term559 = term552.
Proof. exact (MK_COMB (@lem5475891) (@lem5475879)). Qed.
Lemma lem5475894 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5475895 : term552 = term318.
Proof. exact (@lem5475894 term332). Qed.
Lemma lem5475896 : term559 = term318.
Proof. exact (TRANS (@lem5475892) (@lem5475895)). Qed.
Lemma lem5475897 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475898 : term561 = term562.
Proof. exact (MK_COMB (@lem5475897) (@lem5475896)). Qed.
Lemma lem5475899 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5475900 : term563 = term524.
Proof. exact (MK_COMB (@lem5475898) (@lem5475899)). Qed.
Lemma lem5475902 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475903 : term524 = term318.
Proof. exact (@lem5475902 term332). Qed.
Lemma lem5475904 : term563 = term318.
Proof. exact (TRANS (@lem5475900) (@lem5475903)). Qed.
Lemma lem5475906 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475907 : term372 = term373.
Proof. exact (@lem5475906 term332 term332). Qed.
Lemma lem5475908 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475909 : term375 = term332.
Proof. exact (EQ_MP (@lem5475908) (@lem940073)). Qed.
Lemma lem5475910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475911 : term373 = term331.
Proof. exact (MK_COMB (@lem5475910) (@lem5475909)). Qed.
Lemma lem5475912 : term372 = term331.
Proof. exact (TRANS (@lem5475907) (@lem5475911)). Qed.
Lemma lem5475913 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5475914 : term564 = term524.
Proof. exact (MK_COMB (@lem5475913) (@lem5475912)). Qed.
Lemma lem5475916 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5475917 : term524 = term318.
Proof. exact (@lem5475916 term332). Qed.
Lemma lem5475918 : term564 = term318.
Proof. exact (TRANS (@lem5475914) (@lem5475917)). Qed.
Lemma lem5475919 : term318 = term564.
Proof. exact (SYM (@lem5475918)). Qed.
Lemma lem5475920 : term563 = term564.
Proof. exact (TRANS (@lem5475904) (@lem5475919)). Qed.
Lemma lem5475921 : term553 = term360.
Proof. exact (@lem5475871 (@lem5475920)). Qed.
Lemma lem5475922 : term552 = term360.
Proof. exact (TRANS (@lem5475837) (@lem5475921)). Qed.
Lemma lem5475924 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5475925 : term360 = term318.
Proof. exact (@lem5475924 term318). Qed.
Lemma lem5475926 : term552 = term318.
Proof. exact (TRANS (@lem5475922) (@lem5475925)). Qed.
Lemma lem5475927 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5475928 : term565 = term562.
Proof. exact (MK_COMB (@lem5475927) (@lem5475926)). Qed.
Lemma lem5475929 (_70581 : int) : (real_of_int _70581) = (real_of_int _70581).
Proof. exact (eq_refl (real_of_int _70581)). Qed.
Lemma lem5475930 (_70581 : int) : (term549 _70581) = (term566 _70581).
Proof. exact (MK_COMB (@lem5475928) (@lem5475929 _70581)). Qed.
Lemma lem5475931 (_70581 : int) : (term548 _70581) = (term566 _70581).
Proof. exact (TRANS (@lem5475828 _70581) (@lem5475930 _70581)). Qed.
Lemma lem5475932 (_70581 : int) : (term566 _70581) = term318.
Proof. exact (@lem1982719 (real_of_int _70581)). Qed.
Lemma lem5475933 (_70581 : int) : (term548 _70581) = term318.
Proof. exact (TRANS (@lem5475931 _70581) (@lem5475932 _70581)). Qed.
Lemma lem5475934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475935 (_70581 : int) : (term567 _70581) = term568.
Proof. exact (MK_COMB (@lem5475934) (@lem5475933 _70581)). Qed.
Lemma lem5475936 (_70584 : int) : (term582 _70584) = (term583 _70584).
Proof. exact (@lem1982759 (real_of_int _70584) (term411 _70584) term363). Qed.
Lemma lem5475937 (_70584 : int) : (term584 _70584) = (term549 _70584).
Proof. exact (@lem1982715 term363 (real_of_int _70584)). Qed.
Lemma lem5475939 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5475940 : term331 = term389.
Proof. exact (@lem5475939 term332). Qed.
Lemma lem5475942 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5475943 : term363 = term364.
Proof. exact (@lem5475942 term332). Qed.
Lemma lem5475944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5475945 : term550 = term551.
Proof. exact (MK_COMB (@lem5475944) (@lem5475943)). Qed.
Lemma lem5475946 : term552 = term553.
Proof. exact (MK_COMB (@lem5475945) (@lem5475940)). Qed.
Lemma lem5475947 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5475949 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475950 : term513 = term519.
Proof. exact (@lem5475949 (NUMERAL 0) term332). Qed.
Lemma lem5475951 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475952 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475953 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475952 h1) (fun h1 : term519 = True => @lem5475951)). Qed.
Lemma lem5475954 : term519 = True.
Proof. exact (EQ_MP (@lem5475953) (@lem5475951)). Qed.
Lemma lem5475955 : term513 = True.
Proof. exact (TRANS (@lem5475950) (@lem5475954)). Qed.
Lemma lem5475956 : True = term513.
Proof. exact (SYM (@lem5475955)). Qed.
Lemma lem5475957 : term513.
Proof. exact (EQ_MP (@lem5475956) (@lem0)). Qed.
Lemma lem5475958 : term555.
Proof. exact (@lem5475947 (@lem5475957)). Qed.
Lemma lem5475960 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475961 : term513 = term519.
Proof. exact (@lem5475960 (NUMERAL 0) term332). Qed.
Lemma lem5475962 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475963 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475964 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475963 h1) (fun h1 : term519 = True => @lem5475962)). Qed.
Lemma lem5475965 : term519 = True.
Proof. exact (EQ_MP (@lem5475964) (@lem5475962)). Qed.
Lemma lem5475966 : term513 = True.
Proof. exact (TRANS (@lem5475961) (@lem5475965)). Qed.
Lemma lem5475967 : True = term513.
Proof. exact (SYM (@lem5475966)). Qed.
Lemma lem5475968 : term513.
Proof. exact (EQ_MP (@lem5475967) (@lem0)). Qed.
Lemma lem5475969 : term556.
Proof. exact (@lem5475958 (@lem5475968)). Qed.
Lemma lem5475971 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5475972 : term513 = term519.
Proof. exact (@lem5475971 (NUMERAL 0) term332). Qed.
Lemma lem5475973 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5475974 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5475975 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5475974 h1) (fun h1 : term519 = True => @lem5475973)). Qed.
Lemma lem5475976 : term519 = True.
Proof. exact (EQ_MP (@lem5475975) (@lem5475973)). Qed.
Lemma lem5475977 : term513 = True.
Proof. exact (TRANS (@lem5475972) (@lem5475976)). Qed.
Lemma lem5475978 : True = term513.
Proof. exact (SYM (@lem5475977)). Qed.
Lemma lem5475979 : term513.
Proof. exact (EQ_MP (@lem5475978) (@lem0)). Qed.
Lemma lem5475980 : term557.
Proof. exact (@lem5475969 (@lem5475979)). Qed.
Lemma lem5475982 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5475983 : term372 = term373.
Proof. exact (@lem5475982 term332 term332). Qed.
Lemma lem5475984 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475985 : term375 = term332.
Proof. exact (EQ_MP (@lem5475984) (@lem940073)). Qed.
Lemma lem5475986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475987 : term373 = term331.
Proof. exact (MK_COMB (@lem5475986) (@lem5475985)). Qed.
Lemma lem5475988 : term372 = term331.
Proof. exact (TRANS (@lem5475983) (@lem5475987)). Qed.
Lemma lem5475990 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5475991 : term390 = term395.
Proof. exact (@lem5475990 term332 term332). Qed.
Lemma lem5475992 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5475993 : term375 = term332.
Proof. exact (EQ_MP (@lem5475992) (@lem940073)). Qed.
Lemma lem5475994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5475995 : term373 = term331.
Proof. exact (MK_COMB (@lem5475994) (@lem5475993)). Qed.
Lemma lem5475996 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5475997 : term395 = term363.
Proof. exact (MK_COMB (@lem5475996) (@lem5475995)). Qed.
Lemma lem5475998 : term390 = term363.
Proof. exact (TRANS (@lem5475991) (@lem5475997)). Qed.
Lemma lem5475999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476000 : term558 = term550.
Proof. exact (MK_COMB (@lem5475999) (@lem5475998)). Qed.
Lemma lem5476001 : term559 = term552.
Proof. exact (MK_COMB (@lem5476000) (@lem5475988)). Qed.
Lemma lem5476003 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5476004 : term552 = term318.
Proof. exact (@lem5476003 term332). Qed.
Lemma lem5476005 : term559 = term318.
Proof. exact (TRANS (@lem5476001) (@lem5476004)). Qed.
Lemma lem5476006 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476007 : term561 = term562.
Proof. exact (MK_COMB (@lem5476006) (@lem5476005)). Qed.
Lemma lem5476008 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5476009 : term563 = term524.
Proof. exact (MK_COMB (@lem5476007) (@lem5476008)). Qed.
Lemma lem5476011 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476012 : term524 = term318.
Proof. exact (@lem5476011 term332). Qed.
Lemma lem5476013 : term563 = term318.
Proof. exact (TRANS (@lem5476009) (@lem5476012)). Qed.
Lemma lem5476015 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476016 : term372 = term373.
Proof. exact (@lem5476015 term332 term332). Qed.
Lemma lem5476017 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476018 : term375 = term332.
Proof. exact (EQ_MP (@lem5476017) (@lem940073)). Qed.
Lemma lem5476019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476020 : term373 = term331.
Proof. exact (MK_COMB (@lem5476019) (@lem5476018)). Qed.
Lemma lem5476021 : term372 = term331.
Proof. exact (TRANS (@lem5476016) (@lem5476020)). Qed.
Lemma lem5476022 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5476023 : term564 = term524.
Proof. exact (MK_COMB (@lem5476022) (@lem5476021)). Qed.
Lemma lem5476025 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476026 : term524 = term318.
Proof. exact (@lem5476025 term332). Qed.
Lemma lem5476027 : term564 = term318.
Proof. exact (TRANS (@lem5476023) (@lem5476026)). Qed.
Lemma lem5476028 : term318 = term564.
Proof. exact (SYM (@lem5476027)). Qed.
Lemma lem5476029 : term563 = term564.
Proof. exact (TRANS (@lem5476013) (@lem5476028)). Qed.
Lemma lem5476030 : term553 = term360.
Proof. exact (@lem5475980 (@lem5476029)). Qed.
Lemma lem5476031 : term552 = term360.
Proof. exact (TRANS (@lem5475946) (@lem5476030)). Qed.
Lemma lem5476033 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5476034 : term360 = term318.
Proof. exact (@lem5476033 term318). Qed.
Lemma lem5476035 : term552 = term318.
Proof. exact (TRANS (@lem5476031) (@lem5476034)). Qed.
Lemma lem5476036 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476037 : term565 = term562.
Proof. exact (MK_COMB (@lem5476036) (@lem5476035)). Qed.
Lemma lem5476038 (_70584 : int) : (real_of_int _70584) = (real_of_int _70584).
Proof. exact (eq_refl (real_of_int _70584)). Qed.
Lemma lem5476039 (_70584 : int) : (term549 _70584) = (term566 _70584).
Proof. exact (MK_COMB (@lem5476037) (@lem5476038 _70584)). Qed.
Lemma lem5476040 (_70584 : int) : (term584 _70584) = (term566 _70584).
Proof. exact (TRANS (@lem5475937 _70584) (@lem5476039 _70584)). Qed.
Lemma lem5476041 (_70584 : int) : (term566 _70584) = term318.
Proof. exact (@lem1982719 (real_of_int _70584)). Qed.
Lemma lem5476042 (_70584 : int) : (term584 _70584) = term318.
Proof. exact (TRANS (@lem5476040 _70584) (@lem5476041 _70584)). Qed.
Lemma lem5476043 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476044 (_70584 : int) : (term585 _70584) = term568.
Proof. exact (MK_COMB (@lem5476043) (@lem5476042 _70584)). Qed.
Lemma lem5476045 : term363 = term363.
Proof. exact (eq_refl term363). Qed.
Lemma lem5476046 (_70584 : int) : (term583 _70584) = term586.
Proof. exact (MK_COMB (@lem5476044 _70584) (@lem5476045)). Qed.
Lemma lem5476047 (_70584 : int) : (term582 _70584) = term586.
Proof. exact (TRANS (@lem5475936 _70584) (@lem5476046 _70584)). Qed.
Lemma lem5476048 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5476049 (_70584 : int) : (term582 _70584) = term363.
Proof. exact (TRANS (@lem5476047 _70584) (@lem5476048)). Qed.
Lemma lem5476050 (_70581 : int) (_70584 : int) : (term580 _70581 _70584) = term586.
Proof. exact (MK_COMB (@lem5475935 _70581) (@lem5476049 _70584)). Qed.
Lemma lem5476051 (_70581 : int) (_70584 : int) : (term579 _70581 _70584) = term586.
Proof. exact (TRANS (@lem5475827 _70581 _70584) (@lem5476050 _70581 _70584)). Qed.
Lemma lem5476052 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5476053 (_70581 : int) (_70584 : int) : (term579 _70581 _70584) = term363.
Proof. exact (TRANS (@lem5476051 _70581 _70584) (@lem5476052)). Qed.
Lemma lem5476054 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5476055 (_70581 : int) (_70584 : int) : (term587 _70581 _70584) = term588.
Proof. exact (MK_COMB (@lem5476054) (@lem5476053 _70581 _70584)). Qed.
Lemma lem5476056 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5476057 (_70581 : int) (_70584 : int) : (term578 _70581 _70584) = term589.
Proof. exact (MK_COMB (@lem5476055 _70581 _70584) (@lem5476056)). Qed.
Lemma lem5476058 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : term589.
Proof. exact (EQ_MP (@lem5476057 _70581 _70584) (@lem5475826 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476060 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5476061 : term589 = term590.
Proof. exact (@lem5476060 term318 term363). Qed.
Lemma lem5476063 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5476064 : term363 = term364.
Proof. exact (@lem5476063 term332). Qed.
Lemma lem5476066 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476067 : term318 = term360.
Proof. exact (@lem5476066 (NUMERAL 0)). Qed.
Lemma lem5476068 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5476069 : term320 = term591.
Proof. exact (MK_COMB (@lem5476068) (@lem5476067)). Qed.
Lemma lem5476070 : term590 = term592.
Proof. exact (MK_COMB (@lem5476069) (@lem5476064)). Qed.
Lemma lem5476071 : term593.
Proof. exact (@lem1980026 term318 term331 term363 term331). Qed.
Lemma lem5476073 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476074 : term513 = term519.
Proof. exact (@lem5476073 (NUMERAL 0) term332). Qed.
Lemma lem5476075 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476076 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476077 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476076 h1) (fun h1 : term519 = True => @lem5476075)). Qed.
Lemma lem5476078 : term519 = True.
Proof. exact (EQ_MP (@lem5476077) (@lem5476075)). Qed.
Lemma lem5476079 : term513 = True.
Proof. exact (TRANS (@lem5476074) (@lem5476078)). Qed.
Lemma lem5476080 : True = term513.
Proof. exact (SYM (@lem5476079)). Qed.
Lemma lem5476081 : term513.
Proof. exact (EQ_MP (@lem5476080) (@lem0)). Qed.
Lemma lem5476082 : term594.
Proof. exact (@lem5476071 (@lem5476081)). Qed.
Lemma lem5476084 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476085 : term513 = term519.
Proof. exact (@lem5476084 (NUMERAL 0) term332). Qed.
Lemma lem5476086 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476087 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476088 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476087 h1) (fun h1 : term519 = True => @lem5476086)). Qed.
Lemma lem5476089 : term519 = True.
Proof. exact (EQ_MP (@lem5476088) (@lem5476086)). Qed.
Lemma lem5476090 : term513 = True.
Proof. exact (TRANS (@lem5476085) (@lem5476089)). Qed.
Lemma lem5476091 : True = term513.
Proof. exact (SYM (@lem5476090)). Qed.
Lemma lem5476092 : term513.
Proof. exact (EQ_MP (@lem5476091) (@lem0)). Qed.
Lemma lem5476093 : term592 = term595.
Proof. exact (@lem5476082 (@lem5476092)). Qed.
Lemma lem5476095 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5476096 : term390 = term395.
Proof. exact (@lem5476095 term332 term332). Qed.
Lemma lem5476097 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476098 : term375 = term332.
Proof. exact (EQ_MP (@lem5476097) (@lem940073)). Qed.
Lemma lem5476099 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476100 : term373 = term331.
Proof. exact (MK_COMB (@lem5476099) (@lem5476098)). Qed.
Lemma lem5476101 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5476102 : term395 = term363.
Proof. exact (MK_COMB (@lem5476101) (@lem5476100)). Qed.
Lemma lem5476103 : term390 = term363.
Proof. exact (TRANS (@lem5476096) (@lem5476102)). Qed.
Lemma lem5476105 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476106 : term524 = term318.
Proof. exact (@lem5476105 term332). Qed.
Lemma lem5476107 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5476108 : term596 = term320.
Proof. exact (MK_COMB (@lem5476107) (@lem5476106)). Qed.
Lemma lem5476109 : term595 = term590.
Proof. exact (MK_COMB (@lem5476108) (@lem5476103)). Qed.
Lemma lem5476111 (m : nat) (n : nat) : (term597 m n) = (term598 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5476112 : term590 = term599.
Proof. exact (@lem5476111 (NUMERAL 0) term332). Qed.
Lemma lem5476113 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476114 (h1 : term520 = (BIT1 0)) : (term332 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5476115 : (term520 = (BIT1 0)) = ((term332 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476114 h1) (fun h1 : (term332 = (NUMERAL 0)) = False => @lem5476113)). Qed.
Lemma lem5476116 : (term332 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5476115) (@lem5476113)). Qed.
Lemma lem5476117 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5476118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5476119 : term600 = (and True).
Proof. exact (MK_COMB (@lem5476118) (@lem5476117)). Qed.
Lemma lem5476120 : term599 = (True /\ False).
Proof. exact (MK_COMB (@lem5476119) (@lem5476116)). Qed.
Lemma lem5476122 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5476123 : term599 = False.
Proof. exact (TRANS (@lem5476120) (@lem5476122)). Qed.
Lemma lem5476124 : term590 = False.
Proof. exact (TRANS (@lem5476112) (@lem5476123)). Qed.
Lemma lem5476125 : term595 = False.
Proof. exact (TRANS (@lem5476109) (@lem5476124)). Qed.
Lemma lem5476126 : term592 = False.
Proof. exact (TRANS (@lem5476093) (@lem5476125)). Qed.
Lemma lem5476127 : term590 = False.
Proof. exact (TRANS (@lem5476070) (@lem5476126)). Qed.
Lemma lem5476128 : term589 = False.
Proof. exact (TRANS (@lem5476061) (@lem5476127)). Qed.
Lemma lem5476129 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term616 _70582 _70580 _70581 _70583 _70584) : False.
Proof. exact (EQ_MP (@lem5476128) (@lem5476058 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476130 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term617 _70582 _70580 _70581 _70583 _70584.
Proof. exact (h1). Qed.
Lemma lem5476131 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term503 _70582 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5476130 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476133 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term490 _70582 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5476131 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476135 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term477 _70582 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5476133 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476137 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term464 _70582 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5476135 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476139 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term451 _70582 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5476137 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476141 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term438 _70580 _70581 _70583 _70584.
Proof. exact (proj2 (@lem5476139 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476142 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term415 _70580 _70582 _70581 _70583.
Proof. exact (proj1 (@lem5476139 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476143 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term413 _70581 _70583.
Proof. exact (proj2 (@lem5476142 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476145 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term422 _70583 _70584.
Proof. exact (proj2 (@lem5476141 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476146 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term419 _70580 _70581 _70584.
Proof. exact (proj1 (@lem5476141 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476147 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term409 _70581 _70584.
Proof. exact (proj2 (@lem5476146 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476150 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5476151 : term512 = term513.
Proof. exact (@lem5476150 term318 term331). Qed.
Lemma lem5476153 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476154 : term331 = term389.
Proof. exact (@lem5476153 term332). Qed.
Lemma lem5476156 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476157 : term318 = term360.
Proof. exact (@lem5476156 (NUMERAL 0)). Qed.
Lemma lem5476158 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476159 : term514 = term515.
Proof. exact (MK_COMB (@lem5476158) (@lem5476157)). Qed.
Lemma lem5476160 : term513 = term516.
Proof. exact (MK_COMB (@lem5476159) (@lem5476154)). Qed.
Lemma lem5476161 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5476163 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476164 : term513 = term519.
Proof. exact (@lem5476163 (NUMERAL 0) term332). Qed.
Lemma lem5476165 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476166 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476167 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476166 h1) (fun h1 : term519 = True => @lem5476165)). Qed.
Lemma lem5476168 : term519 = True.
Proof. exact (EQ_MP (@lem5476167) (@lem5476165)). Qed.
Lemma lem5476169 : term513 = True.
Proof. exact (TRANS (@lem5476164) (@lem5476168)). Qed.
Lemma lem5476170 : True = term513.
Proof. exact (SYM (@lem5476169)). Qed.
Lemma lem5476171 : term513.
Proof. exact (EQ_MP (@lem5476170) (@lem0)). Qed.
Lemma lem5476172 : term521.
Proof. exact (@lem5476161 (@lem5476171)). Qed.
Lemma lem5476174 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476175 : term513 = term519.
Proof. exact (@lem5476174 (NUMERAL 0) term332). Qed.
Lemma lem5476176 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476177 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476178 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476177 h1) (fun h1 : term519 = True => @lem5476176)). Qed.
Lemma lem5476179 : term519 = True.
Proof. exact (EQ_MP (@lem5476178) (@lem5476176)). Qed.
Lemma lem5476180 : term513 = True.
Proof. exact (TRANS (@lem5476175) (@lem5476179)). Qed.
Lemma lem5476181 : True = term513.
Proof. exact (SYM (@lem5476180)). Qed.
Lemma lem5476182 : term513.
Proof. exact (EQ_MP (@lem5476181) (@lem0)). Qed.
Lemma lem5476183 : term516 = term522.
Proof. exact (@lem5476172 (@lem5476182)). Qed.
Lemma lem5476185 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476186 : term372 = term373.
Proof. exact (@lem5476185 term332 term332). Qed.
Lemma lem5476187 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476188 : term375 = term332.
Proof. exact (EQ_MP (@lem5476187) (@lem940073)). Qed.
Lemma lem5476189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476190 : term373 = term331.
Proof. exact (MK_COMB (@lem5476189) (@lem5476188)). Qed.
Lemma lem5476191 : term372 = term331.
Proof. exact (TRANS (@lem5476186) (@lem5476190)). Qed.
Lemma lem5476193 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476194 : term524 = term318.
Proof. exact (@lem5476193 term332). Qed.
Lemma lem5476195 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476196 : term525 = term514.
Proof. exact (MK_COMB (@lem5476195) (@lem5476194)). Qed.
Lemma lem5476197 : term522 = term513.
Proof. exact (MK_COMB (@lem5476196) (@lem5476191)). Qed.
Lemma lem5476199 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476200 : term513 = term519.
Proof. exact (@lem5476199 (NUMERAL 0) term332). Qed.
Lemma lem5476201 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476202 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476203 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476202 h1) (fun h1 : term519 = True => @lem5476201)). Qed.
Lemma lem5476204 : term519 = True.
Proof. exact (EQ_MP (@lem5476203) (@lem5476201)). Qed.
Lemma lem5476205 : term513 = True.
Proof. exact (TRANS (@lem5476200) (@lem5476204)). Qed.
Lemma lem5476206 : term522 = True.
Proof. exact (TRANS (@lem5476197) (@lem5476205)). Qed.
Lemma lem5476207 : term516 = True.
Proof. exact (TRANS (@lem5476183) (@lem5476206)). Qed.
Lemma lem5476208 : term513 = True.
Proof. exact (TRANS (@lem5476160) (@lem5476207)). Qed.
Lemma lem5476209 : term512 = True.
Proof. exact (TRANS (@lem5476151) (@lem5476208)). Qed.
Lemma lem5476210 : True = term512.
Proof. exact (SYM (@lem5476209)). Qed.
Lemma lem5476211 : term512.
Proof. exact (EQ_MP (@lem5476210) (@lem0)). Qed.
Lemma lem5476212 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term526 _70581 _70584.
Proof. exact (conj (@lem5476211) (@lem5476147 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476214 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5476215 (_70581 : int) (_70584 : int) : term528 _70581 _70584.
Proof. exact (@lem5476214 term331 (term406 _70581 _70584)). Qed.
Lemma lem5476216 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term529 _70581 _70584.
Proof. exact (@lem5476215 _70581 _70584 (@lem5476212 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476217 (_70581 : int) (_70584 : int) : (term530 _70581 _70584) = (term406 _70581 _70584).
Proof. exact (@lem1982733 (term406 _70581 _70584)). Qed.
Lemma lem5476218 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5476219 (_70581 : int) (_70584 : int) : (term531 _70581 _70584) = (term408 _70581 _70584).
Proof. exact (MK_COMB (@lem5476218) (@lem5476217 _70581 _70584)). Qed.
Lemma lem5476220 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5476221 (_70581 : int) (_70584 : int) : (term529 _70581 _70584) = (term409 _70581 _70584).
Proof. exact (MK_COMB (@lem5476219 _70581 _70584) (@lem5476220)). Qed.
Lemma lem5476222 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term409 _70581 _70584.
Proof. exact (EQ_MP (@lem5476221 _70581 _70584) (@lem5476216 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476224 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5476225 : term512 = term513.
Proof. exact (@lem5476224 term318 term331). Qed.
Lemma lem5476227 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476228 : term331 = term389.
Proof. exact (@lem5476227 term332). Qed.
Lemma lem5476230 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476231 : term318 = term360.
Proof. exact (@lem5476230 (NUMERAL 0)). Qed.
Lemma lem5476232 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476233 : term514 = term515.
Proof. exact (MK_COMB (@lem5476232) (@lem5476231)). Qed.
Lemma lem5476234 : term513 = term516.
Proof. exact (MK_COMB (@lem5476233) (@lem5476228)). Qed.
Lemma lem5476235 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5476237 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476238 : term513 = term519.
Proof. exact (@lem5476237 (NUMERAL 0) term332). Qed.
Lemma lem5476239 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476240 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476241 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476240 h1) (fun h1 : term519 = True => @lem5476239)). Qed.
Lemma lem5476242 : term519 = True.
Proof. exact (EQ_MP (@lem5476241) (@lem5476239)). Qed.
Lemma lem5476243 : term513 = True.
Proof. exact (TRANS (@lem5476238) (@lem5476242)). Qed.
Lemma lem5476244 : True = term513.
Proof. exact (SYM (@lem5476243)). Qed.
Lemma lem5476245 : term513.
Proof. exact (EQ_MP (@lem5476244) (@lem0)). Qed.
Lemma lem5476246 : term521.
Proof. exact (@lem5476235 (@lem5476245)). Qed.
Lemma lem5476248 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476249 : term513 = term519.
Proof. exact (@lem5476248 (NUMERAL 0) term332). Qed.
Lemma lem5476250 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476251 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476252 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476251 h1) (fun h1 : term519 = True => @lem5476250)). Qed.
Lemma lem5476253 : term519 = True.
Proof. exact (EQ_MP (@lem5476252) (@lem5476250)). Qed.
Lemma lem5476254 : term513 = True.
Proof. exact (TRANS (@lem5476249) (@lem5476253)). Qed.
Lemma lem5476255 : True = term513.
Proof. exact (SYM (@lem5476254)). Qed.
Lemma lem5476256 : term513.
Proof. exact (EQ_MP (@lem5476255) (@lem0)). Qed.
Lemma lem5476257 : term516 = term522.
Proof. exact (@lem5476246 (@lem5476256)). Qed.
Lemma lem5476259 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476260 : term372 = term373.
Proof. exact (@lem5476259 term332 term332). Qed.
Lemma lem5476261 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476262 : term375 = term332.
Proof. exact (EQ_MP (@lem5476261) (@lem940073)). Qed.
Lemma lem5476263 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476264 : term373 = term331.
Proof. exact (MK_COMB (@lem5476263) (@lem5476262)). Qed.
Lemma lem5476265 : term372 = term331.
Proof. exact (TRANS (@lem5476260) (@lem5476264)). Qed.
Lemma lem5476267 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476268 : term524 = term318.
Proof. exact (@lem5476267 term332). Qed.
Lemma lem5476269 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476270 : term525 = term514.
Proof. exact (MK_COMB (@lem5476269) (@lem5476268)). Qed.
Lemma lem5476271 : term522 = term513.
Proof. exact (MK_COMB (@lem5476270) (@lem5476265)). Qed.
Lemma lem5476273 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476274 : term513 = term519.
Proof. exact (@lem5476273 (NUMERAL 0) term332). Qed.
Lemma lem5476275 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476276 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476277 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476276 h1) (fun h1 : term519 = True => @lem5476275)). Qed.
Lemma lem5476278 : term519 = True.
Proof. exact (EQ_MP (@lem5476277) (@lem5476275)). Qed.
Lemma lem5476279 : term513 = True.
Proof. exact (TRANS (@lem5476274) (@lem5476278)). Qed.
Lemma lem5476280 : term522 = True.
Proof. exact (TRANS (@lem5476271) (@lem5476279)). Qed.
Lemma lem5476281 : term516 = True.
Proof. exact (TRANS (@lem5476257) (@lem5476280)). Qed.
Lemma lem5476282 : term513 = True.
Proof. exact (TRANS (@lem5476234) (@lem5476281)). Qed.
Lemma lem5476283 : term512 = True.
Proof. exact (TRANS (@lem5476225) (@lem5476282)). Qed.
Lemma lem5476284 : True = term512.
Proof. exact (SYM (@lem5476283)). Qed.
Lemma lem5476285 : term512.
Proof. exact (EQ_MP (@lem5476284) (@lem0)). Qed.
Lemma lem5476286 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term537 _70581 _70583.
Proof. exact (conj (@lem5476285) (@lem5476143 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476288 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5476289 (_70581 : int) (_70583 : int) : term538 _70581 _70583.
Proof. exact (@lem5476288 term331 (term410 _70581 _70583)). Qed.
Lemma lem5476290 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term539 _70581 _70583.
Proof. exact (@lem5476289 _70581 _70583 (@lem5476286 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476291 (_70581 : int) (_70583 : int) : (term540 _70581 _70583) = (term410 _70581 _70583).
Proof. exact (@lem1982733 (term410 _70581 _70583)). Qed.
Lemma lem5476292 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5476293 (_70581 : int) (_70583 : int) : (term541 _70581 _70583) = (term412 _70581 _70583).
Proof. exact (MK_COMB (@lem5476292) (@lem5476291 _70581 _70583)). Qed.
Lemma lem5476294 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5476295 (_70581 : int) (_70583 : int) : (term539 _70581 _70583) = (term413 _70581 _70583).
Proof. exact (MK_COMB (@lem5476293 _70581 _70583) (@lem5476294)). Qed.
Lemma lem5476296 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term413 _70581 _70583.
Proof. exact (EQ_MP (@lem5476295 _70581 _70583) (@lem5476290 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476297 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term602 _70583 _70581 _70584.
Proof. exact (conj (@lem5476296 _70582 _70580 _70581 _70583 _70584 h1) (@lem5476222 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476299 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5476300 (_70583 : int) (_70581 : int) (_70584 : int) : term603 _70583 _70581 _70584.
Proof. exact (@lem5476299 (term410 _70581 _70583) (term406 _70581 _70584)). Qed.
Lemma lem5476301 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term604 _70583 _70581 _70584.
Proof. exact (@lem5476300 _70583 _70581 _70584 (@lem5476297 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476302 (_70581 : int) (_70583 : int) (_70584 : int) : (term605 _70583 _70581 _70584) = (term606 _70581 _70583 _70584).
Proof. exact (@lem1982753 (term411 _70581) (real_of_int _70581) (real_of_int _70583) (term411 _70584)). Qed.
Lemma lem5476303 (_70581 : int) : (term548 _70581) = (term549 _70581).
Proof. exact (@lem1982713 term363 (real_of_int _70581)). Qed.
Lemma lem5476305 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476306 : term331 = term389.
Proof. exact (@lem5476305 term332). Qed.
Lemma lem5476308 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5476309 : term363 = term364.
Proof. exact (@lem5476308 term332). Qed.
Lemma lem5476310 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476311 : term550 = term551.
Proof. exact (MK_COMB (@lem5476310) (@lem5476309)). Qed.
Lemma lem5476312 : term552 = term553.
Proof. exact (MK_COMB (@lem5476311) (@lem5476306)). Qed.
Lemma lem5476313 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5476315 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476316 : term513 = term519.
Proof. exact (@lem5476315 (NUMERAL 0) term332). Qed.
Lemma lem5476317 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476318 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476319 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476318 h1) (fun h1 : term519 = True => @lem5476317)). Qed.
Lemma lem5476320 : term519 = True.
Proof. exact (EQ_MP (@lem5476319) (@lem5476317)). Qed.
Lemma lem5476321 : term513 = True.
Proof. exact (TRANS (@lem5476316) (@lem5476320)). Qed.
Lemma lem5476322 : True = term513.
Proof. exact (SYM (@lem5476321)). Qed.
Lemma lem5476323 : term513.
Proof. exact (EQ_MP (@lem5476322) (@lem0)). Qed.
Lemma lem5476324 : term555.
Proof. exact (@lem5476313 (@lem5476323)). Qed.
Lemma lem5476326 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476327 : term513 = term519.
Proof. exact (@lem5476326 (NUMERAL 0) term332). Qed.
Lemma lem5476328 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476329 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476330 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476329 h1) (fun h1 : term519 = True => @lem5476328)). Qed.
Lemma lem5476331 : term519 = True.
Proof. exact (EQ_MP (@lem5476330) (@lem5476328)). Qed.
Lemma lem5476332 : term513 = True.
Proof. exact (TRANS (@lem5476327) (@lem5476331)). Qed.
Lemma lem5476333 : True = term513.
Proof. exact (SYM (@lem5476332)). Qed.
Lemma lem5476334 : term513.
Proof. exact (EQ_MP (@lem5476333) (@lem0)). Qed.
Lemma lem5476335 : term556.
Proof. exact (@lem5476324 (@lem5476334)). Qed.
Lemma lem5476337 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476338 : term513 = term519.
Proof. exact (@lem5476337 (NUMERAL 0) term332). Qed.
Lemma lem5476339 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476340 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476341 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476340 h1) (fun h1 : term519 = True => @lem5476339)). Qed.
Lemma lem5476342 : term519 = True.
Proof. exact (EQ_MP (@lem5476341) (@lem5476339)). Qed.
Lemma lem5476343 : term513 = True.
Proof. exact (TRANS (@lem5476338) (@lem5476342)). Qed.
Lemma lem5476344 : True = term513.
Proof. exact (SYM (@lem5476343)). Qed.
Lemma lem5476345 : term513.
Proof. exact (EQ_MP (@lem5476344) (@lem0)). Qed.
Lemma lem5476346 : term557.
Proof. exact (@lem5476335 (@lem5476345)). Qed.
Lemma lem5476348 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476349 : term372 = term373.
Proof. exact (@lem5476348 term332 term332). Qed.
Lemma lem5476350 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476351 : term375 = term332.
Proof. exact (EQ_MP (@lem5476350) (@lem940073)). Qed.
Lemma lem5476352 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476353 : term373 = term331.
Proof. exact (MK_COMB (@lem5476352) (@lem5476351)). Qed.
Lemma lem5476354 : term372 = term331.
Proof. exact (TRANS (@lem5476349) (@lem5476353)). Qed.
Lemma lem5476356 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5476357 : term390 = term395.
Proof. exact (@lem5476356 term332 term332). Qed.
Lemma lem5476358 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476359 : term375 = term332.
Proof. exact (EQ_MP (@lem5476358) (@lem940073)). Qed.
Lemma lem5476360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476361 : term373 = term331.
Proof. exact (MK_COMB (@lem5476360) (@lem5476359)). Qed.
Lemma lem5476362 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5476363 : term395 = term363.
Proof. exact (MK_COMB (@lem5476362) (@lem5476361)). Qed.
Lemma lem5476364 : term390 = term363.
Proof. exact (TRANS (@lem5476357) (@lem5476363)). Qed.
Lemma lem5476365 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476366 : term558 = term550.
Proof. exact (MK_COMB (@lem5476365) (@lem5476364)). Qed.
Lemma lem5476367 : term559 = term552.
Proof. exact (MK_COMB (@lem5476366) (@lem5476354)). Qed.
Lemma lem5476369 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5476370 : term552 = term318.
Proof. exact (@lem5476369 term332). Qed.
Lemma lem5476371 : term559 = term318.
Proof. exact (TRANS (@lem5476367) (@lem5476370)). Qed.
Lemma lem5476372 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476373 : term561 = term562.
Proof. exact (MK_COMB (@lem5476372) (@lem5476371)). Qed.
Lemma lem5476374 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5476375 : term563 = term524.
Proof. exact (MK_COMB (@lem5476373) (@lem5476374)). Qed.
Lemma lem5476377 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476378 : term524 = term318.
Proof. exact (@lem5476377 term332). Qed.
Lemma lem5476379 : term563 = term318.
Proof. exact (TRANS (@lem5476375) (@lem5476378)). Qed.
Lemma lem5476381 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476382 : term372 = term373.
Proof. exact (@lem5476381 term332 term332). Qed.
Lemma lem5476383 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476384 : term375 = term332.
Proof. exact (EQ_MP (@lem5476383) (@lem940073)). Qed.
Lemma lem5476385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476386 : term373 = term331.
Proof. exact (MK_COMB (@lem5476385) (@lem5476384)). Qed.
Lemma lem5476387 : term372 = term331.
Proof. exact (TRANS (@lem5476382) (@lem5476386)). Qed.
Lemma lem5476388 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5476389 : term564 = term524.
Proof. exact (MK_COMB (@lem5476388) (@lem5476387)). Qed.
Lemma lem5476391 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476392 : term524 = term318.
Proof. exact (@lem5476391 term332). Qed.
Lemma lem5476393 : term564 = term318.
Proof. exact (TRANS (@lem5476389) (@lem5476392)). Qed.
Lemma lem5476394 : term318 = term564.
Proof. exact (SYM (@lem5476393)). Qed.
Lemma lem5476395 : term563 = term564.
Proof. exact (TRANS (@lem5476379) (@lem5476394)). Qed.
Lemma lem5476396 : term553 = term360.
Proof. exact (@lem5476346 (@lem5476395)). Qed.
Lemma lem5476397 : term552 = term360.
Proof. exact (TRANS (@lem5476312) (@lem5476396)). Qed.
Lemma lem5476399 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5476400 : term360 = term318.
Proof. exact (@lem5476399 term318). Qed.
Lemma lem5476401 : term552 = term318.
Proof. exact (TRANS (@lem5476397) (@lem5476400)). Qed.
Lemma lem5476402 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476403 : term565 = term562.
Proof. exact (MK_COMB (@lem5476402) (@lem5476401)). Qed.
Lemma lem5476404 (_70581 : int) : (real_of_int _70581) = (real_of_int _70581).
Proof. exact (eq_refl (real_of_int _70581)). Qed.
Lemma lem5476405 (_70581 : int) : (term549 _70581) = (term566 _70581).
Proof. exact (MK_COMB (@lem5476403) (@lem5476404 _70581)). Qed.
Lemma lem5476406 (_70581 : int) : (term548 _70581) = (term566 _70581).
Proof. exact (TRANS (@lem5476303 _70581) (@lem5476405 _70581)). Qed.
Lemma lem5476407 (_70581 : int) : (term566 _70581) = term318.
Proof. exact (@lem1982719 (real_of_int _70581)). Qed.
Lemma lem5476408 (_70581 : int) : (term548 _70581) = term318.
Proof. exact (TRANS (@lem5476406 _70581) (@lem5476407 _70581)). Qed.
Lemma lem5476409 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476410 (_70581 : int) : (term567 _70581) = term568.
Proof. exact (MK_COMB (@lem5476409) (@lem5476408 _70581)). Qed.
Lemma lem5476411 (_70583 : int) (_70584 : int) : (term406 _70583 _70584) = (term406 _70583 _70584).
Proof. exact (eq_refl (term406 _70583 _70584)). Qed.
Lemma lem5476412 (_70581 : int) (_70583 : int) (_70584 : int) : (term606 _70581 _70583 _70584) = (term618 _70583 _70584).
Proof. exact (MK_COMB (@lem5476410 _70581) (@lem5476411 _70583 _70584)). Qed.
Lemma lem5476413 (_70581 : int) (_70583 : int) (_70584 : int) : (term605 _70583 _70581 _70584) = (term618 _70583 _70584).
Proof. exact (TRANS (@lem5476302 _70581 _70583 _70584) (@lem5476412 _70581 _70583 _70584)). Qed.
Lemma lem5476414 (_70583 : int) (_70584 : int) : (term618 _70583 _70584) = (term406 _70583 _70584).
Proof. exact (@lem1982721 (term406 _70583 _70584)). Qed.
Lemma lem5476415 (_70581 : int) (_70583 : int) (_70584 : int) : (term605 _70583 _70581 _70584) = (term406 _70583 _70584).
Proof. exact (TRANS (@lem5476413 _70581 _70583 _70584) (@lem5476414 _70583 _70584)). Qed.
Lemma lem5476416 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5476417 (_70581 : int) (_70583 : int) (_70584 : int) : (term608 _70583 _70581 _70584) = (term408 _70583 _70584).
Proof. exact (MK_COMB (@lem5476416) (@lem5476415 _70581 _70583 _70584)). Qed.
Lemma lem5476418 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5476419 (_70581 : int) (_70583 : int) (_70584 : int) : (term604 _70583 _70581 _70584) = (term409 _70583 _70584).
Proof. exact (MK_COMB (@lem5476417 _70581 _70583 _70584) (@lem5476418)). Qed.
Lemma lem5476420 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term409 _70583 _70584.
Proof. exact (EQ_MP (@lem5476419 _70581 _70583 _70584) (@lem5476301 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476422 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5476423 : term512 = term513.
Proof. exact (@lem5476422 term318 term331). Qed.
Lemma lem5476425 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476426 : term331 = term389.
Proof. exact (@lem5476425 term332). Qed.
Lemma lem5476428 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476429 : term318 = term360.
Proof. exact (@lem5476428 (NUMERAL 0)). Qed.
Lemma lem5476430 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476431 : term514 = term515.
Proof. exact (MK_COMB (@lem5476430) (@lem5476429)). Qed.
Lemma lem5476432 : term513 = term516.
Proof. exact (MK_COMB (@lem5476431) (@lem5476426)). Qed.
Lemma lem5476433 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5476435 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476436 : term513 = term519.
Proof. exact (@lem5476435 (NUMERAL 0) term332). Qed.
Lemma lem5476437 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476438 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476439 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476438 h1) (fun h1 : term519 = True => @lem5476437)). Qed.
Lemma lem5476440 : term519 = True.
Proof. exact (EQ_MP (@lem5476439) (@lem5476437)). Qed.
Lemma lem5476441 : term513 = True.
Proof. exact (TRANS (@lem5476436) (@lem5476440)). Qed.
Lemma lem5476442 : True = term513.
Proof. exact (SYM (@lem5476441)). Qed.
Lemma lem5476443 : term513.
Proof. exact (EQ_MP (@lem5476442) (@lem0)). Qed.
Lemma lem5476444 : term521.
Proof. exact (@lem5476433 (@lem5476443)). Qed.
Lemma lem5476446 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476447 : term513 = term519.
Proof. exact (@lem5476446 (NUMERAL 0) term332). Qed.
Lemma lem5476448 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476449 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476450 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476449 h1) (fun h1 : term519 = True => @lem5476448)). Qed.
Lemma lem5476451 : term519 = True.
Proof. exact (EQ_MP (@lem5476450) (@lem5476448)). Qed.
Lemma lem5476452 : term513 = True.
Proof. exact (TRANS (@lem5476447) (@lem5476451)). Qed.
Lemma lem5476453 : True = term513.
Proof. exact (SYM (@lem5476452)). Qed.
Lemma lem5476454 : term513.
Proof. exact (EQ_MP (@lem5476453) (@lem0)). Qed.
Lemma lem5476455 : term516 = term522.
Proof. exact (@lem5476444 (@lem5476454)). Qed.
Lemma lem5476457 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476458 : term372 = term373.
Proof. exact (@lem5476457 term332 term332). Qed.
Lemma lem5476459 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476460 : term375 = term332.
Proof. exact (EQ_MP (@lem5476459) (@lem940073)). Qed.
Lemma lem5476461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476462 : term373 = term331.
Proof. exact (MK_COMB (@lem5476461) (@lem5476460)). Qed.
Lemma lem5476463 : term372 = term331.
Proof. exact (TRANS (@lem5476458) (@lem5476462)). Qed.
Lemma lem5476465 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476466 : term524 = term318.
Proof. exact (@lem5476465 term332). Qed.
Lemma lem5476467 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476468 : term525 = term514.
Proof. exact (MK_COMB (@lem5476467) (@lem5476466)). Qed.
Lemma lem5476469 : term522 = term513.
Proof. exact (MK_COMB (@lem5476468) (@lem5476463)). Qed.
Lemma lem5476471 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476472 : term513 = term519.
Proof. exact (@lem5476471 (NUMERAL 0) term332). Qed.
Lemma lem5476473 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476474 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476475 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476474 h1) (fun h1 : term519 = True => @lem5476473)). Qed.
Lemma lem5476476 : term519 = True.
Proof. exact (EQ_MP (@lem5476475) (@lem5476473)). Qed.
Lemma lem5476477 : term513 = True.
Proof. exact (TRANS (@lem5476472) (@lem5476476)). Qed.
Lemma lem5476478 : term522 = True.
Proof. exact (TRANS (@lem5476469) (@lem5476477)). Qed.
Lemma lem5476479 : term516 = True.
Proof. exact (TRANS (@lem5476455) (@lem5476478)). Qed.
Lemma lem5476480 : term513 = True.
Proof. exact (TRANS (@lem5476432) (@lem5476479)). Qed.
Lemma lem5476481 : term512 = True.
Proof. exact (TRANS (@lem5476423) (@lem5476480)). Qed.
Lemma lem5476482 : True = term512.
Proof. exact (SYM (@lem5476481)). Qed.
Lemma lem5476483 : term512.
Proof. exact (EQ_MP (@lem5476482) (@lem0)). Qed.
Lemma lem5476484 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term526 _70583 _70584.
Proof. exact (conj (@lem5476483) (@lem5476420 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476486 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5476487 (_70583 : int) (_70584 : int) : term528 _70583 _70584.
Proof. exact (@lem5476486 term331 (term406 _70583 _70584)). Qed.
Lemma lem5476488 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term529 _70583 _70584.
Proof. exact (@lem5476487 _70583 _70584 (@lem5476484 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476489 (_70583 : int) (_70584 : int) : (term530 _70583 _70584) = (term406 _70583 _70584).
Proof. exact (@lem1982733 (term406 _70583 _70584)). Qed.
Lemma lem5476490 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5476491 (_70583 : int) (_70584 : int) : (term531 _70583 _70584) = (term408 _70583 _70584).
Proof. exact (MK_COMB (@lem5476490) (@lem5476489 _70583 _70584)). Qed.
Lemma lem5476492 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5476493 (_70583 : int) (_70584 : int) : (term529 _70583 _70584) = (term409 _70583 _70584).
Proof. exact (MK_COMB (@lem5476491 _70583 _70584) (@lem5476492)). Qed.
Lemma lem5476494 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term409 _70583 _70584.
Proof. exact (EQ_MP (@lem5476493 _70583 _70584) (@lem5476488 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476496 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5476497 : term512 = term513.
Proof. exact (@lem5476496 term318 term331). Qed.
Lemma lem5476499 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476500 : term331 = term389.
Proof. exact (@lem5476499 term332). Qed.
Lemma lem5476502 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476503 : term318 = term360.
Proof. exact (@lem5476502 (NUMERAL 0)). Qed.
Lemma lem5476504 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476505 : term514 = term515.
Proof. exact (MK_COMB (@lem5476504) (@lem5476503)). Qed.
Lemma lem5476506 : term513 = term516.
Proof. exact (MK_COMB (@lem5476505) (@lem5476500)). Qed.
Lemma lem5476507 : term517.
Proof. exact (@lem1980255 term318 term331 term331 term331). Qed.
Lemma lem5476509 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476510 : term513 = term519.
Proof. exact (@lem5476509 (NUMERAL 0) term332). Qed.
Lemma lem5476511 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476512 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476513 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476512 h1) (fun h1 : term519 = True => @lem5476511)). Qed.
Lemma lem5476514 : term519 = True.
Proof. exact (EQ_MP (@lem5476513) (@lem5476511)). Qed.
Lemma lem5476515 : term513 = True.
Proof. exact (TRANS (@lem5476510) (@lem5476514)). Qed.
Lemma lem5476516 : True = term513.
Proof. exact (SYM (@lem5476515)). Qed.
Lemma lem5476517 : term513.
Proof. exact (EQ_MP (@lem5476516) (@lem0)). Qed.
Lemma lem5476518 : term521.
Proof. exact (@lem5476507 (@lem5476517)). Qed.
Lemma lem5476520 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476521 : term513 = term519.
Proof. exact (@lem5476520 (NUMERAL 0) term332). Qed.
Lemma lem5476522 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476523 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476524 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476523 h1) (fun h1 : term519 = True => @lem5476522)). Qed.
Lemma lem5476525 : term519 = True.
Proof. exact (EQ_MP (@lem5476524) (@lem5476522)). Qed.
Lemma lem5476526 : term513 = True.
Proof. exact (TRANS (@lem5476521) (@lem5476525)). Qed.
Lemma lem5476527 : True = term513.
Proof. exact (SYM (@lem5476526)). Qed.
Lemma lem5476528 : term513.
Proof. exact (EQ_MP (@lem5476527) (@lem0)). Qed.
Lemma lem5476529 : term516 = term522.
Proof. exact (@lem5476518 (@lem5476528)). Qed.
Lemma lem5476531 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476532 : term372 = term373.
Proof. exact (@lem5476531 term332 term332). Qed.
Lemma lem5476533 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476534 : term375 = term332.
Proof. exact (EQ_MP (@lem5476533) (@lem940073)). Qed.
Lemma lem5476535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476536 : term373 = term331.
Proof. exact (MK_COMB (@lem5476535) (@lem5476534)). Qed.
Lemma lem5476537 : term372 = term331.
Proof. exact (TRANS (@lem5476532) (@lem5476536)). Qed.
Lemma lem5476539 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476540 : term524 = term318.
Proof. exact (@lem5476539 term332). Qed.
Lemma lem5476541 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5476542 : term525 = term514.
Proof. exact (MK_COMB (@lem5476541) (@lem5476540)). Qed.
Lemma lem5476543 : term522 = term513.
Proof. exact (MK_COMB (@lem5476542) (@lem5476537)). Qed.
Lemma lem5476545 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476546 : term513 = term519.
Proof. exact (@lem5476545 (NUMERAL 0) term332). Qed.
Lemma lem5476547 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476548 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476549 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476548 h1) (fun h1 : term519 = True => @lem5476547)). Qed.
Lemma lem5476550 : term519 = True.
Proof. exact (EQ_MP (@lem5476549) (@lem5476547)). Qed.
Lemma lem5476551 : term513 = True.
Proof. exact (TRANS (@lem5476546) (@lem5476550)). Qed.
Lemma lem5476552 : term522 = True.
Proof. exact (TRANS (@lem5476543) (@lem5476551)). Qed.
Lemma lem5476553 : term516 = True.
Proof. exact (TRANS (@lem5476529) (@lem5476552)). Qed.
Lemma lem5476554 : term513 = True.
Proof. exact (TRANS (@lem5476506) (@lem5476553)). Qed.
Lemma lem5476555 : term512 = True.
Proof. exact (TRANS (@lem5476497) (@lem5476554)). Qed.
Lemma lem5476556 : True = term512.
Proof. exact (SYM (@lem5476555)). Qed.
Lemma lem5476557 : term512.
Proof. exact (EQ_MP (@lem5476556) (@lem0)). Qed.
Lemma lem5476558 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term571 _70583 _70584.
Proof. exact (conj (@lem5476557) (@lem5476145 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476560 (x : real) (y : real) : term527 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5476561 (_70583 : int) (_70584 : int) : term572 _70583 _70584.
Proof. exact (@lem5476560 term331 (term420 _70583 _70584)). Qed.
Lemma lem5476562 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term573 _70583 _70584.
Proof. exact (@lem5476561 _70583 _70584 (@lem5476558 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476563 (_70583 : int) (_70584 : int) : (term574 _70583 _70584) = (term420 _70583 _70584).
Proof. exact (@lem1982733 (term420 _70583 _70584)). Qed.
Lemma lem5476564 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5476565 (_70583 : int) (_70584 : int) : (term575 _70583 _70584) = (term421 _70583 _70584).
Proof. exact (MK_COMB (@lem5476564) (@lem5476563 _70583 _70584)). Qed.
Lemma lem5476566 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5476567 (_70583 : int) (_70584 : int) : (term573 _70583 _70584) = (term422 _70583 _70584).
Proof. exact (MK_COMB (@lem5476565 _70583 _70584) (@lem5476566)). Qed.
Lemma lem5476568 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term422 _70583 _70584.
Proof. exact (EQ_MP (@lem5476567 _70583 _70584) (@lem5476562 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476569 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term576 _70583 _70584.
Proof. exact (conj (@lem5476568 _70582 _70580 _70581 _70583 _70584 h1) (@lem5476494 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476571 (x : real) (y : real) : term543 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5476572 (_70583 : int) (_70584 : int) : term577 _70583 _70584.
Proof. exact (@lem5476571 (term420 _70583 _70584) (term406 _70583 _70584)). Qed.
Lemma lem5476573 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term578 _70583 _70584.
Proof. exact (@lem5476572 _70583 _70584 (@lem5476569 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476574 (_70583 : int) (_70584 : int) : (term579 _70583 _70584) = (term580 _70583 _70584).
Proof. exact (@lem1982753 (term411 _70583) (real_of_int _70583) (term581 _70584) (term411 _70584)). Qed.
Lemma lem5476575 (_70583 : int) : (term548 _70583) = (term549 _70583).
Proof. exact (@lem1982713 term363 (real_of_int _70583)). Qed.
Lemma lem5476577 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476578 : term331 = term389.
Proof. exact (@lem5476577 term332). Qed.
Lemma lem5476580 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5476581 : term363 = term364.
Proof. exact (@lem5476580 term332). Qed.
Lemma lem5476582 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476583 : term550 = term551.
Proof. exact (MK_COMB (@lem5476582) (@lem5476581)). Qed.
Lemma lem5476584 : term552 = term553.
Proof. exact (MK_COMB (@lem5476583) (@lem5476578)). Qed.
Lemma lem5476585 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5476587 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476588 : term513 = term519.
Proof. exact (@lem5476587 (NUMERAL 0) term332). Qed.
Lemma lem5476589 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476590 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476591 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476590 h1) (fun h1 : term519 = True => @lem5476589)). Qed.
Lemma lem5476592 : term519 = True.
Proof. exact (EQ_MP (@lem5476591) (@lem5476589)). Qed.
Lemma lem5476593 : term513 = True.
Proof. exact (TRANS (@lem5476588) (@lem5476592)). Qed.
Lemma lem5476594 : True = term513.
Proof. exact (SYM (@lem5476593)). Qed.
Lemma lem5476595 : term513.
Proof. exact (EQ_MP (@lem5476594) (@lem0)). Qed.
Lemma lem5476596 : term555.
Proof. exact (@lem5476585 (@lem5476595)). Qed.
Lemma lem5476598 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476599 : term513 = term519.
Proof. exact (@lem5476598 (NUMERAL 0) term332). Qed.
Lemma lem5476600 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476601 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476602 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476601 h1) (fun h1 : term519 = True => @lem5476600)). Qed.
Lemma lem5476603 : term519 = True.
Proof. exact (EQ_MP (@lem5476602) (@lem5476600)). Qed.
Lemma lem5476604 : term513 = True.
Proof. exact (TRANS (@lem5476599) (@lem5476603)). Qed.
Lemma lem5476605 : True = term513.
Proof. exact (SYM (@lem5476604)). Qed.
Lemma lem5476606 : term513.
Proof. exact (EQ_MP (@lem5476605) (@lem0)). Qed.
Lemma lem5476607 : term556.
Proof. exact (@lem5476596 (@lem5476606)). Qed.
Lemma lem5476609 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476610 : term513 = term519.
Proof. exact (@lem5476609 (NUMERAL 0) term332). Qed.
Lemma lem5476611 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476612 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476613 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476612 h1) (fun h1 : term519 = True => @lem5476611)). Qed.
Lemma lem5476614 : term519 = True.
Proof. exact (EQ_MP (@lem5476613) (@lem5476611)). Qed.
Lemma lem5476615 : term513 = True.
Proof. exact (TRANS (@lem5476610) (@lem5476614)). Qed.
Lemma lem5476616 : True = term513.
Proof. exact (SYM (@lem5476615)). Qed.
Lemma lem5476617 : term513.
Proof. exact (EQ_MP (@lem5476616) (@lem0)). Qed.
Lemma lem5476618 : term557.
Proof. exact (@lem5476607 (@lem5476617)). Qed.
Lemma lem5476620 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476621 : term372 = term373.
Proof. exact (@lem5476620 term332 term332). Qed.
Lemma lem5476622 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476623 : term375 = term332.
Proof. exact (EQ_MP (@lem5476622) (@lem940073)). Qed.
Lemma lem5476624 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476625 : term373 = term331.
Proof. exact (MK_COMB (@lem5476624) (@lem5476623)). Qed.
Lemma lem5476626 : term372 = term331.
Proof. exact (TRANS (@lem5476621) (@lem5476625)). Qed.
Lemma lem5476628 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5476629 : term390 = term395.
Proof. exact (@lem5476628 term332 term332). Qed.
Lemma lem5476630 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476631 : term375 = term332.
Proof. exact (EQ_MP (@lem5476630) (@lem940073)). Qed.
Lemma lem5476632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476633 : term373 = term331.
Proof. exact (MK_COMB (@lem5476632) (@lem5476631)). Qed.
Lemma lem5476634 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5476635 : term395 = term363.
Proof. exact (MK_COMB (@lem5476634) (@lem5476633)). Qed.
Lemma lem5476636 : term390 = term363.
Proof. exact (TRANS (@lem5476629) (@lem5476635)). Qed.
Lemma lem5476637 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476638 : term558 = term550.
Proof. exact (MK_COMB (@lem5476637) (@lem5476636)). Qed.
Lemma lem5476639 : term559 = term552.
Proof. exact (MK_COMB (@lem5476638) (@lem5476626)). Qed.
Lemma lem5476641 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5476642 : term552 = term318.
Proof. exact (@lem5476641 term332). Qed.
Lemma lem5476643 : term559 = term318.
Proof. exact (TRANS (@lem5476639) (@lem5476642)). Qed.
Lemma lem5476644 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476645 : term561 = term562.
Proof. exact (MK_COMB (@lem5476644) (@lem5476643)). Qed.
Lemma lem5476646 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5476647 : term563 = term524.
Proof. exact (MK_COMB (@lem5476645) (@lem5476646)). Qed.
Lemma lem5476649 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476650 : term524 = term318.
Proof. exact (@lem5476649 term332). Qed.
Lemma lem5476651 : term563 = term318.
Proof. exact (TRANS (@lem5476647) (@lem5476650)). Qed.
Lemma lem5476653 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476654 : term372 = term373.
Proof. exact (@lem5476653 term332 term332). Qed.
Lemma lem5476655 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476656 : term375 = term332.
Proof. exact (EQ_MP (@lem5476655) (@lem940073)). Qed.
Lemma lem5476657 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476658 : term373 = term331.
Proof. exact (MK_COMB (@lem5476657) (@lem5476656)). Qed.
Lemma lem5476659 : term372 = term331.
Proof. exact (TRANS (@lem5476654) (@lem5476658)). Qed.
Lemma lem5476660 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5476661 : term564 = term524.
Proof. exact (MK_COMB (@lem5476660) (@lem5476659)). Qed.
Lemma lem5476663 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476664 : term524 = term318.
Proof. exact (@lem5476663 term332). Qed.
Lemma lem5476665 : term564 = term318.
Proof. exact (TRANS (@lem5476661) (@lem5476664)). Qed.
Lemma lem5476666 : term318 = term564.
Proof. exact (SYM (@lem5476665)). Qed.
Lemma lem5476667 : term563 = term564.
Proof. exact (TRANS (@lem5476651) (@lem5476666)). Qed.
Lemma lem5476668 : term553 = term360.
Proof. exact (@lem5476618 (@lem5476667)). Qed.
Lemma lem5476669 : term552 = term360.
Proof. exact (TRANS (@lem5476584) (@lem5476668)). Qed.
Lemma lem5476671 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5476672 : term360 = term318.
Proof. exact (@lem5476671 term318). Qed.
Lemma lem5476673 : term552 = term318.
Proof. exact (TRANS (@lem5476669) (@lem5476672)). Qed.
Lemma lem5476674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476675 : term565 = term562.
Proof. exact (MK_COMB (@lem5476674) (@lem5476673)). Qed.
Lemma lem5476676 (_70583 : int) : (real_of_int _70583) = (real_of_int _70583).
Proof. exact (eq_refl (real_of_int _70583)). Qed.
Lemma lem5476677 (_70583 : int) : (term549 _70583) = (term566 _70583).
Proof. exact (MK_COMB (@lem5476675) (@lem5476676 _70583)). Qed.
Lemma lem5476678 (_70583 : int) : (term548 _70583) = (term566 _70583).
Proof. exact (TRANS (@lem5476575 _70583) (@lem5476677 _70583)). Qed.
Lemma lem5476679 (_70583 : int) : (term566 _70583) = term318.
Proof. exact (@lem1982719 (real_of_int _70583)). Qed.
Lemma lem5476680 (_70583 : int) : (term548 _70583) = term318.
Proof. exact (TRANS (@lem5476678 _70583) (@lem5476679 _70583)). Qed.
Lemma lem5476681 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476682 (_70583 : int) : (term567 _70583) = term568.
Proof. exact (MK_COMB (@lem5476681) (@lem5476680 _70583)). Qed.
Lemma lem5476683 (_70584 : int) : (term582 _70584) = (term583 _70584).
Proof. exact (@lem1982759 (real_of_int _70584) (term411 _70584) term363). Qed.
Lemma lem5476684 (_70584 : int) : (term584 _70584) = (term549 _70584).
Proof. exact (@lem1982715 term363 (real_of_int _70584)). Qed.
Lemma lem5476686 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476687 : term331 = term389.
Proof. exact (@lem5476686 term332). Qed.
Lemma lem5476689 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5476690 : term363 = term364.
Proof. exact (@lem5476689 term332). Qed.
Lemma lem5476691 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476692 : term550 = term551.
Proof. exact (MK_COMB (@lem5476691) (@lem5476690)). Qed.
Lemma lem5476693 : term552 = term553.
Proof. exact (MK_COMB (@lem5476692) (@lem5476687)). Qed.
Lemma lem5476694 : term554.
Proof. exact (@lem1981473 term363 term331 term331 term331 term318 term331). Qed.
Lemma lem5476696 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476697 : term513 = term519.
Proof. exact (@lem5476696 (NUMERAL 0) term332). Qed.
Lemma lem5476698 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476699 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476700 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476699 h1) (fun h1 : term519 = True => @lem5476698)). Qed.
Lemma lem5476701 : term519 = True.
Proof. exact (EQ_MP (@lem5476700) (@lem5476698)). Qed.
Lemma lem5476702 : term513 = True.
Proof. exact (TRANS (@lem5476697) (@lem5476701)). Qed.
Lemma lem5476703 : True = term513.
Proof. exact (SYM (@lem5476702)). Qed.
Lemma lem5476704 : term513.
Proof. exact (EQ_MP (@lem5476703) (@lem0)). Qed.
Lemma lem5476705 : term555.
Proof. exact (@lem5476694 (@lem5476704)). Qed.
Lemma lem5476707 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476708 : term513 = term519.
Proof. exact (@lem5476707 (NUMERAL 0) term332). Qed.
Lemma lem5476709 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476710 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476711 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476710 h1) (fun h1 : term519 = True => @lem5476709)). Qed.
Lemma lem5476712 : term519 = True.
Proof. exact (EQ_MP (@lem5476711) (@lem5476709)). Qed.
Lemma lem5476713 : term513 = True.
Proof. exact (TRANS (@lem5476708) (@lem5476712)). Qed.
Lemma lem5476714 : True = term513.
Proof. exact (SYM (@lem5476713)). Qed.
Lemma lem5476715 : term513.
Proof. exact (EQ_MP (@lem5476714) (@lem0)). Qed.
Lemma lem5476716 : term556.
Proof. exact (@lem5476705 (@lem5476715)). Qed.
Lemma lem5476718 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476719 : term513 = term519.
Proof. exact (@lem5476718 (NUMERAL 0) term332). Qed.
Lemma lem5476720 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476721 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476722 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476721 h1) (fun h1 : term519 = True => @lem5476720)). Qed.
Lemma lem5476723 : term519 = True.
Proof. exact (EQ_MP (@lem5476722) (@lem5476720)). Qed.
Lemma lem5476724 : term513 = True.
Proof. exact (TRANS (@lem5476719) (@lem5476723)). Qed.
Lemma lem5476725 : True = term513.
Proof. exact (SYM (@lem5476724)). Qed.
Lemma lem5476726 : term513.
Proof. exact (EQ_MP (@lem5476725) (@lem0)). Qed.
Lemma lem5476727 : term557.
Proof. exact (@lem5476716 (@lem5476726)). Qed.
Lemma lem5476729 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476730 : term372 = term373.
Proof. exact (@lem5476729 term332 term332). Qed.
Lemma lem5476731 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476732 : term375 = term332.
Proof. exact (EQ_MP (@lem5476731) (@lem940073)). Qed.
Lemma lem5476733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476734 : term373 = term331.
Proof. exact (MK_COMB (@lem5476733) (@lem5476732)). Qed.
Lemma lem5476735 : term372 = term331.
Proof. exact (TRANS (@lem5476730) (@lem5476734)). Qed.
Lemma lem5476737 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5476738 : term390 = term395.
Proof. exact (@lem5476737 term332 term332). Qed.
Lemma lem5476739 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476740 : term375 = term332.
Proof. exact (EQ_MP (@lem5476739) (@lem940073)). Qed.
Lemma lem5476741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476742 : term373 = term331.
Proof. exact (MK_COMB (@lem5476741) (@lem5476740)). Qed.
Lemma lem5476743 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5476744 : term395 = term363.
Proof. exact (MK_COMB (@lem5476743) (@lem5476742)). Qed.
Lemma lem5476745 : term390 = term363.
Proof. exact (TRANS (@lem5476738) (@lem5476744)). Qed.
Lemma lem5476746 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476747 : term558 = term550.
Proof. exact (MK_COMB (@lem5476746) (@lem5476745)). Qed.
Lemma lem5476748 : term559 = term552.
Proof. exact (MK_COMB (@lem5476747) (@lem5476735)). Qed.
Lemma lem5476750 (m : nat) : (term560 m) = term318.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5476751 : term552 = term318.
Proof. exact (@lem5476750 term332). Qed.
Lemma lem5476752 : term559 = term318.
Proof. exact (TRANS (@lem5476748) (@lem5476751)). Qed.
Lemma lem5476753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476754 : term561 = term562.
Proof. exact (MK_COMB (@lem5476753) (@lem5476752)). Qed.
Lemma lem5476755 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem5476756 : term563 = term524.
Proof. exact (MK_COMB (@lem5476754) (@lem5476755)). Qed.
Lemma lem5476758 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476759 : term524 = term318.
Proof. exact (@lem5476758 term332). Qed.
Lemma lem5476760 : term563 = term318.
Proof. exact (TRANS (@lem5476756) (@lem5476759)). Qed.
Lemma lem5476762 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5476763 : term372 = term373.
Proof. exact (@lem5476762 term332 term332). Qed.
Lemma lem5476764 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476765 : term375 = term332.
Proof. exact (EQ_MP (@lem5476764) (@lem940073)). Qed.
Lemma lem5476766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476767 : term373 = term331.
Proof. exact (MK_COMB (@lem5476766) (@lem5476765)). Qed.
Lemma lem5476768 : term372 = term331.
Proof. exact (TRANS (@lem5476763) (@lem5476767)). Qed.
Lemma lem5476769 : term562 = term562.
Proof. exact (eq_refl term562). Qed.
Lemma lem5476770 : term564 = term524.
Proof. exact (MK_COMB (@lem5476769) (@lem5476768)). Qed.
Lemma lem5476772 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476773 : term524 = term318.
Proof. exact (@lem5476772 term332). Qed.
Lemma lem5476774 : term564 = term318.
Proof. exact (TRANS (@lem5476770) (@lem5476773)). Qed.
Lemma lem5476775 : term318 = term564.
Proof. exact (SYM (@lem5476774)). Qed.
Lemma lem5476776 : term563 = term564.
Proof. exact (TRANS (@lem5476760) (@lem5476775)). Qed.
Lemma lem5476777 : term553 = term360.
Proof. exact (@lem5476727 (@lem5476776)). Qed.
Lemma lem5476778 : term552 = term360.
Proof. exact (TRANS (@lem5476693) (@lem5476777)). Qed.
Lemma lem5476780 (x : real) : (term379 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5476781 : term360 = term318.
Proof. exact (@lem5476780 term318). Qed.
Lemma lem5476782 : term552 = term318.
Proof. exact (TRANS (@lem5476778) (@lem5476781)). Qed.
Lemma lem5476783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5476784 : term565 = term562.
Proof. exact (MK_COMB (@lem5476783) (@lem5476782)). Qed.
Lemma lem5476785 (_70584 : int) : (real_of_int _70584) = (real_of_int _70584).
Proof. exact (eq_refl (real_of_int _70584)). Qed.
Lemma lem5476786 (_70584 : int) : (term549 _70584) = (term566 _70584).
Proof. exact (MK_COMB (@lem5476784) (@lem5476785 _70584)). Qed.
Lemma lem5476787 (_70584 : int) : (term584 _70584) = (term566 _70584).
Proof. exact (TRANS (@lem5476684 _70584) (@lem5476786 _70584)). Qed.
Lemma lem5476788 (_70584 : int) : (term566 _70584) = term318.
Proof. exact (@lem1982719 (real_of_int _70584)). Qed.
Lemma lem5476789 (_70584 : int) : (term584 _70584) = term318.
Proof. exact (TRANS (@lem5476787 _70584) (@lem5476788 _70584)). Qed.
Lemma lem5476790 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5476791 (_70584 : int) : (term585 _70584) = term568.
Proof. exact (MK_COMB (@lem5476790) (@lem5476789 _70584)). Qed.
Lemma lem5476792 : term363 = term363.
Proof. exact (eq_refl term363). Qed.
Lemma lem5476793 (_70584 : int) : (term583 _70584) = term586.
Proof. exact (MK_COMB (@lem5476791 _70584) (@lem5476792)). Qed.
Lemma lem5476794 (_70584 : int) : (term582 _70584) = term586.
Proof. exact (TRANS (@lem5476683 _70584) (@lem5476793 _70584)). Qed.
Lemma lem5476795 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5476796 (_70584 : int) : (term582 _70584) = term363.
Proof. exact (TRANS (@lem5476794 _70584) (@lem5476795)). Qed.
Lemma lem5476797 (_70583 : int) (_70584 : int) : (term580 _70583 _70584) = term586.
Proof. exact (MK_COMB (@lem5476682 _70583) (@lem5476796 _70584)). Qed.
Lemma lem5476798 (_70583 : int) (_70584 : int) : (term579 _70583 _70584) = term586.
Proof. exact (TRANS (@lem5476574 _70583 _70584) (@lem5476797 _70583 _70584)). Qed.
Lemma lem5476799 : term586 = term363.
Proof. exact (@lem1982721 term363). Qed.
Lemma lem5476800 (_70583 : int) (_70584 : int) : (term579 _70583 _70584) = term363.
Proof. exact (TRANS (@lem5476798 _70583 _70584) (@lem5476799)). Qed.
Lemma lem5476801 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5476802 (_70583 : int) (_70584 : int) : (term587 _70583 _70584) = term588.
Proof. exact (MK_COMB (@lem5476801) (@lem5476800 _70583 _70584)). Qed.
Lemma lem5476803 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem5476804 (_70583 : int) (_70584 : int) : (term578 _70583 _70584) = term589.
Proof. exact (MK_COMB (@lem5476802 _70583 _70584) (@lem5476803)). Qed.
Lemma lem5476805 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : term589.
Proof. exact (EQ_MP (@lem5476804 _70583 _70584) (@lem5476573 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476807 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5476808 : term589 = term590.
Proof. exact (@lem5476807 term318 term363). Qed.
Lemma lem5476810 (x : nat) : (term361 x) = (term362 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5476811 : term363 = term364.
Proof. exact (@lem5476810 term332). Qed.
Lemma lem5476813 (x : nat) : (real_of_num x) = (term359 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5476814 : term318 = term360.
Proof. exact (@lem5476813 (NUMERAL 0)). Qed.
Lemma lem5476815 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5476816 : term320 = term591.
Proof. exact (MK_COMB (@lem5476815) (@lem5476814)). Qed.
Lemma lem5476817 : term590 = term592.
Proof. exact (MK_COMB (@lem5476816) (@lem5476811)). Qed.
Lemma lem5476818 : term593.
Proof. exact (@lem1980026 term318 term331 term363 term331). Qed.
Lemma lem5476820 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476821 : term513 = term519.
Proof. exact (@lem5476820 (NUMERAL 0) term332). Qed.
Lemma lem5476822 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476823 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476824 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476823 h1) (fun h1 : term519 = True => @lem5476822)). Qed.
Lemma lem5476825 : term519 = True.
Proof. exact (EQ_MP (@lem5476824) (@lem5476822)). Qed.
Lemma lem5476826 : term513 = True.
Proof. exact (TRANS (@lem5476821) (@lem5476825)). Qed.
Lemma lem5476827 : True = term513.
Proof. exact (SYM (@lem5476826)). Qed.
Lemma lem5476828 : term513.
Proof. exact (EQ_MP (@lem5476827) (@lem0)). Qed.
Lemma lem5476829 : term594.
Proof. exact (@lem5476818 (@lem5476828)). Qed.
Lemma lem5476831 (m : nat) (n : nat) : (term518 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5476832 : term513 = term519.
Proof. exact (@lem5476831 (NUMERAL 0) term332). Qed.
Lemma lem5476833 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476834 (h1 : term520 = (BIT1 0)) : term519 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5476835 : (term520 = (BIT1 0)) = (term519 = True).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476834 h1) (fun h1 : term519 = True => @lem5476833)). Qed.
Lemma lem5476836 : term519 = True.
Proof. exact (EQ_MP (@lem5476835) (@lem5476833)). Qed.
Lemma lem5476837 : term513 = True.
Proof. exact (TRANS (@lem5476832) (@lem5476836)). Qed.
Lemma lem5476838 : True = term513.
Proof. exact (SYM (@lem5476837)). Qed.
Lemma lem5476839 : term513.
Proof. exact (EQ_MP (@lem5476838) (@lem0)). Qed.
Lemma lem5476840 : term592 = term595.
Proof. exact (@lem5476829 (@lem5476839)). Qed.
Lemma lem5476842 (m : nat) (n : nat) : (term393 m n) = (term394 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5476843 : term390 = term395.
Proof. exact (@lem5476842 term332 term332). Qed.
Lemma lem5476844 : (term374 = (BIT1 0)) = (term375 = term332).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5476845 : term375 = term332.
Proof. exact (EQ_MP (@lem5476844) (@lem940073)). Qed.
Lemma lem5476846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5476847 : term373 = term331.
Proof. exact (MK_COMB (@lem5476846) (@lem5476845)). Qed.
Lemma lem5476848 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5476849 : term395 = term363.
Proof. exact (MK_COMB (@lem5476848) (@lem5476847)). Qed.
Lemma lem5476850 : term390 = term363.
Proof. exact (TRANS (@lem5476843) (@lem5476849)). Qed.
Lemma lem5476852 (x : nat) : (term523 x) = term318.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5476853 : term524 = term318.
Proof. exact (@lem5476852 term332). Qed.
Lemma lem5476854 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5476855 : term596 = term320.
Proof. exact (MK_COMB (@lem5476854) (@lem5476853)). Qed.
Lemma lem5476856 : term595 = term590.
Proof. exact (MK_COMB (@lem5476855) (@lem5476850)). Qed.
Lemma lem5476858 (m : nat) (n : nat) : (term597 m n) = (term598 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5476859 : term590 = term599.
Proof. exact (@lem5476858 (NUMERAL 0) term332). Qed.
Lemma lem5476860 : term520 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5476861 (h1 : term520 = (BIT1 0)) : (term332 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5476862 : (term520 = (BIT1 0)) = ((term332 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term520 = (BIT1 0) => @lem5476861 h1) (fun h1 : (term332 = (NUMERAL 0)) = False => @lem5476860)). Qed.
Lemma lem5476863 : (term332 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5476862) (@lem5476860)). Qed.
Lemma lem5476864 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5476865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5476866 : term600 = (and True).
Proof. exact (MK_COMB (@lem5476865) (@lem5476864)). Qed.
Lemma lem5476867 : term599 = (True /\ False).
Proof. exact (MK_COMB (@lem5476866) (@lem5476863)). Qed.
Lemma lem5476869 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5476870 : term599 = False.
Proof. exact (TRANS (@lem5476867) (@lem5476869)). Qed.
Lemma lem5476871 : term590 = False.
Proof. exact (TRANS (@lem5476859) (@lem5476870)). Qed.
Lemma lem5476872 : term595 = False.
Proof. exact (TRANS (@lem5476856) (@lem5476871)). Qed.
Lemma lem5476873 : term592 = False.
Proof. exact (TRANS (@lem5476840) (@lem5476872)). Qed.
Lemma lem5476874 : term590 = False.
Proof. exact (TRANS (@lem5476817) (@lem5476873)). Qed.
Lemma lem5476875 : term589 = False.
Proof. exact (TRANS (@lem5476808) (@lem5476874)). Qed.
Lemma lem5476876 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term617 _70582 _70580 _70581 _70583 _70584) : False.
Proof. exact (EQ_MP (@lem5476875) (@lem5476805 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476877 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term501 _70582 _70580 _70581 _70583 _70584) : False.
Proof. exact (or_elim (@lem5475380 _70582 _70580 _70581 _70583 _70584 h1) (fun h0 : term616 _70582 _70580 _70581 _70583 _70584 => @lem5476129 _70582 _70580 _70581 _70583 _70584 h0) (fun h0 : term617 _70582 _70580 _70581 _70583 _70584 => @lem5476876 _70582 _70580 _70581 _70583 _70584 h0)). Qed.
Lemma lem5476878 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term510 _70582 _70580 _70581 _70583 _70584) : False.
Proof. exact (or_elim (@lem5473881 _70582 _70580 _70581 _70583 _70584 h1) (fun h0 : term505 _70583 _70580 _70581 _70582 _70584 => @lem5475379 _70583 _70580 _70581 _70582 _70584 h0) (fun h0 : term501 _70582 _70580 _70581 _70583 _70584 => @lem5476877 _70582 _70580 _70581 _70583 _70584 h0)). Qed.
Lemma lem5476880 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term510 _70582 _70580 _70581 _70583 _70584) : term510 _70582 _70580 _70581 _70583 _70584.
Proof. exact (h1). Qed.
Lemma lem5476881 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term510 _70582 _70580 _70581 _70583 _70584) : (term510 _70582 _70580 _70581 _70583 _70584) = False.
Proof. exact (prop_ext (fun h2 : term510 _70582 _70580 _70581 _70583 _70584 => @lem5476878 _70582 _70580 _70581 _70583 _70584 h1) (fun h2 : False => @lem5476880 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476882 (_70582 : int) (_70580 : int) (_70581 : int) (_70583 : int) (_70584 : int) (h1 : term510 _70582 _70580 _70581 _70583 _70584) : False.
Proof. exact (EQ_MP (@lem5476881 _70582 _70580 _70581 _70583 _70584 h1) (@lem5476880 _70582 _70580 _70581 _70583 _70584 h1)). Qed.
Lemma lem5476883 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) (h1 : term355 _70580 _70581 _70582 _70583 _70584) : term355 _70580 _70581 _70582 _70583 _70584.
Proof. exact (h1). Qed.
Lemma lem5476884 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) (h1 : term355 _70580 _70581 _70582 _70583 _70584) : term510 _70582 _70580 _70581 _70583 _70584.
Proof. exact (EQ_MP (@lem5473859 _70582 _70580 _70581 _70583 _70584) (@lem5476883 _70580 _70581 _70582 _70583 _70584 h1)). Qed.
Lemma lem5476885 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) (h1 : term355 _70580 _70581 _70582 _70583 _70584) : (term510 _70582 _70580 _70581 _70583 _70584) = False.
Proof. exact (prop_ext (fun h2 : term510 _70582 _70580 _70581 _70583 _70584 => @lem5476882 _70582 _70580 _70581 _70583 _70584 h2) (fun h2 : False => @lem5476884 _70580 _70581 _70582 _70583 _70584 h1)). Qed.
Lemma lem5476886 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) (h1 : term355 _70580 _70581 _70582 _70583 _70584) : False.
Proof. exact (EQ_MP (@lem5476885 _70580 _70581 _70582 _70583 _70584 h1) (@lem5476884 _70580 _70581 _70582 _70583 _70584 h1)). Qed.
Lemma lem5476887 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : term619 _70580 _70581 _70582 _70583 _70584.
Proof. exact (fun h0 : term355 _70580 _70581 _70582 _70583 _70584 => @lem5476886 _70580 _70581 _70582 _70583 _70584 h0). Qed.
Lemma lem5476888 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : term620 _70580 _70581 _70582 _70583 _70584.
Proof. exact (@lem1386578 (term621 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5476891 (_70580 : int) (_70581 : int) (_70582 : int) (_70583 : int) (_70584 : int) : term621 _70580 _70581 _70582 _70583 _70584.
Proof. exact (@lem5476888 _70580 _70581 _70582 _70583 _70584 (@lem5476887 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5476892 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term354 _70580 _70581 _70582 _70583 _70584) = (term311 _70580 _70581 _70582 _70584 _70583).
Proof. exact (SYM (@lem5473000 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5476893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5476894 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : (term621 _70580 _70581 _70582 _70583 _70584) = (term257 _70580 _70581 _70582 _70584 _70583).
Proof. exact (MK_COMB (@lem5476893) (@lem5476892 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5476895 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : term257 _70580 _70581 _70582 _70584 _70583.
Proof. exact (EQ_MP (@lem5476894 _70580 _70581 _70582 _70584 _70583) (@lem5476891 _70580 _70581 _70582 _70583 _70584)). Qed.
Lemma lem5476896 (_70580 : int) (_70581 : int) (_70582 : int) (_70584 : int) (_70583 : int) : term258 _70580 _70581 _70582 _70584 _70583.
Proof. exact (EQ_MP (@lem5472663 _70580 _70581 _70582 _70584 _70583) (@lem5476895 _70580 _70581 _70582 _70584 _70583)). Qed.
Lemma lem5476897 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : term622 m n p x q.
Proof. exact (@lem5476896 (int_of_num m) (int_of_num n) (int_of_num p) (int_of_num x) (int_of_num q)). Qed.
Lemma lem5476898 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : term623 m n p x q.
Proof. exact (@lem5476897 m n p x q (@lem5472650 m)). Qed.
Lemma lem5476899 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : term624 m n p x q.
Proof. exact (@lem5476898 m n p x q (@lem5472653 n)). Qed.
Lemma lem5476900 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : term625 m n p x q.
Proof. exact (@lem5476899 m n p x q (@lem5472656 p)). Qed.
Lemma lem5476901 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : term626 m n p x q.
Proof. exact (@lem5476900 m n p x q (@lem5472659 q)). Qed.
Lemma lem5476902 (m : nat) (n : nat) (p : nat) (x : nat) (q : nat) : term252 m n p x q.
Proof. exact (@lem5476901 m n p x q (@lem5472662 x)). Qed.
Lemma lem5476903 (m : nat) (n : nat) (p : nat) (q : nat) : term254 m n p q.
Proof. exact (fun x : nat => @lem5476902 m n p x q). Qed.
Lemma lem5476904 (m : nat) (n : nat) (p : nat) (q : nat) : (term254 m n p q) = (term217 m n p q).
Proof. exact (SYM (@lem5472647 m n p q)). Qed.
Lemma lem5476905 (m : nat) (n : nat) (p : nat) (q : nat) : term217 m n p q.
Proof. exact (EQ_MP (@lem5476904 m n p q) (@lem5476903 m n p q)). Qed.
Lemma lem5476906 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = ((term217 m n p q) = True).
Proof. exact (@lem7 (term217 m n p q)). Qed.
Lemma lem5476907 (m : nat) (n : nat) (p : nat) (q : nat) : (term217 m n p q) = True.
Proof. exact (EQ_MP (@lem5476906 m n p q) (@lem5476905 m n p q)). Qed.
Lemma lem5476908 (m : nat) (n : nat) (p : nat) (q : nat) : True = (term217 m n p q).
Proof. exact (SYM (@lem5476907 m n p q)). Qed.
Lemma lem5476909 (m : nat) (n : nat) (p : nat) (q : nat) : term217 m n p q.
Proof. exact (EQ_MP (@lem5476908 m n p q) (@lem0)). Qed.
Lemma lem5476910 (m : nat) (n : nat) (p : nat) (q : nat) : term627 m n p q.
Proof. exact (conj (@lem5472390 p m n q) (@lem5476909 m n p q)). Qed.
Lemma lem5476911 (p : nat) (m : nat) (n : nat) (q : nat) : (term627 m n p q) = ((term27 m n p q) = (term30 p m n q)).
Proof. exact (@lem32 (term27 m n p q) (term30 p m n q)). Qed.
Lemma lem5476912 (p : nat) (m : nat) (n : nat) (q : nat) : (term27 m n p q) = (term30 p m n q).
Proof. exact (EQ_MP (@lem5476911 p m n q) (@lem5476910 m n p q)). Qed.
Lemma lem5476913 (p : nat) (m : nat) (n : nat) (q : nat) : (term19 m n p q) = (term30 p m n q).
Proof. exact (EQ_MP (@lem5470642 p m n q) (@lem5476912 p m n q)). Qed.
Lemma lem5476918 (p : nat) (m : nat) (n : nat) : term628 p m n.
Proof. exact (fun q : nat => @lem5476913 p m n q). Qed.
Lemma lem5476923 (m : nat) (n : nat) : term629 m n.
Proof. exact (fun p : nat => @lem5476918 p m n). Qed.
Lemma lem5476928 (m : nat) : term630 m.
Proof. exact (fun n : nat => @lem5476923 m n). Qed.
Lemma lem5476933 : term631.
Proof. exact (fun m : nat => @lem5476928 m). Qed.
