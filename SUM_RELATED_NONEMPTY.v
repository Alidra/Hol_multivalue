Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_RELATED_NONEMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import ITERATE_RELATED_NONEMPTY_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import sum_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7205599 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7205600 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7205601 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7205600 t1) (@lem7205599 t1)). Qed.
Lemma lem7205602 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7205601 t1 t2). Qed.
Lemma lem7205603 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7205604 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7205603 t1 t2) (@lem7205602 t1 t2)). Qed.
Lemma lem7205605 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7205604 t1 t2 t3). Qed.
Lemma lem7205606 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7205607 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7205606 t1 t2 t3) (@lem7205605 t1 t2 t3)). Qed.
Lemma lem7205608 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7205607 t1 t2 t3)). Qed.
Lemma lem7205609 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (h1). Qed.
Lemma lem7205610 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (SYM (@lem7205609 _131408 h1)). Qed.
Lemma lem7205611 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (h1). Qed.
Lemma lem7205612 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (SYM (@lem7205611 _131408 h1)). Qed.
Lemma lem7205613 {_131408 : Type'} : ((@sum _131408) = (@iterate real _131408 real_add)) = ((@iterate real _131408 real_add) = (@sum _131408)).
Proof. exact (prop_ext (fun h1 : (@sum _131408) = (@iterate real _131408 real_add) => @lem7205610 _131408 h1) (fun h1 : (@iterate real _131408 real_add) = (@sum _131408) => @lem7205612 _131408 h1)). Qed.
Lemma lem7205615 {A B : Type'} (op : type1400 B) : term7 A B op.
Proof. exact (@lem5811935 A B op). Qed.
Lemma lem7205616 {A B : Type'} (op : type1400 B) : (term7 A B op) = (term8 A B op).
Proof. exact (eq_refl (term7 A B op)). Qed.
Lemma lem7205619 {A B : Type'} (op : type1400 B) : term8 A B op.
Proof. exact (EQ_MP (@lem7205616 A B op) (@lem7205615 A B op)). Qed.
Lemma lem7205620 {A : Type'} (op : type1627) : term9 A op.
Proof. exact (@lem7205619 A real op). Qed.
Lemma lem7205621 {A : Type'} : term10 A.
Proof. exact (@lem7205620 A real_add). Qed.
Lemma lem7205622 {A : Type'} : term11 A.
Proof. exact (@lem7205621 A (@lem7067132)). Qed.
Lemma lem7205623 {A : Type'} (R : type1626) : term12 A R.
Proof. exact (@lem7205622 A R). Qed.
Lemma lem7205624 {A : Type'} (R : type1626) : (term12 A R) = (term13 A R).
Proof. exact (eq_refl (term12 A R)). Qed.
Lemma lem7205625 {A : Type'} (R : type1626) : term13 A R.
Proof. exact (EQ_MP (@lem7205624 A R) (@lem7205623 A R)). Qed.
Lemma lem7205626 {A : Type'} (P : Prop) : term14 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7205627 {A : Type'} (P : Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem7205628 {A : Type'} (P : Prop) : term15 A P.
Proof. exact (EQ_MP (@lem7205627 A P) (@lem7205626 A P)). Qed.
Lemma lem7205629 {A : Type'} (P : Prop) (Q : A -> Prop) : term16 A P Q.
Proof. exact (@lem7205628 A P Q). Qed.
Lemma lem7205630 {A : Type'} (P : Prop) (Q : A -> Prop) : (term16 A P Q) = ((term17 A P Q) = (term18 A P Q)).
Proof. exact (eq_refl (term16 A P Q)). Qed.
Lemma lem7205669 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7205670 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term21 A R f s g) = (term22 A R f s g).
Proof. exact (@lem7205669 (term23 R) (term24 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7205710 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7205711 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term26 R m m' n n') = (term27 R m m' n n').
Proof. exact (@lem7205710 (R m n) (R m' n') (term28 R m m' n n')). Qed.
Lemma lem7205716 (R : type1626) (m : real) (m' : real) (n : real) : (term29 R m m' n) = (term30 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7205711 R m m' n n')). Qed.
Lemma lem7205717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205718 (R : type1626) (m : real) (m' : real) (n : real) : (term31 R m m' n) = (term32 R m m' n).
Proof. exact (MK_COMB (@lem7205717) (@lem7205716 R m m' n)). Qed.
Lemma lem7205720 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7205630 A P Q) (@lem7205629 A P Q)). Qed.
Lemma lem7205721 (P : Prop) (Q : real -> Prop) : (term33 P Q) = (term34 P Q).
Proof. exact (@lem7205720 real P Q). Qed.
Lemma lem7205722 (R : type1626) (m : real) (m' : real) (n : real) : (term35 R m m' n) = (term36 R m m' n).
Proof. exact (@lem7205721 (R m n) (term37 R m m' n)). Qed.
Lemma lem7205723 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term38 R m m' n n') = (term39 R m m' n n').
Proof. exact (eq_refl (term38 R m m' n n')). Qed.
Lemma lem7205724 (R : type1626) (m : real) (n : real) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7205725 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term41 R m m' n n') = (term27 R m m' n n').
Proof. exact (MK_COMB (@lem7205724 R m n) (@lem7205723 R m m' n n')). Qed.
Lemma lem7205726 (R : type1626) (m : real) (m' : real) (n : real) : (term42 R m m' n) = (term30 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7205725 R m m' n n')). Qed.
Lemma lem7205727 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205728 (R : type1626) (m : real) (m' : real) (n : real) : (term35 R m m' n) = (term32 R m m' n).
Proof. exact (MK_COMB (@lem7205727) (@lem7205726 R m m' n)). Qed.
Lemma lem7205729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7205730 (R : type1626) (m : real) (m' : real) (n : real) : (term43 R m m' n) = (term44 R m m' n).
Proof. exact (MK_COMB (@lem7205729) (@lem7205728 R m m' n)). Qed.
Lemma lem7205731 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term38 R m m' n n') = (term39 R m m' n n').
Proof. exact (eq_refl (term38 R m m' n n')). Qed.
Lemma lem7205732 (R : type1626) (m : real) (m' : real) (n : real) : (term45 R m m' n) = (term37 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7205731 R m m' n n')). Qed.
Lemma lem7205733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205734 (R : type1626) (m : real) (m' : real) (n : real) : (term46 R m m' n) = (term47 R m m' n).
Proof. exact (MK_COMB (@lem7205733) (@lem7205732 R m m' n)). Qed.
Lemma lem7205735 (R : type1626) (m : real) (n : real) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7205736 (R : type1626) (m : real) (m' : real) (n : real) : (term36 R m m' n) = (term48 R m m' n).
Proof. exact (MK_COMB (@lem7205735 R m n) (@lem7205734 R m m' n)). Qed.
Lemma lem7205737 (R : type1626) (m : real) (m' : real) (n : real) : ((term35 R m m' n) = (term36 R m m' n)) = ((term32 R m m' n) = (term48 R m m' n)).
Proof. exact (MK_COMB (@lem7205730 R m m' n) (@lem7205736 R m m' n)). Qed.
Lemma lem7205738 (R : type1626) (m : real) (m' : real) (n : real) : (term32 R m m' n) = (term48 R m m' n).
Proof. exact (EQ_MP (@lem7205737 R m m' n) (@lem7205722 R m m' n)). Qed.
Lemma lem7205767 (R : type1626) (m : real) (m' : real) (n : real) : (term31 R m m' n) = (term48 R m m' n).
Proof. exact (TRANS (@lem7205718 R m m' n) (@lem7205738 R m m' n)). Qed.
Lemma lem7205768 (R : type1626) (m : real) (n : real) : (term49 R m n) = (term50 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7205767 R m m' n)). Qed.
Lemma lem7205769 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205770 (R : type1626) (m : real) (n : real) : (term51 R m n) = (term52 R m n).
Proof. exact (MK_COMB (@lem7205769) (@lem7205768 R m n)). Qed.
Lemma lem7205772 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7205630 A P Q) (@lem7205629 A P Q)). Qed.
Lemma lem7205773 (P : Prop) (Q : real -> Prop) : (term33 P Q) = (term34 P Q).
Proof. exact (@lem7205772 real P Q). Qed.
Lemma lem7205774 (R : type1626) (m : real) (n : real) : (term53 R m n) = (term54 R m n).
Proof. exact (@lem7205773 (R m n) (term55 R m n)). Qed.
Lemma lem7205775 (R : type1626) (m : real) (m' : real) (n : real) : (term56 R m n m') = (term47 R m m' n).
Proof. exact (eq_refl (term56 R m n m')). Qed.
Lemma lem7205776 (R : type1626) (m : real) (n : real) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7205777 (R : type1626) (m : real) (m' : real) (n : real) : (term57 R m n m') = (term48 R m m' n).
Proof. exact (MK_COMB (@lem7205776 R m n) (@lem7205775 R m m' n)). Qed.
Lemma lem7205778 (R : type1626) (m : real) (n : real) : (term58 R m n) = (term50 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7205777 R m m' n)). Qed.
Lemma lem7205779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205780 (R : type1626) (m : real) (n : real) : (term53 R m n) = (term52 R m n).
Proof. exact (MK_COMB (@lem7205779) (@lem7205778 R m n)). Qed.
Lemma lem7205781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7205782 (R : type1626) (m : real) (n : real) : (term59 R m n) = (term60 R m n).
Proof. exact (MK_COMB (@lem7205781) (@lem7205780 R m n)). Qed.
Lemma lem7205783 (R : type1626) (m : real) (m' : real) (n : real) : (term56 R m n m') = (term47 R m m' n).
Proof. exact (eq_refl (term56 R m n m')). Qed.
Lemma lem7205784 (R : type1626) (m : real) (n : real) : (term61 R m n) = (term55 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7205783 R m m' n)). Qed.
Lemma lem7205785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205786 (R : type1626) (m : real) (n : real) : (term62 R m n) = (term63 R m n).
Proof. exact (MK_COMB (@lem7205785) (@lem7205784 R m n)). Qed.
Lemma lem7205787 (R : type1626) (m : real) (n : real) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7205788 (R : type1626) (m : real) (n : real) : (term54 R m n) = (term64 R m n).
Proof. exact (MK_COMB (@lem7205787 R m n) (@lem7205786 R m n)). Qed.
Lemma lem7205789 (R : type1626) (m : real) (n : real) : ((term53 R m n) = (term54 R m n)) = ((term52 R m n) = (term64 R m n)).
Proof. exact (MK_COMB (@lem7205782 R m n) (@lem7205788 R m n)). Qed.
Lemma lem7205790 (R : type1626) (m : real) (n : real) : (term52 R m n) = (term64 R m n).
Proof. exact (EQ_MP (@lem7205789 R m n) (@lem7205774 R m n)). Qed.
Lemma lem7205823 (R : type1626) (m : real) (n : real) : (term51 R m n) = (term64 R m n).
Proof. exact (TRANS (@lem7205770 R m n) (@lem7205790 R m n)). Qed.
Lemma lem7205824 (R : type1626) (m : real) : (term65 R m) = (term66 R m).
Proof. exact (fun_ext (fun n : real => @lem7205823 R m n)). Qed.
Lemma lem7205825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205826 (R : type1626) (m : real) : (term67 R m) = (term68 R m).
Proof. exact (MK_COMB (@lem7205825) (@lem7205824 R m)). Qed.
Lemma lem7205851 (R : type1626) : (term69 R) = (term70 R).
Proof. exact (fun_ext (fun m : real => @lem7205826 R m)). Qed.
Lemma lem7205852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7205853 (R : type1626) : (term23 R) = (term71 R).
Proof. exact (MK_COMB (@lem7205852) (@lem7205851 R)). Qed.
Lemma lem7205858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7205859 (R : type1626) : (term72 R) = (term73 R).
Proof. exact (MK_COMB (@lem7205858) (@lem7205853 R)). Qed.
Lemma lem7205861 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7205862 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term74 A R f s g) = (term75 A R f s g).
Proof. exact (@lem7205861 (@FINITE A s) (term76 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7205866 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7205867 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term77 A R f s g) = (term78 A R f s g).
Proof. exact (@lem7205866 (term79 A s) (term80 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7205900 {A : Type'} (s : A -> Prop) : (term81 A s) = (term81 A s).
Proof. exact (eq_refl (term81 A s)). Qed.
Lemma lem7205901 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term75 A R f s g) = (term82 A R f s g).
Proof. exact (MK_COMB (@lem7205900 A s) (@lem7205867 A R f s g)). Qed.
Lemma lem7205904 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term74 A R f s g) = (term82 A R f s g).
Proof. exact (TRANS (@lem7205862 A R f s g) (@lem7205901 A R f s g)). Qed.
Lemma lem7205905 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term22 A R f s g) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7205859 R) (@lem7205904 A R f s g)). Qed.
Lemma lem7205908 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term21 A R f s g) = (term83 A R f s g).
Proof. exact (TRANS (@lem7205670 A R f s g) (@lem7205905 A R f s g)). Qed.
Lemma lem7205909 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term84 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7205908 A R f s g)). Qed.
Lemma lem7205910 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7205911 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term86 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7205910 A) (@lem7205909 A R f g)). Qed.
Lemma lem7205913 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7205630 A P Q) (@lem7205629 A P Q)). Qed.
Lemma lem7205914 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem7205913 (A -> Prop) P Q). Qed.
Lemma lem7205915 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term90 A R f g) = (term91 A R f g).
Proof. exact (@lem7205914 A (term71 R) (term92 A R f g)). Qed.
Lemma lem7205916 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term93 A R f g s) = (term82 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7205917 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7205918 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term94 A R f g s) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7205917 R) (@lem7205916 A R f s g)). Qed.
Lemma lem7205919 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term95 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7205918 A R f s g)). Qed.
Lemma lem7205920 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7205921 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term90 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7205920 A) (@lem7205919 A R f g)). Qed.
Lemma lem7205922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7205923 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term96 A R f g) = (term97 A R f g).
Proof. exact (MK_COMB (@lem7205922) (@lem7205921 A R f g)). Qed.
Lemma lem7205924 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term93 A R f g s) = (term82 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7205925 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term98 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7205924 A R f s g)). Qed.
Lemma lem7205926 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7205927 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term99 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7205926 A) (@lem7205925 A R f g)). Qed.
Lemma lem7205928 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7205929 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term91 A R f g) = (term101 A R f g).
Proof. exact (MK_COMB (@lem7205928 R) (@lem7205927 A R f g)). Qed.
Lemma lem7205930 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : ((term90 A R f g) = (term91 A R f g)) = ((term87 A R f g) = (term101 A R f g)).
Proof. exact (MK_COMB (@lem7205923 A R f g) (@lem7205929 A R f g)). Qed.
Lemma lem7205931 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term87 A R f g) = (term101 A R f g).
Proof. exact (EQ_MP (@lem7205930 A R f g) (@lem7205915 A R f g)). Qed.
Lemma lem7206052 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term86 A R f g) = (term101 A R f g).
Proof. exact (TRANS (@lem7205911 A R f g) (@lem7205931 A R f g)). Qed.
Lemma lem7206053 {A : Type'} (R : type1626) (f : A -> real) : (term102 A R f) = (term103 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7206052 A R f g)). Qed.
Lemma lem7206054 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206055 {A : Type'} (R : type1626) (f : A -> real) : (term104 A R f) = (term105 A R f).
Proof. exact (MK_COMB (@lem7206054 A) (@lem7206053 A R f)). Qed.
Lemma lem7206057 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7205630 A P Q) (@lem7205629 A P Q)). Qed.
Lemma lem7206058 {A : Type'} (P : Prop) (Q : type716 A) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem7206057 (A -> real) P Q). Qed.
Lemma lem7206059 {A : Type'} (R : type1626) (f : A -> real) : (term108 A R f) = (term109 A R f).
Proof. exact (@lem7206058 A (term71 R) (term110 A R f)). Qed.
Lemma lem7206060 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term111 A R f g) = (term100 A R f g).
Proof. exact (eq_refl (term111 A R f g)). Qed.
Lemma lem7206061 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7206062 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term112 A R f g) = (term101 A R f g).
Proof. exact (MK_COMB (@lem7206061 R) (@lem7206060 A R f g)). Qed.
Lemma lem7206063 {A : Type'} (R : type1626) (f : A -> real) : (term113 A R f) = (term103 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7206062 A R f g)). Qed.
Lemma lem7206064 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206065 {A : Type'} (R : type1626) (f : A -> real) : (term108 A R f) = (term105 A R f).
Proof. exact (MK_COMB (@lem7206064 A) (@lem7206063 A R f)). Qed.
Lemma lem7206066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7206067 {A : Type'} (R : type1626) (f : A -> real) : (term114 A R f) = (term115 A R f).
Proof. exact (MK_COMB (@lem7206066) (@lem7206065 A R f)). Qed.
Lemma lem7206068 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term111 A R f g) = (term100 A R f g).
Proof. exact (eq_refl (term111 A R f g)). Qed.
Lemma lem7206069 {A : Type'} (R : type1626) (f : A -> real) : (term116 A R f) = (term110 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7206068 A R f g)). Qed.
Lemma lem7206070 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206071 {A : Type'} (R : type1626) (f : A -> real) : (term117 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7206070 A) (@lem7206069 A R f)). Qed.
Lemma lem7206072 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7206073 {A : Type'} (R : type1626) (f : A -> real) : (term109 A R f) = (term119 A R f).
Proof. exact (MK_COMB (@lem7206072 R) (@lem7206071 A R f)). Qed.
Lemma lem7206074 {A : Type'} (R : type1626) (f : A -> real) : ((term108 A R f) = (term109 A R f)) = ((term105 A R f) = (term119 A R f)).
Proof. exact (MK_COMB (@lem7206067 A R f) (@lem7206073 A R f)). Qed.
Lemma lem7206075 {A : Type'} (R : type1626) (f : A -> real) : (term105 A R f) = (term119 A R f).
Proof. exact (EQ_MP (@lem7206074 A R f) (@lem7206059 A R f)). Qed.
Lemma lem7206200 {A : Type'} (R : type1626) (f : A -> real) : (term104 A R f) = (term119 A R f).
Proof. exact (TRANS (@lem7206055 A R f) (@lem7206075 A R f)). Qed.
Lemma lem7206201 {A : Type'} (R : type1626) : (term120 A R) = (term121 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7206200 A R f)). Qed.
Lemma lem7206202 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206203 {A : Type'} (R : type1626) : (term122 A R) = (term123 A R).
Proof. exact (MK_COMB (@lem7206202 A) (@lem7206201 A R)). Qed.
Lemma lem7206205 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7205630 A P Q) (@lem7205629 A P Q)). Qed.
Lemma lem7206206 {A : Type'} (P : Prop) (Q : type716 A) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem7206205 (A -> real) P Q). Qed.
Lemma lem7206207 {A : Type'} (R : type1626) : (term124 A R) = (term125 A R).
Proof. exact (@lem7206206 A (term71 R) (term126 A R)). Qed.
Lemma lem7206208 {A : Type'} (R : type1626) (f : A -> real) : (term127 A R f) = (term118 A R f).
Proof. exact (eq_refl (term127 A R f)). Qed.
Lemma lem7206209 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7206210 {A : Type'} (R : type1626) (f : A -> real) : (term128 A R f) = (term119 A R f).
Proof. exact (MK_COMB (@lem7206209 R) (@lem7206208 A R f)). Qed.
Lemma lem7206211 {A : Type'} (R : type1626) : (term129 A R) = (term121 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7206210 A R f)). Qed.
Lemma lem7206212 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206213 {A : Type'} (R : type1626) : (term124 A R) = (term123 A R).
Proof. exact (MK_COMB (@lem7206212 A) (@lem7206211 A R)). Qed.
Lemma lem7206214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7206215 {A : Type'} (R : type1626) : (term130 A R) = (term131 A R).
Proof. exact (MK_COMB (@lem7206214) (@lem7206213 A R)). Qed.
Lemma lem7206216 {A : Type'} (R : type1626) (f : A -> real) : (term127 A R f) = (term118 A R f).
Proof. exact (eq_refl (term127 A R f)). Qed.
Lemma lem7206217 {A : Type'} (R : type1626) : (term132 A R) = (term126 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7206216 A R f)). Qed.
Lemma lem7206218 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206219 {A : Type'} (R : type1626) : (term133 A R) = (term134 A R).
Proof. exact (MK_COMB (@lem7206218 A) (@lem7206217 A R)). Qed.
Lemma lem7206220 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7206221 {A : Type'} (R : type1626) : (term125 A R) = (term135 A R).
Proof. exact (MK_COMB (@lem7206220 R) (@lem7206219 A R)). Qed.
Lemma lem7206222 {A : Type'} (R : type1626) : ((term124 A R) = (term125 A R)) = ((term123 A R) = (term135 A R)).
Proof. exact (MK_COMB (@lem7206215 A R) (@lem7206221 A R)). Qed.
Lemma lem7206223 {A : Type'} (R : type1626) : (term123 A R) = (term135 A R).
Proof. exact (EQ_MP (@lem7206222 A R) (@lem7206207 A R)). Qed.
Lemma lem7206352 {A : Type'} (R : type1626) : (term122 A R) = (term135 A R).
Proof. exact (TRANS (@lem7206203 A R) (@lem7206223 A R)). Qed.
Lemma lem7206353 {A : Type'} : (term136 A) = (term137 A).
Proof. exact (fun_ext (fun R : type1626 => @lem7206352 A R)). Qed.
Lemma lem7206354 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem7206355 {A : Type'} : (term138 A) = (term139 A).
Proof. exact (MK_COMB (@lem7206354) (@lem7206353 A)). Qed.
Lemma lem7206380 {A : Type'} : (term139 A) = (term138 A).
Proof. exact (SYM (@lem7206355 A)). Qed.
Lemma lem7206381 (R : type1626) (h1 : term71 R) : term71 R.
Proof. exact (h1). Qed.
Lemma lem7206441 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7205613 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7206442 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7206441 A). Qed.
Lemma lem7206443 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7206444 {A : Type'} (s : A -> Prop) : (@iterate real A real_add s) = (@sum A s).
Proof. exact (MK_COMB (@lem7206442 A) (@lem7206443 A s)). Qed.
Lemma lem7206445 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7206446 {A : Type'} (s : A -> Prop) (f : A -> real) : (@iterate real A real_add s f) = (@sum A s f).
Proof. exact (MK_COMB (@lem7206444 A s) (@lem7206445 A f)). Qed.
Lemma lem7206447 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7206448 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term140 A R s f) = (term141 A R s f).
Proof. exact (MK_COMB (@lem7206447 R) (@lem7206446 A s f)). Qed.
Lemma lem7206450 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7205613 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7206451 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7206450 A). Qed.
Lemma lem7206452 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7206453 {A : Type'} (s : A -> Prop) : (@iterate real A real_add s) = (@sum A s).
Proof. exact (MK_COMB (@lem7206451 A) (@lem7206452 A s)). Qed.
Lemma lem7206454 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7206455 {A : Type'} (s : A -> Prop) (g : A -> real) : (@iterate real A real_add s g) = (@sum A s g).
Proof. exact (MK_COMB (@lem7206453 A s) (@lem7206454 A g)). Qed.
Lemma lem7206456 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term142 A R f s g) = (term25 A R f s g).
Proof. exact (MK_COMB (@lem7206448 A R s f) (@lem7206455 A s g)). Qed.
Lemma lem7206457 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term143 A s R f g) = (term143 A s R f g).
Proof. exact (eq_refl (term143 A s R f g)). Qed.
Lemma lem7206458 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term144 A R f s g) = (term74 A R f s g).
Proof. exact (MK_COMB (@lem7206457 A s R f g) (@lem7206456 A R f s g)). Qed.
Lemma lem7206461 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term145 A R f g) = (term146 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7206458 A R f s g)). Qed.
Lemma lem7206462 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7206463 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term147 A R f g) = (term148 A R f g).
Proof. exact (MK_COMB (@lem7206462 A) (@lem7206461 A R f g)). Qed.
Lemma lem7206468 {A : Type'} (R : type1626) (f : A -> real) : (term149 A R f) = (term150 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7206463 A R f g)). Qed.
Lemma lem7206469 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206470 {A : Type'} (R : type1626) (f : A -> real) : (term151 A R f) = (term152 A R f).
Proof. exact (MK_COMB (@lem7206469 A) (@lem7206468 A R f)). Qed.
Lemma lem7206475 {A : Type'} (R : type1626) : (term153 A R) = (term154 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7206470 A R f)). Qed.
Lemma lem7206476 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206477 {A : Type'} (R : type1626) : (term155 A R) = (term156 A R).
Proof. exact (MK_COMB (@lem7206476 A) (@lem7206475 A R)). Qed.
Lemma lem7206482 (R : type1626) : (term157 R) = (term157 R).
Proof. exact (eq_refl (term157 R)). Qed.
Lemma lem7206483 {A : Type'} (R : type1626) : (term13 A R) = (term158 A R).
Proof. exact (MK_COMB (@lem7206482 R) (@lem7206477 A R)). Qed.
Lemma lem7206486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7206487 {A : Type'} (R : type1626) : (term159 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7206486) (@lem7206483 A R)). Qed.
Lemma lem7206514 {A : Type'} (R : type1626) : (term134 A R) = (term134 A R).
Proof. exact (eq_refl (term134 A R)). Qed.
Lemma lem7206515 {A : Type'} (R : type1626) : (term161 A R) = (term162 A R).
Proof. exact (MK_COMB (@lem7206487 A R) (@lem7206514 A R)). Qed.
Lemma lem7206518 {A : Type'} (R : type1626) : (term162 A R) = (term161 A R).
Proof. exact (SYM (@lem7206515 A R)). Qed.
Lemma lem7206520 (p : Prop) : p = (term163 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7206521 {A : Type'} (R : type1626) : (term162 A R) = (term164 A R).
Proof. exact (@lem7206520 (term162 A R)). Qed.
Lemma lem7206522 {A : Type'} (R : type1626) : (term164 A R) = (term162 A R).
Proof. exact (SYM (@lem7206521 A R)). Qed.
Lemma lem7206523 {A : Type'} (R : type1626) (h1 : term165 A R) : term165 A R.
Proof. exact (h1). Qed.
Lemma lem7206526 {A : Type'} (R : type1626) (h1 : term166 A R) : term166 A R.
Proof. exact (h1). Qed.
Lemma lem7206527 {A : Type'} (R : type1626) : term167 A R.
Proof. exact (fun h0 : term166 A R => @lem7206526 A R h0). Qed.
Lemma lem7206528 {A : Type'} (R : type1626) (h1 : term167 A R) : term167 A R.
Proof. exact (h1). Qed.
Lemma lem7206529 {A : Type'} (R : type1626) (h1 : term166 A R) : term166 A R.
Proof. exact (h1). Qed.
Lemma lem7206530 {A : Type'} (R : type1626) (h1 : term166 A R) (h2 : term167 A R) : term166 A R.
Proof. exact (@lem7206528 A R h2 (@lem7206529 A R h1)). Qed.
Lemma lem7206531 {A : Type'} (R : type1626) (h1 : term166 A R) : term168 A R.
Proof. exact (fun h0 : term167 A R => @lem7206530 A R h1 h0). Qed.
Lemma lem7206532 {A : Type'} (R : type1626) (h1 : term167 A R) : term167 A R.
Proof. exact (h1). Qed.
Lemma lem7206533 {A : Type'} (R : type1626) (h1 : term166 A R) (h2 : term167 A R) : term166 A R.
Proof. exact (@lem7206531 A R h1 (@lem7206532 A R h2)). Qed.
Lemma lem7206534 {A : Type'} (R : type1626) (h1 : term167 A R) : term167 A R.
Proof. exact (fun h0 : term166 A R => @lem7206533 A R h0 h1). Qed.
Lemma lem7206535 {A : Type'} (R : type1626) : term169 A R.
Proof. exact (fun h0 : term167 A R => @lem7206534 A R h0). Qed.
Lemma lem7206538 {A : Type'} (R : type1626) : term167 A R.
Proof. exact (@lem7206535 A R (@lem7206527 A R)). Qed.
Lemma lem7206539 {A : Type'} (R : type1626) : term167 A R.
Proof. exact (@lem7206538 A R). Qed.
Lemma lem7206567 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7206568 {A : Type'} (R : type1626) : (term164 A R) = (term170 A R).
Proof. exact (@lem7206567 (term165 A R)). Qed.
Lemma lem7206570 (t : Prop) : (term171 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7206571 {A : Type'} (R : type1626) : (term170 A R) = (term162 A R).
Proof. exact (@lem7206570 (term162 A R)). Qed.
Lemma lem7206574 {A : Type'} (R : type1626) : (term164 A R) = (term162 A R).
Proof. exact (TRANS (@lem7206568 A R) (@lem7206571 A R)). Qed.
Lemma lem7206645 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7206646 {A : Type'} (R : type1626) : (term166 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7206645 R) (@lem7206574 A R)). Qed.
Lemma lem7206649 {A : Type'} : (term173 A) = (term174 A).
Proof. exact (fun_ext (fun R : type1626 => @lem7206646 A R)). Qed.
Lemma lem7206650 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem7206659 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (MK_COMB (@lem7206650) (@lem7206649 A)). Qed.
Lemma lem7206660 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7206665 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term177 A s R f g x) = (term177 A s R f g x).
Proof. exact (eq_refl (term177 A s R f g x)). Qed.
Lemma lem7206666 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term178 A s R f g) = (term178 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7206665 A s R f g x)). Qed.
Lemma lem7206667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7206668 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7206667 A) (@lem7206666 A s R f g)). Qed.
Lemma lem7206669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7206670 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term179 A s R f g) = (term179 A s R f g).
Proof. exact (MK_COMB (@lem7206669) (@lem7206668 A s R f g)). Qed.
Lemma lem7206671 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term180 A R f s g) = (term180 A R f s g).
Proof. exact (MK_COMB (@lem7206670 A s R f g) (@lem7206660 A R f s g)). Qed.
Lemma lem7206676 {A : Type'} (s : A -> Prop) : (term181 A s) = (term181 A s).
Proof. exact (eq_refl (term181 A s)). Qed.
Lemma lem7206677 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term78 A R f s g) = (term78 A R f s g).
Proof. exact (MK_COMB (@lem7206676 A s) (@lem7206671 A R f s g)). Qed.
Lemma lem7206680 {A : Type'} (s : A -> Prop) : (term81 A s) = (term81 A s).
Proof. exact (eq_refl (term81 A s)). Qed.
Lemma lem7206681 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term82 A R f s g) = (term82 A R f s g).
Proof. exact (MK_COMB (@lem7206680 A s) (@lem7206677 A R f s g)). Qed.
Lemma lem7206682 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term92 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7206681 A R f s g)). Qed.
Lemma lem7206683 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7206684 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term100 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7206683 A) (@lem7206682 A R f g)). Qed.
Lemma lem7206685 {A : Type'} (R : type1626) (f : A -> real) : (term110 A R f) = (term110 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7206684 A R f g)). Qed.
Lemma lem7206686 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206687 {A : Type'} (R : type1626) (f : A -> real) : (term118 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7206686 A) (@lem7206685 A R f)). Qed.
Lemma lem7206688 {A : Type'} (R : type1626) : (term126 A R) = (term126 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7206687 A R f)). Qed.
Lemma lem7206689 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206690 {A : Type'} (R : type1626) : (term134 A R) = (term134 A R).
Proof. exact (MK_COMB (@lem7206689 A) (@lem7206688 A R)). Qed.
Lemma lem7206691 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7206696 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term177 A s R f g x) = (term177 A s R f g x).
Proof. exact (eq_refl (term177 A s R f g x)). Qed.
Lemma lem7206697 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term178 A s R f g) = (term178 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7206696 A s R f g x)). Qed.
Lemma lem7206698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7206699 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7206698 A) (@lem7206697 A s R f g)). Qed.
Lemma lem7206704 {A : Type'} (s : A -> Prop) : (term182 A s) = (term182 A s).
Proof. exact (eq_refl (term182 A s)). Qed.
Lemma lem7206705 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term76 A s R f g) = (term76 A s R f g).
Proof. exact (MK_COMB (@lem7206704 A s) (@lem7206699 A s R f g)). Qed.
Lemma lem7206708 {A : Type'} (s : A -> Prop) : (term183 A s) = (term183 A s).
Proof. exact (eq_refl (term183 A s)). Qed.
Lemma lem7206709 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term24 A s R f g) = (term24 A s R f g).
Proof. exact (MK_COMB (@lem7206708 A s) (@lem7206705 A s R f g)). Qed.
Lemma lem7206710 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7206711 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term143 A s R f g) = (term143 A s R f g).
Proof. exact (MK_COMB (@lem7206710) (@lem7206709 A s R f g)). Qed.
Lemma lem7206712 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term74 A R f s g) = (term74 A R f s g).
Proof. exact (MK_COMB (@lem7206711 A s R f g) (@lem7206691 A R f s g)). Qed.
Lemma lem7206713 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term146 A R f g) = (term146 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7206712 A R f s g)). Qed.
Lemma lem7206714 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7206715 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term148 A R f g) = (term148 A R f g).
Proof. exact (MK_COMB (@lem7206714 A) (@lem7206713 A R f g)). Qed.
Lemma lem7206716 {A : Type'} (R : type1626) (f : A -> real) : (term150 A R f) = (term150 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7206715 A R f g)). Qed.
Lemma lem7206717 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206718 {A : Type'} (R : type1626) (f : A -> real) : (term152 A R f) = (term152 A R f).
Proof. exact (MK_COMB (@lem7206717 A) (@lem7206716 A R f)). Qed.
Lemma lem7206719 {A : Type'} (R : type1626) : (term154 A R) = (term154 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7206718 A R f)). Qed.
Lemma lem7206720 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7206721 {A : Type'} (R : type1626) : (term156 A R) = (term156 A R).
Proof. exact (MK_COMB (@lem7206720 A) (@lem7206719 A R)). Qed.
Lemma lem7206730 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term26 R x1 y1 x2 y2) = (term26 R x1 y1 x2 y2).
Proof. exact (eq_refl (term26 R x1 y1 x2 y2)). Qed.
Lemma lem7206731 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term29 R x1 y1 x2) = (term29 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : real => @lem7206730 R x1 y1 x2 y2)). Qed.
Lemma lem7206732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206733 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term31 R x1 y1 x2) = (term31 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7206732) (@lem7206731 R x1 y1 x2)). Qed.
Lemma lem7206734 (R : type1626) (x1 : real) (y1 : real) : (term184 R x1 y1) = (term184 R x1 y1).
Proof. exact (fun_ext (fun x2 : real => @lem7206733 R x1 y1 x2)). Qed.
Lemma lem7206735 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206736 (R : type1626) (x1 : real) (y1 : real) : (term185 R x1 y1) = (term185 R x1 y1).
Proof. exact (MK_COMB (@lem7206735) (@lem7206734 R x1 y1)). Qed.
Lemma lem7206737 (R : type1626) (x1 : real) : (term186 R x1) = (term186 R x1).
Proof. exact (fun_ext (fun y1 : real => @lem7206736 R x1 y1)). Qed.
Lemma lem7206738 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206739 (R : type1626) (x1 : real) : (term187 R x1) = (term187 R x1).
Proof. exact (MK_COMB (@lem7206738) (@lem7206737 R x1)). Qed.
Lemma lem7206740 (R : type1626) : (term188 R) = (term188 R).
Proof. exact (fun_ext (fun x1 : real => @lem7206739 R x1)). Qed.
Lemma lem7206741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206742 (R : type1626) : (term189 R) = (term189 R).
Proof. exact (MK_COMB (@lem7206741) (@lem7206740 R)). Qed.
Lemma lem7206743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7206744 (R : type1626) : (term157 R) = (term157 R).
Proof. exact (MK_COMB (@lem7206743) (@lem7206742 R)). Qed.
Lemma lem7206745 {A : Type'} (R : type1626) : (term158 A R) = (term158 A R).
Proof. exact (MK_COMB (@lem7206744 R) (@lem7206721 A R)). Qed.
Lemma lem7206746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7206747 {A : Type'} (R : type1626) : (term160 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7206746) (@lem7206745 A R)). Qed.
Lemma lem7206748 {A : Type'} (R : type1626) : (term162 A R) = (term162 A R).
Proof. exact (MK_COMB (@lem7206747 A R) (@lem7206690 A R)). Qed.
Lemma lem7206753 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term39 R m m' n n') = (term39 R m m' n n').
Proof. exact (eq_refl (term39 R m m' n n')). Qed.
Lemma lem7206754 (R : type1626) (m : real) (m' : real) (n : real) : (term37 R m m' n) = (term37 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7206753 R m m' n n')). Qed.
Lemma lem7206755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206756 (R : type1626) (m : real) (m' : real) (n : real) : (term47 R m m' n) = (term47 R m m' n).
Proof. exact (MK_COMB (@lem7206755) (@lem7206754 R m m' n)). Qed.
Lemma lem7206757 (R : type1626) (m : real) (n : real) : (term55 R m n) = (term55 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7206756 R m m' n)). Qed.
Lemma lem7206758 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206759 (R : type1626) (m : real) (n : real) : (term63 R m n) = (term63 R m n).
Proof. exact (MK_COMB (@lem7206758) (@lem7206757 R m n)). Qed.
Lemma lem7206762 (R : type1626) (m : real) (n : real) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7206763 (R : type1626) (m : real) (n : real) : (term64 R m n) = (term64 R m n).
Proof. exact (MK_COMB (@lem7206762 R m n) (@lem7206759 R m n)). Qed.
Lemma lem7206764 (R : type1626) (m : real) : (term66 R m) = (term66 R m).
Proof. exact (fun_ext (fun n : real => @lem7206763 R m n)). Qed.
Lemma lem7206765 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206766 (R : type1626) (m : real) : (term68 R m) = (term68 R m).
Proof. exact (MK_COMB (@lem7206765) (@lem7206764 R m)). Qed.
Lemma lem7206767 (R : type1626) : (term70 R) = (term70 R).
Proof. exact (fun_ext (fun m : real => @lem7206766 R m)). Qed.
Lemma lem7206768 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206769 (R : type1626) : (term71 R) = (term71 R).
Proof. exact (MK_COMB (@lem7206768) (@lem7206767 R)). Qed.
Lemma lem7206770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7206771 (R : type1626) : (term73 R) = (term73 R).
Proof. exact (MK_COMB (@lem7206770) (@lem7206769 R)). Qed.
Lemma lem7206772 {A : Type'} (R : type1626) : (term172 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7206771 R) (@lem7206748 A R)). Qed.
Lemma lem7206773 {A : Type'} : (term174 A) = (term174 A).
Proof. exact (fun_ext (fun R : type1626 => @lem7206772 A R)). Qed.
Lemma lem7206774 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem7206775 {A : Type'} : (term176 A) = (term176 A).
Proof. exact (MK_COMB (@lem7206774) (@lem7206773 A)). Qed.
Lemma lem7206910 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (TRANS (@lem7206659 A) (@lem7206775 A)). Qed.
Lemma lem7206911 {A : Type'} : (term176 A) = (term175 A).
Proof. exact (SYM (@lem7206910 A)). Qed.
Lemma lem7206912 (R : type1626) (h1 : term71 R) : term71 R.
Proof. exact (h1). Qed.
Lemma lem7206913 {A : Type'} (R : type1626) (h1 : term158 A R) : term158 A R.
Proof. exact (h1). Qed.
Lemma lem7206916 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term80 A s R f g.
Proof. exact (h1). Qed.
Lemma lem7206918 (p : Prop) : p = (term163 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7206919 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term190 A R f s g).
Proof. exact (@lem7206918 (term25 A R f s g)). Qed.
Lemma lem7206920 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term190 A R f s g) = (term25 A R f s g).
Proof. exact (SYM (@lem7206919 A R f s g)). Qed.
Lemma lem7206921 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term191 A R f s g) : term191 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7206929 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term39 R m m' n n') = (term192 R m m' n n').
Proof. exact (@lem17265 (R m' n') (term28 R m m' n n')). Qed.
Lemma lem7206930 (R : type1626) (m : real) (m' : real) (n : real) : (term37 R m m' n) = (term193 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7206929 R m m' n n')). Qed.
Lemma lem7206931 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206932 (R : type1626) (m : real) (m' : real) (n : real) : (term47 R m m' n) = (term194 R m m' n).
Proof. exact (MK_COMB (@lem7206931) (@lem7206930 R m m' n)). Qed.
Lemma lem7206933 (R : type1626) (m : real) (n : real) : (term55 R m n) = (term195 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7206932 R m m' n)). Qed.
Lemma lem7206934 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206935 (R : type1626) (m : real) (n : real) : (term63 R m n) = (term196 R m n).
Proof. exact (MK_COMB (@lem7206934) (@lem7206933 R m n)). Qed.
Lemma lem7206937 (R : type1626) (m : real) (n : real) : (term197 R m n) = (term197 R m n).
Proof. exact (eq_refl (term197 R m n)). Qed.
Lemma lem7206938 (R : type1626) (m : real) (n : real) : (term198 R m n) = (term199 R m n).
Proof. exact (MK_COMB (@lem7206937 R m n) (@lem7206935 R m n)). Qed.
Lemma lem7206939 (R : type1626) (m : real) (n : real) : (term64 R m n) = (term198 R m n).
Proof. exact (@lem17265 (R m n) (term63 R m n)). Qed.
Lemma lem7206940 (R : type1626) (m : real) (n : real) : (term64 R m n) = (term199 R m n).
Proof. exact (TRANS (@lem7206939 R m n) (@lem7206938 R m n)). Qed.
Lemma lem7206941 (R : type1626) (m : real) : (term66 R m) = (term200 R m).
Proof. exact (fun_ext (fun n : real => @lem7206940 R m n)). Qed.
Lemma lem7206942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7206943 (R : type1626) (m : real) : (term68 R m) = (term201 R m).
Proof. exact (MK_COMB (@lem7206942) (@lem7206941 R m)). Qed.
Lemma lem7206944 (R : type1626) : (term70 R) = (term202 R).
Proof. exact (fun_ext (fun m : real => @lem7206943 R m)). Qed.
Lemma lem7206945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7207054 (R : type1626) : (term71 R) = (term203 R).
Proof. exact (MK_COMB (@lem7206945) (@lem7206944 R)). Qed.
Lemma lem7207055 (R : type1626) (h1 : term71 R) : term203 R.
Proof. exact (EQ_MP (@lem7207054 R) (@lem7206912 R h1)). Qed.
Lemma lem7207066 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term204 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (@lem17362 (term206 x1 x2 R y1 y2) (term28 R x1 y1 x2 y2)). Qed.
Lemma lem7207067 (P : real -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7207068 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term209 R x1 y1 x2) = (term210 R x1 y1 x2).
Proof. exact (@lem7207067 (term29 R x1 y1 x2)). Qed.
Lemma lem7207069 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term211 R x1 y1 x2 y2) = (term26 R x1 y1 x2 y2).
Proof. exact (eq_refl (term211 R x1 y1 x2 y2)). Qed.
Lemma lem7207070 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207071 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term212 R x1 y1 x2 y2) = (term204 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7207070) (@lem7207069 R x1 y1 x2 y2)). Qed.
Lemma lem7207072 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term212 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7207071 R x1 y1 x2 y2) (@lem7207066 R x1 y1 x2 y2)). Qed.
Lemma lem7207073 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term213 R x1 y1 x2) = (term214 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : real => @lem7207072 R x1 y1 x2 y2)). Qed.
Lemma lem7207074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207075 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term210 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7207074) (@lem7207073 R x1 y1 x2)). Qed.
Lemma lem7207076 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term209 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (TRANS (@lem7207068 R x1 y1 x2) (@lem7207075 R x1 y1 x2)). Qed.
Lemma lem7207077 (P : real -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7207078 (R : type1626) (x1 : real) (y1 : real) : (term216 R x1 y1) = (term217 R x1 y1).
Proof. exact (@lem7207077 (term184 R x1 y1)). Qed.
Lemma lem7207079 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term218 R x1 y1 x2) = (term31 R x1 y1 x2).
Proof. exact (eq_refl (term218 R x1 y1 x2)). Qed.
Lemma lem7207080 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207081 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term219 R x1 y1 x2) = (term209 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7207080) (@lem7207079 R x1 y1 x2)). Qed.
Lemma lem7207082 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term219 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (TRANS (@lem7207081 R x1 y1 x2) (@lem7207076 R x1 y1 x2)). Qed.
Lemma lem7207083 (R : type1626) (x1 : real) (y1 : real) : (term220 R x1 y1) = (term221 R x1 y1).
Proof. exact (fun_ext (fun x2 : real => @lem7207082 R x1 y1 x2)). Qed.
Lemma lem7207084 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207085 (R : type1626) (x1 : real) (y1 : real) : (term217 R x1 y1) = (term222 R x1 y1).
Proof. exact (MK_COMB (@lem7207084) (@lem7207083 R x1 y1)). Qed.
Lemma lem7207086 (R : type1626) (x1 : real) (y1 : real) : (term216 R x1 y1) = (term222 R x1 y1).
Proof. exact (TRANS (@lem7207078 R x1 y1) (@lem7207085 R x1 y1)). Qed.
Lemma lem7207087 (P : real -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7207088 (R : type1626) (x1 : real) : (term223 R x1) = (term224 R x1).
Proof. exact (@lem7207087 (term186 R x1)). Qed.
Lemma lem7207089 (R : type1626) (x1 : real) (y1 : real) : (term225 R x1 y1) = (term185 R x1 y1).
Proof. exact (eq_refl (term225 R x1 y1)). Qed.
Lemma lem7207090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207091 (R : type1626) (x1 : real) (y1 : real) : (term226 R x1 y1) = (term216 R x1 y1).
Proof. exact (MK_COMB (@lem7207090) (@lem7207089 R x1 y1)). Qed.
Lemma lem7207092 (R : type1626) (x1 : real) (y1 : real) : (term226 R x1 y1) = (term222 R x1 y1).
Proof. exact (TRANS (@lem7207091 R x1 y1) (@lem7207086 R x1 y1)). Qed.
Lemma lem7207093 (R : type1626) (x1 : real) : (term227 R x1) = (term228 R x1).
Proof. exact (fun_ext (fun y1 : real => @lem7207092 R x1 y1)). Qed.
Lemma lem7207094 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207095 (R : type1626) (x1 : real) : (term224 R x1) = (term229 R x1).
Proof. exact (MK_COMB (@lem7207094) (@lem7207093 R x1)). Qed.
Lemma lem7207096 (R : type1626) (x1 : real) : (term223 R x1) = (term229 R x1).
Proof. exact (TRANS (@lem7207088 R x1) (@lem7207095 R x1)). Qed.
Lemma lem7207097 (P : real -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7207098 (R : type1626) : (term230 R) = (term231 R).
Proof. exact (@lem7207097 (term188 R)). Qed.
Lemma lem7207099 (R : type1626) (x1 : real) : (term232 R x1) = (term187 R x1).
Proof. exact (eq_refl (term232 R x1)). Qed.
Lemma lem7207100 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207101 (R : type1626) (x1 : real) : (term233 R x1) = (term223 R x1).
Proof. exact (MK_COMB (@lem7207100) (@lem7207099 R x1)). Qed.
Lemma lem7207102 (R : type1626) (x1 : real) : (term233 R x1) = (term229 R x1).
Proof. exact (TRANS (@lem7207101 R x1) (@lem7207096 R x1)). Qed.
Lemma lem7207103 (R : type1626) : (term234 R) = (term235 R).
Proof. exact (fun_ext (fun x1 : real => @lem7207102 R x1)). Qed.
Lemma lem7207104 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207105 (R : type1626) : (term231 R) = (term236 R).
Proof. exact (MK_COMB (@lem7207104) (@lem7207103 R)). Qed.
Lemma lem7207106 (R : type1626) : (term230 R) = (term236 R).
Proof. exact (TRANS (@lem7207098 R) (@lem7207105 R)). Qed.
Lemma lem7207110 {A : Type'} (s : A -> Prop) : (term237 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem7207117 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term238 A s R f g x) = (term239 A s R f g x).
Proof. exact (@lem17362 (@IN A x s) (term240 A R f g x)). Qed.
Lemma lem7207118 {A : Type'} (P : A -> Prop) : (term241 A P) = (term242 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7207119 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term243 A s R f g) = (term244 A s R f g).
Proof. exact (@lem7207118 A (term178 A s R f g)). Qed.
Lemma lem7207120 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term245 A s R f g x) = (term177 A s R f g x).
Proof. exact (eq_refl (term245 A s R f g x)). Qed.
Lemma lem7207121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207122 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term246 A s R f g x) = (term238 A s R f g x).
Proof. exact (MK_COMB (@lem7207121) (@lem7207120 A s R f g x)). Qed.
Lemma lem7207123 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term246 A s R f g x) = (term239 A s R f g x).
Proof. exact (TRANS (@lem7207122 A s R f g x) (@lem7207117 A s R f g x)). Qed.
Lemma lem7207124 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term247 A s R f g) = (term248 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207123 A s R f g x)). Qed.
Lemma lem7207125 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207126 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term244 A s R f g) = (term249 A s R f g).
Proof. exact (MK_COMB (@lem7207125 A) (@lem7207124 A s R f g)). Qed.
Lemma lem7207127 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term243 A s R f g) = (term249 A s R f g).
Proof. exact (TRANS (@lem7207119 A s R f g) (@lem7207126 A s R f g)). Qed.
Lemma lem7207128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207129 {A : Type'} (s : A -> Prop) : (term250 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem7207128) (@lem7207110 A s)). Qed.
Lemma lem7207130 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term252 A s R f g) = (term253 A s R f g).
Proof. exact (MK_COMB (@lem7207129 A s) (@lem7207127 A s R f g)). Qed.
Lemma lem7207131 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term254 A s R f g) = (term252 A s R f g).
Proof. exact (@lem17045 (term79 A s) (term80 A s R f g)). Qed.
Lemma lem7207132 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term254 A s R f g) = (term253 A s R f g).
Proof. exact (TRANS (@lem7207131 A s R f g) (@lem7207130 A s R f g)). Qed.
Lemma lem7207134 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7207135 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term256 A s R f g) = (term257 A s R f g).
Proof. exact (MK_COMB (@lem7207134 A s) (@lem7207132 A s R f g)). Qed.
Lemma lem7207136 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term258 A s R f g) = (term256 A s R f g).
Proof. exact (@lem17045 (@FINITE A s) (term76 A s R f g)). Qed.
Lemma lem7207137 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term258 A s R f g) = (term257 A s R f g).
Proof. exact (TRANS (@lem7207136 A s R f g) (@lem7207135 A s R f g)). Qed.
Lemma lem7207138 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7207139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207140 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term259 A s R f g) = (term260 A s R f g).
Proof. exact (MK_COMB (@lem7207139) (@lem7207137 A s R f g)). Qed.
Lemma lem7207141 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term261 A R f s g) = (term262 A R f s g).
Proof. exact (MK_COMB (@lem7207140 A s R f g) (@lem7207138 A R f s g)). Qed.
Lemma lem7207142 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term74 A R f s g) = (term261 A R f s g).
Proof. exact (@lem17265 (term24 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7207143 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term74 A R f s g) = (term262 A R f s g).
Proof. exact (TRANS (@lem7207142 A R f s g) (@lem7207141 A R f s g)). Qed.
Lemma lem7207144 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term146 A R f g) = (term263 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7207143 A R f s g)). Qed.
Lemma lem7207145 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7207146 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term148 A R f g) = (term264 A R f g).
Proof. exact (MK_COMB (@lem7207145 A) (@lem7207144 A R f g)). Qed.
Lemma lem7207147 {A : Type'} (R : type1626) (f : A -> real) : (term150 A R f) = (term265 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7207146 A R f g)). Qed.
Lemma lem7207148 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207149 {A : Type'} (R : type1626) (f : A -> real) : (term152 A R f) = (term266 A R f).
Proof. exact (MK_COMB (@lem7207148 A) (@lem7207147 A R f)). Qed.
Lemma lem7207150 {A : Type'} (R : type1626) : (term154 A R) = (term267 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7207149 A R f)). Qed.
Lemma lem7207151 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207152 {A : Type'} (R : type1626) : (term156 A R) = (term268 A R).
Proof. exact (MK_COMB (@lem7207151 A) (@lem7207150 A R)). Qed.
Lemma lem7207153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207154 (R : type1626) : (term269 R) = (term270 R).
Proof. exact (MK_COMB (@lem7207153) (@lem7207106 R)). Qed.
Lemma lem7207155 {A : Type'} (R : type1626) : (term271 A R) = (term272 A R).
Proof. exact (MK_COMB (@lem7207154 R) (@lem7207152 A R)). Qed.
Lemma lem7207156 {A : Type'} (R : type1626) : (term158 A R) = (term271 A R).
Proof. exact (@lem17265 (term189 R) (term156 A R)). Qed.
Lemma lem7207157 {A : Type'} (R : type1626) : (term158 A R) = (term272 A R).
Proof. exact (TRANS (@lem7207156 A R) (@lem7207155 A R)). Qed.
Lemma lem7207324 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7207325 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (@lem7207324 A P Q). Qed.
Lemma lem7207326 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term275 A s R f g) = (term276 A s R f g).
Proof. exact (@lem7207325 A (s = (@EMPTY A)) (term248 A s R f g)). Qed.
Lemma lem7207327 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term277 A s R f g x) = (term239 A s R f g x).
Proof. exact (eq_refl (term277 A s R f g x)). Qed.
Lemma lem7207328 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term278 A s R f g) = (term248 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207327 A s R f g x)). Qed.
Lemma lem7207329 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207330 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term279 A s R f g) = (term249 A s R f g).
Proof. exact (MK_COMB (@lem7207329 A) (@lem7207328 A s R f g)). Qed.
Lemma lem7207331 {A : Type'} (s : A -> Prop) : (term251 A s) = (term251 A s).
Proof. exact (eq_refl (term251 A s)). Qed.
Lemma lem7207332 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term275 A s R f g) = (term253 A s R f g).
Proof. exact (MK_COMB (@lem7207331 A s) (@lem7207330 A s R f g)). Qed.
Lemma lem7207333 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207334 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term280 A s R f g) = (term281 A s R f g).
Proof. exact (MK_COMB (@lem7207333) (@lem7207332 A s R f g)). Qed.
Lemma lem7207335 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term277 A s R f g x) = (term239 A s R f g x).
Proof. exact (eq_refl (term277 A s R f g x)). Qed.
Lemma lem7207336 {A : Type'} (s : A -> Prop) : (term251 A s) = (term251 A s).
Proof. exact (eq_refl (term251 A s)). Qed.
Lemma lem7207337 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term282 A s R f g x) = (term283 A s R f g x).
Proof. exact (MK_COMB (@lem7207336 A s) (@lem7207335 A s R f g x)). Qed.
Lemma lem7207338 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term284 A s R f g) = (term285 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207337 A s R f g x)). Qed.
Lemma lem7207339 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207340 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term276 A s R f g) = (term286 A s R f g).
Proof. exact (MK_COMB (@lem7207339 A) (@lem7207338 A s R f g)). Qed.
Lemma lem7207341 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : ((term275 A s R f g) = (term276 A s R f g)) = ((term253 A s R f g) = (term286 A s R f g)).
Proof. exact (MK_COMB (@lem7207334 A s R f g) (@lem7207340 A s R f g)). Qed.
Lemma lem7207342 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term253 A s R f g) = (term286 A s R f g).
Proof. exact (EQ_MP (@lem7207341 A s R f g) (@lem7207326 A s R f g)). Qed.
Lemma lem7207343 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7207344 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term257 A s R f g) = (term287 A s R f g).
Proof. exact (MK_COMB (@lem7207343 A s) (@lem7207342 A s R f g)). Qed.
Lemma lem7207346 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7207347 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (@lem7207346 A P Q). Qed.
Lemma lem7207348 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term288 A s R f g) = (term289 A s R f g).
Proof. exact (@lem7207347 A (term290 A s) (term285 A s R f g)). Qed.
Lemma lem7207349 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term291 A s R f g x) = (term283 A s R f g x).
Proof. exact (eq_refl (term291 A s R f g x)). Qed.
Lemma lem7207350 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term292 A s R f g) = (term285 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207349 A s R f g x)). Qed.
Lemma lem7207351 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207352 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term293 A s R f g) = (term286 A s R f g).
Proof. exact (MK_COMB (@lem7207351 A) (@lem7207350 A s R f g)). Qed.
Lemma lem7207353 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7207354 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term288 A s R f g) = (term287 A s R f g).
Proof. exact (MK_COMB (@lem7207353 A s) (@lem7207352 A s R f g)). Qed.
Lemma lem7207355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207356 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term294 A s R f g) = (term295 A s R f g).
Proof. exact (MK_COMB (@lem7207355) (@lem7207354 A s R f g)). Qed.
Lemma lem7207357 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term291 A s R f g x) = (term283 A s R f g x).
Proof. exact (eq_refl (term291 A s R f g x)). Qed.
Lemma lem7207358 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7207359 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term296 A s R f g x) = (term297 A s R f g x).
Proof. exact (MK_COMB (@lem7207358 A s) (@lem7207357 A s R f g x)). Qed.
Lemma lem7207360 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term298 A s R f g) = (term299 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207359 A s R f g x)). Qed.
Lemma lem7207361 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207362 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term289 A s R f g) = (term300 A s R f g).
Proof. exact (MK_COMB (@lem7207361 A) (@lem7207360 A s R f g)). Qed.
Lemma lem7207363 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : ((term288 A s R f g) = (term289 A s R f g)) = ((term287 A s R f g) = (term300 A s R f g)).
Proof. exact (MK_COMB (@lem7207356 A s R f g) (@lem7207362 A s R f g)). Qed.
Lemma lem7207364 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term287 A s R f g) = (term300 A s R f g).
Proof. exact (EQ_MP (@lem7207363 A s R f g) (@lem7207348 A s R f g)). Qed.
Lemma lem7207365 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term257 A s R f g) = (term300 A s R f g).
Proof. exact (TRANS (@lem7207344 A s R f g) (@lem7207364 A s R f g)). Qed.
Lemma lem7207366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207367 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term260 A s R f g) = (term301 A s R f g).
Proof. exact (MK_COMB (@lem7207366) (@lem7207365 A s R f g)). Qed.
Lemma lem7207368 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7207369 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term262 A R f s g) = (term302 A R f s g).
Proof. exact (MK_COMB (@lem7207367 A s R f g) (@lem7207368 A R f s g)). Qed.
Lemma lem7207371 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7207372 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (@lem7207371 A P Q). Qed.
Lemma lem7207373 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term305 A R f s g) = (term306 A R f s g).
Proof. exact (@lem7207372 A (term299 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7207374 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term307 A s R f g x) = (term297 A s R f g x).
Proof. exact (eq_refl (term307 A s R f g x)). Qed.
Lemma lem7207375 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term308 A s R f g) = (term299 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207374 A s R f g x)). Qed.
Lemma lem7207376 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207377 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term309 A s R f g) = (term300 A s R f g).
Proof. exact (MK_COMB (@lem7207376 A) (@lem7207375 A s R f g)). Qed.
Lemma lem7207378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207379 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term310 A s R f g) = (term301 A s R f g).
Proof. exact (MK_COMB (@lem7207378) (@lem7207377 A s R f g)). Qed.
Lemma lem7207380 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7207381 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term305 A R f s g) = (term302 A R f s g).
Proof. exact (MK_COMB (@lem7207379 A s R f g) (@lem7207380 A R f s g)). Qed.
Lemma lem7207382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207383 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term311 A R f s g) = (term312 A R f s g).
Proof. exact (MK_COMB (@lem7207382) (@lem7207381 A R f s g)). Qed.
Lemma lem7207384 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term307 A s R f g x) = (term297 A s R f g x).
Proof. exact (eq_refl (term307 A s R f g x)). Qed.
Lemma lem7207385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207386 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term313 A s R f g x) = (term314 A s R f g x).
Proof. exact (MK_COMB (@lem7207385) (@lem7207384 A s R f g x)). Qed.
Lemma lem7207387 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7207388 {A : Type'} (x : A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term315 A x R f s g) = (term316 A x R f s g).
Proof. exact (MK_COMB (@lem7207386 A s R f g x) (@lem7207387 A R f s g)). Qed.
Lemma lem7207389 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term317 A R f s g) = (term318 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7207388 A x R f s g)). Qed.
Lemma lem7207390 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207391 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term306 A R f s g) = (term319 A R f s g).
Proof. exact (MK_COMB (@lem7207390 A) (@lem7207389 A R f s g)). Qed.
Lemma lem7207392 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : ((term305 A R f s g) = (term306 A R f s g)) = ((term302 A R f s g) = (term319 A R f s g)).
Proof. exact (MK_COMB (@lem7207383 A R f s g) (@lem7207391 A R f s g)). Qed.
Lemma lem7207393 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term302 A R f s g) = (term319 A R f s g).
Proof. exact (EQ_MP (@lem7207392 A R f s g) (@lem7207373 A R f s g)). Qed.
Lemma lem7207394 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term262 A R f s g) = (term319 A R f s g).
Proof. exact (TRANS (@lem7207369 A R f s g) (@lem7207393 A R f s g)). Qed.
Lemma lem7207395 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term263 A R f g) = (term320 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7207394 A R f s g)). Qed.
Lemma lem7207396 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7207397 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term264 A R f g) = (term321 A R f g).
Proof. exact (MK_COMB (@lem7207396 A) (@lem7207395 A R f g)). Qed.
Lemma lem7207399 {A B : Type'} (P : type1413 A B) : (term322 A B P) = (term323 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7207400 {A : Type'} (P : type672 A) : (term324 A P) = (term325 A P).
Proof. exact (@lem7207399 (A -> Prop) A P). Qed.
Lemma lem7207401 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term326 A R f g) = (term327 A R f g).
Proof. exact (@lem7207400 A (term328 A R f g)). Qed.
Lemma lem7207402 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term329 A R f g s) = (term318 A R f s g).
Proof. exact (eq_refl (term329 A R f g s)). Qed.
Lemma lem7207403 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7207404 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (x : A) : (term330 A R f g s x) = (term331 A R f s g x).
Proof. exact (MK_COMB (@lem7207402 A R f s g) (@lem7207403 A x)). Qed.
Lemma lem7207405 {A : Type'} (x : A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term331 A R f s g x) = (term316 A x R f s g).
Proof. exact (eq_refl (term331 A R f s g x)). Qed.
Lemma lem7207406 {A : Type'} (x : A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term330 A R f g s x) = (term316 A x R f s g).
Proof. exact (TRANS (@lem7207404 A R f s g x) (@lem7207405 A x R f s g)). Qed.
Lemma lem7207407 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term332 A R f g s) = (term318 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7207406 A x R f s g)). Qed.
Lemma lem7207408 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7207409 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term333 A R f g s) = (term319 A R f s g).
Proof. exact (MK_COMB (@lem7207408 A) (@lem7207407 A R f s g)). Qed.
Lemma lem7207410 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term334 A R f g) = (term320 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7207409 A R f s g)). Qed.
Lemma lem7207411 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7207412 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term326 A R f g) = (term321 A R f g).
Proof. exact (MK_COMB (@lem7207411 A) (@lem7207410 A R f g)). Qed.
Lemma lem7207413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207414 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term335 A R f g) = (term336 A R f g).
Proof. exact (MK_COMB (@lem7207413) (@lem7207412 A R f g)). Qed.
Lemma lem7207415 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term329 A R f g s) = (term318 A R f s g).
Proof. exact (eq_refl (term329 A R f g s)). Qed.
Lemma lem7207416 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7207417 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : type684 A) (s : A -> Prop) : (term337 A R f g x s) = (term338 A R f g x s).
Proof. exact (MK_COMB (@lem7207415 A R f s g) (@lem7207416 A x s)). Qed.
Lemma lem7207418 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term338 A R f g x s) = (term339 A x R f s g).
Proof. exact (eq_refl (term338 A R f g x s)). Qed.
Lemma lem7207419 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term337 A R f g x s) = (term339 A x R f s g).
Proof. exact (TRANS (@lem7207417 A R f g x s) (@lem7207418 A x R f s g)). Qed.
Lemma lem7207420 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term340 A R f g x) = (term341 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7207419 A x R f s g)). Qed.
Lemma lem7207421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7207422 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term342 A R f g x) = (term343 A x R f g).
Proof. exact (MK_COMB (@lem7207421 A) (@lem7207420 A x R f g)). Qed.
Lemma lem7207423 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term344 A R f g) = (term345 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7207422 A x R f g)). Qed.
Lemma lem7207424 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7207425 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term327 A R f g) = (term346 A R f g).
Proof. exact (MK_COMB (@lem7207424 A) (@lem7207423 A R f g)). Qed.
Lemma lem7207426 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : ((term326 A R f g) = (term327 A R f g)) = ((term321 A R f g) = (term346 A R f g)).
Proof. exact (MK_COMB (@lem7207414 A R f g) (@lem7207425 A R f g)). Qed.
Lemma lem7207427 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term321 A R f g) = (term346 A R f g).
Proof. exact (EQ_MP (@lem7207426 A R f g) (@lem7207401 A R f g)). Qed.
Lemma lem7207428 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term264 A R f g) = (term346 A R f g).
Proof. exact (TRANS (@lem7207397 A R f g) (@lem7207427 A R f g)). Qed.
Lemma lem7207429 {A : Type'} (R : type1626) (f : A -> real) : (term265 A R f) = (term347 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7207428 A R f g)). Qed.
Lemma lem7207430 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207431 {A : Type'} (R : type1626) (f : A -> real) : (term266 A R f) = (term348 A R f).
Proof. exact (MK_COMB (@lem7207430 A) (@lem7207429 A R f)). Qed.
Lemma lem7207433 {A B : Type'} (P : type1413 A B) : (term322 A B P) = (term323 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7207434 {A : Type'} (P : type707 A) : (term349 A P) = (term350 A P).
Proof. exact (@lem7207433 (A -> real) (type684 A) P). Qed.
Lemma lem7207435 {A : Type'} (R : type1626) (f : A -> real) : (term351 A R f) = (term352 A R f).
Proof. exact (@lem7207434 A (term353 A R f)). Qed.
Lemma lem7207436 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term354 A R f g) = (term345 A R f g).
Proof. exact (eq_refl (term354 A R f g)). Qed.
Lemma lem7207437 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7207438 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : type684 A) : (term355 A R f g x) = (term356 A R f g x).
Proof. exact (MK_COMB (@lem7207436 A R f g) (@lem7207437 A x)). Qed.
Lemma lem7207439 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term356 A R f g x) = (term343 A x R f g).
Proof. exact (eq_refl (term356 A R f g x)). Qed.
Lemma lem7207440 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term355 A R f g x) = (term343 A x R f g).
Proof. exact (TRANS (@lem7207438 A R f g x) (@lem7207439 A x R f g)). Qed.
Lemma lem7207441 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term357 A R f g) = (term345 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7207440 A x R f g)). Qed.
Lemma lem7207442 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7207443 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term358 A R f g) = (term346 A R f g).
Proof. exact (MK_COMB (@lem7207442 A) (@lem7207441 A R f g)). Qed.
Lemma lem7207444 {A : Type'} (R : type1626) (f : A -> real) : (term359 A R f) = (term347 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7207443 A R f g)). Qed.
Lemma lem7207445 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207446 {A : Type'} (R : type1626) (f : A -> real) : (term351 A R f) = (term348 A R f).
Proof. exact (MK_COMB (@lem7207445 A) (@lem7207444 A R f)). Qed.
Lemma lem7207447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207448 {A : Type'} (R : type1626) (f : A -> real) : (term360 A R f) = (term361 A R f).
Proof. exact (MK_COMB (@lem7207447) (@lem7207446 A R f)). Qed.
Lemma lem7207449 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term354 A R f g) = (term345 A R f g).
Proof. exact (eq_refl (term354 A R f g)). Qed.
Lemma lem7207450 {A : Type'} (x : type710 A) (g : A -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7207451 {A : Type'} (R : type1626) (f : A -> real) (x : type710 A) (g : A -> real) : (term362 A R f x g) = (term363 A R f x g).
Proof. exact (MK_COMB (@lem7207449 A R f g) (@lem7207450 A x g)). Qed.
Lemma lem7207452 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) (g : A -> real) : (term363 A R f x g) = (term364 A x R f g).
Proof. exact (eq_refl (term363 A R f x g)). Qed.
Lemma lem7207453 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) (g : A -> real) : (term362 A R f x g) = (term364 A x R f g).
Proof. exact (TRANS (@lem7207451 A R f x g) (@lem7207452 A x R f g)). Qed.
Lemma lem7207454 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term365 A R f x) = (term366 A x R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7207453 A x R f g)). Qed.
Lemma lem7207455 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207456 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term367 A R f x) = (term368 A x R f).
Proof. exact (MK_COMB (@lem7207455 A) (@lem7207454 A x R f)). Qed.
Lemma lem7207457 {A : Type'} (R : type1626) (f : A -> real) : (term369 A R f) = (term370 A R f).
Proof. exact (fun_ext (fun x : type710 A => @lem7207456 A x R f)). Qed.
Lemma lem7207458 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7207459 {A : Type'} (R : type1626) (f : A -> real) : (term352 A R f) = (term371 A R f).
Proof. exact (MK_COMB (@lem7207458 A) (@lem7207457 A R f)). Qed.
Lemma lem7207460 {A : Type'} (R : type1626) (f : A -> real) : ((term351 A R f) = (term352 A R f)) = ((term348 A R f) = (term371 A R f)).
Proof. exact (MK_COMB (@lem7207448 A R f) (@lem7207459 A R f)). Qed.
Lemma lem7207461 {A : Type'} (R : type1626) (f : A -> real) : (term348 A R f) = (term371 A R f).
Proof. exact (EQ_MP (@lem7207460 A R f) (@lem7207435 A R f)). Qed.
Lemma lem7207462 {A : Type'} (R : type1626) (f : A -> real) : (term266 A R f) = (term371 A R f).
Proof. exact (TRANS (@lem7207431 A R f) (@lem7207461 A R f)). Qed.
Lemma lem7207463 {A : Type'} (R : type1626) : (term267 A R) = (term372 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7207462 A R f)). Qed.
Lemma lem7207464 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207465 {A : Type'} (R : type1626) : (term268 A R) = (term373 A R).
Proof. exact (MK_COMB (@lem7207464 A) (@lem7207463 A R)). Qed.
Lemma lem7207467 {A B : Type'} (P : type1413 A B) : (term322 A B P) = (term323 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7207468 {A : Type'} (P : type708 A) : (term374 A P) = (term375 A P).
Proof. exact (@lem7207467 (A -> real) (type710 A) P). Qed.
Lemma lem7207469 {A : Type'} (R : type1626) : (term376 A R) = (term377 A R).
Proof. exact (@lem7207468 A (term378 A R)). Qed.
Lemma lem7207470 {A : Type'} (R : type1626) (f : A -> real) : (term379 A R f) = (term370 A R f).
Proof. exact (eq_refl (term379 A R f)). Qed.
Lemma lem7207471 {A : Type'} (x : type710 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7207472 {A : Type'} (R : type1626) (f : A -> real) (x : type710 A) : (term380 A R f x) = (term381 A R f x).
Proof. exact (MK_COMB (@lem7207470 A R f) (@lem7207471 A x)). Qed.
Lemma lem7207473 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term381 A R f x) = (term368 A x R f).
Proof. exact (eq_refl (term381 A R f x)). Qed.
Lemma lem7207474 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term380 A R f x) = (term368 A x R f).
Proof. exact (TRANS (@lem7207472 A R f x) (@lem7207473 A x R f)). Qed.
Lemma lem7207475 {A : Type'} (R : type1626) (f : A -> real) : (term382 A R f) = (term370 A R f).
Proof. exact (fun_ext (fun x : type710 A => @lem7207474 A x R f)). Qed.
Lemma lem7207476 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7207477 {A : Type'} (R : type1626) (f : A -> real) : (term383 A R f) = (term371 A R f).
Proof. exact (MK_COMB (@lem7207476 A) (@lem7207475 A R f)). Qed.
Lemma lem7207478 {A : Type'} (R : type1626) : (term384 A R) = (term372 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7207477 A R f)). Qed.
Lemma lem7207479 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207480 {A : Type'} (R : type1626) : (term376 A R) = (term373 A R).
Proof. exact (MK_COMB (@lem7207479 A) (@lem7207478 A R)). Qed.
Lemma lem7207481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207482 {A : Type'} (R : type1626) : (term385 A R) = (term386 A R).
Proof. exact (MK_COMB (@lem7207481) (@lem7207480 A R)). Qed.
Lemma lem7207483 {A : Type'} (R : type1626) (f : A -> real) : (term379 A R f) = (term370 A R f).
Proof. exact (eq_refl (term379 A R f)). Qed.
Lemma lem7207484 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7207485 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) : (term387 A R x f) = (term388 A R x f).
Proof. exact (MK_COMB (@lem7207483 A R f) (@lem7207484 A x f)). Qed.
Lemma lem7207486 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term388 A R x f) = (term389 A x R f).
Proof. exact (eq_refl (term388 A R x f)). Qed.
Lemma lem7207487 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term387 A R x f) = (term389 A x R f).
Proof. exact (TRANS (@lem7207485 A R x f) (@lem7207486 A x R f)). Qed.
Lemma lem7207488 {A : Type'} (x : type711 A) (R : type1626) : (term390 A R x) = (term391 A x R).
Proof. exact (fun_ext (fun f : A -> real => @lem7207487 A x R f)). Qed.
Lemma lem7207489 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7207490 {A : Type'} (x : type711 A) (R : type1626) : (term392 A R x) = (term393 A x R).
Proof. exact (MK_COMB (@lem7207489 A) (@lem7207488 A x R)). Qed.
Lemma lem7207491 {A : Type'} (R : type1626) : (term394 A R) = (term395 A R).
Proof. exact (fun_ext (fun x : type711 A => @lem7207490 A x R)). Qed.
Lemma lem7207492 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7207493 {A : Type'} (R : type1626) : (term377 A R) = (term396 A R).
Proof. exact (MK_COMB (@lem7207492 A) (@lem7207491 A R)). Qed.
Lemma lem7207494 {A : Type'} (R : type1626) : ((term376 A R) = (term377 A R)) = ((term373 A R) = (term396 A R)).
Proof. exact (MK_COMB (@lem7207482 A R) (@lem7207493 A R)). Qed.
Lemma lem7207495 {A : Type'} (R : type1626) : (term373 A R) = (term396 A R).
Proof. exact (EQ_MP (@lem7207494 A R) (@lem7207469 A R)). Qed.
Lemma lem7207496 {A : Type'} (R : type1626) : (term268 A R) = (term396 A R).
Proof. exact (TRANS (@lem7207465 A R) (@lem7207495 A R)). Qed.
Lemma lem7207497 (R : type1626) : (term270 R) = (term270 R).
Proof. exact (eq_refl (term270 R)). Qed.
Lemma lem7207498 {A : Type'} (R : type1626) : (term272 A R) = (term397 A R).
Proof. exact (MK_COMB (@lem7207497 R) (@lem7207496 A R)). Qed.
Lemma lem7207502 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7207503 (P : real -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7207502 real P Q). Qed.
Lemma lem7207504 {A : Type'} (R : type1626) : (term400 A R) = (term401 A R).
Proof. exact (@lem7207503 (term235 R) (term396 A R)). Qed.
Lemma lem7207505 (R : type1626) (x1 : real) : (term402 R x1) = (term229 R x1).
Proof. exact (eq_refl (term402 R x1)). Qed.
Lemma lem7207506 (R : type1626) : (term403 R) = (term235 R).
Proof. exact (fun_ext (fun x1 : real => @lem7207505 R x1)). Qed.
Lemma lem7207507 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207508 (R : type1626) : (term404 R) = (term236 R).
Proof. exact (MK_COMB (@lem7207507) (@lem7207506 R)). Qed.
Lemma lem7207509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207510 (R : type1626) : (term405 R) = (term270 R).
Proof. exact (MK_COMB (@lem7207509) (@lem7207508 R)). Qed.
Lemma lem7207511 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207512 {A : Type'} (R : type1626) : (term400 A R) = (term397 A R).
Proof. exact (MK_COMB (@lem7207510 R) (@lem7207511 A R)). Qed.
Lemma lem7207513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207514 {A : Type'} (R : type1626) : (term406 A R) = (term407 A R).
Proof. exact (MK_COMB (@lem7207513) (@lem7207512 A R)). Qed.
Lemma lem7207515 (R : type1626) (x1 : real) : (term402 R x1) = (term229 R x1).
Proof. exact (eq_refl (term402 R x1)). Qed.
Lemma lem7207516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207517 (R : type1626) (x1 : real) : (term408 R x1) = (term409 R x1).
Proof. exact (MK_COMB (@lem7207516) (@lem7207515 R x1)). Qed.
Lemma lem7207518 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207519 {A : Type'} (x1 : real) (R : type1626) : (term410 A x1 R) = (term411 A x1 R).
Proof. exact (MK_COMB (@lem7207517 R x1) (@lem7207518 A R)). Qed.
Lemma lem7207520 {A : Type'} (R : type1626) : (term412 A R) = (term413 A R).
Proof. exact (fun_ext (fun x1 : real => @lem7207519 A x1 R)). Qed.
Lemma lem7207521 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207522 {A : Type'} (R : type1626) : (term401 A R) = (term414 A R).
Proof. exact (MK_COMB (@lem7207521) (@lem7207520 A R)). Qed.
Lemma lem7207523 {A : Type'} (R : type1626) : ((term400 A R) = (term401 A R)) = ((term397 A R) = (term414 A R)).
Proof. exact (MK_COMB (@lem7207514 A R) (@lem7207522 A R)). Qed.
Lemma lem7207524 {A : Type'} (R : type1626) : (term397 A R) = (term414 A R).
Proof. exact (EQ_MP (@lem7207523 A R) (@lem7207504 A R)). Qed.
Lemma lem7207528 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7207529 (P : real -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7207528 real P Q). Qed.
Lemma lem7207530 {A : Type'} (x1 : real) (R : type1626) : (term415 A x1 R) = (term416 A x1 R).
Proof. exact (@lem7207529 (term228 R x1) (term396 A R)). Qed.
Lemma lem7207531 (R : type1626) (x1 : real) (y1 : real) : (term417 R x1 y1) = (term222 R x1 y1).
Proof. exact (eq_refl (term417 R x1 y1)). Qed.
Lemma lem7207532 (R : type1626) (x1 : real) : (term418 R x1) = (term228 R x1).
Proof. exact (fun_ext (fun y1 : real => @lem7207531 R x1 y1)). Qed.
Lemma lem7207533 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207534 (R : type1626) (x1 : real) : (term419 R x1) = (term229 R x1).
Proof. exact (MK_COMB (@lem7207533) (@lem7207532 R x1)). Qed.
Lemma lem7207535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207536 (R : type1626) (x1 : real) : (term420 R x1) = (term409 R x1).
Proof. exact (MK_COMB (@lem7207535) (@lem7207534 R x1)). Qed.
Lemma lem7207537 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207538 {A : Type'} (x1 : real) (R : type1626) : (term415 A x1 R) = (term411 A x1 R).
Proof. exact (MK_COMB (@lem7207536 R x1) (@lem7207537 A R)). Qed.
Lemma lem7207539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207540 {A : Type'} (x1 : real) (R : type1626) : (term421 A x1 R) = (term422 A x1 R).
Proof. exact (MK_COMB (@lem7207539) (@lem7207538 A x1 R)). Qed.
Lemma lem7207541 (R : type1626) (x1 : real) (y1 : real) : (term417 R x1 y1) = (term222 R x1 y1).
Proof. exact (eq_refl (term417 R x1 y1)). Qed.
Lemma lem7207542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207543 (R : type1626) (x1 : real) (y1 : real) : (term423 R x1 y1) = (term424 R x1 y1).
Proof. exact (MK_COMB (@lem7207542) (@lem7207541 R x1 y1)). Qed.
Lemma lem7207544 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207545 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term425 A x1 y1 R) = (term426 A x1 y1 R).
Proof. exact (MK_COMB (@lem7207543 R x1 y1) (@lem7207544 A R)). Qed.
Lemma lem7207546 {A : Type'} (x1 : real) (R : type1626) : (term427 A x1 R) = (term428 A x1 R).
Proof. exact (fun_ext (fun y1 : real => @lem7207545 A x1 y1 R)). Qed.
Lemma lem7207547 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207548 {A : Type'} (x1 : real) (R : type1626) : (term416 A x1 R) = (term429 A x1 R).
Proof. exact (MK_COMB (@lem7207547) (@lem7207546 A x1 R)). Qed.
Lemma lem7207549 {A : Type'} (x1 : real) (R : type1626) : ((term415 A x1 R) = (term416 A x1 R)) = ((term411 A x1 R) = (term429 A x1 R)).
Proof. exact (MK_COMB (@lem7207540 A x1 R) (@lem7207548 A x1 R)). Qed.
Lemma lem7207550 {A : Type'} (x1 : real) (R : type1626) : (term411 A x1 R) = (term429 A x1 R).
Proof. exact (EQ_MP (@lem7207549 A x1 R) (@lem7207530 A x1 R)). Qed.
Lemma lem7207554 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7207555 (P : real -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7207554 real P Q). Qed.
Lemma lem7207556 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term430 A x1 y1 R) = (term431 A x1 y1 R).
Proof. exact (@lem7207555 (term221 R x1 y1) (term396 A R)). Qed.
Lemma lem7207557 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term432 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (eq_refl (term432 R x1 y1 x2)). Qed.
Lemma lem7207558 (R : type1626) (x1 : real) (y1 : real) : (term433 R x1 y1) = (term221 R x1 y1).
Proof. exact (fun_ext (fun x2 : real => @lem7207557 R x1 y1 x2)). Qed.
Lemma lem7207559 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207560 (R : type1626) (x1 : real) (y1 : real) : (term434 R x1 y1) = (term222 R x1 y1).
Proof. exact (MK_COMB (@lem7207559) (@lem7207558 R x1 y1)). Qed.
Lemma lem7207561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207562 (R : type1626) (x1 : real) (y1 : real) : (term435 R x1 y1) = (term424 R x1 y1).
Proof. exact (MK_COMB (@lem7207561) (@lem7207560 R x1 y1)). Qed.
Lemma lem7207563 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207564 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term430 A x1 y1 R) = (term426 A x1 y1 R).
Proof. exact (MK_COMB (@lem7207562 R x1 y1) (@lem7207563 A R)). Qed.
Lemma lem7207565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207566 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term436 A x1 y1 R) = (term437 A x1 y1 R).
Proof. exact (MK_COMB (@lem7207565) (@lem7207564 A x1 y1 R)). Qed.
Lemma lem7207567 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term432 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (eq_refl (term432 R x1 y1 x2)). Qed.
Lemma lem7207568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207569 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term438 R x1 y1 x2) = (term439 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7207568) (@lem7207567 R x1 y1 x2)). Qed.
Lemma lem7207570 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207571 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term440 A x1 y1 x2 R) = (term441 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7207569 R x1 y1 x2) (@lem7207570 A R)). Qed.
Lemma lem7207572 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term442 A x1 y1 R) = (term443 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : real => @lem7207571 A x1 y1 x2 R)). Qed.
Lemma lem7207573 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207574 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term431 A x1 y1 R) = (term444 A x1 y1 R).
Proof. exact (MK_COMB (@lem7207573) (@lem7207572 A x1 y1 R)). Qed.
Lemma lem7207575 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : ((term430 A x1 y1 R) = (term431 A x1 y1 R)) = ((term426 A x1 y1 R) = (term444 A x1 y1 R)).
Proof. exact (MK_COMB (@lem7207566 A x1 y1 R) (@lem7207574 A x1 y1 R)). Qed.
Lemma lem7207576 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term426 A x1 y1 R) = (term444 A x1 y1 R).
Proof. exact (EQ_MP (@lem7207575 A x1 y1 R) (@lem7207556 A x1 y1 R)). Qed.
Lemma lem7207580 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7207581 (P : real -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7207580 real P Q). Qed.
Lemma lem7207582 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term445 A x1 y1 x2 R) = (term446 A x1 y1 x2 R).
Proof. exact (@lem7207581 (term214 R x1 y1 x2) (term396 A R)). Qed.
Lemma lem7207583 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term447 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (eq_refl (term447 R x1 y1 x2 y2)). Qed.
Lemma lem7207584 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term448 R x1 y1 x2) = (term214 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : real => @lem7207583 R x1 y1 x2 y2)). Qed.
Lemma lem7207585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207586 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term449 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7207585) (@lem7207584 R x1 y1 x2)). Qed.
Lemma lem7207587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207588 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term450 R x1 y1 x2) = (term439 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7207587) (@lem7207586 R x1 y1 x2)). Qed.
Lemma lem7207589 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207590 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term445 A x1 y1 x2 R) = (term441 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7207588 R x1 y1 x2) (@lem7207589 A R)). Qed.
Lemma lem7207591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207592 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term451 A x1 y1 x2 R) = (term452 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7207591) (@lem7207590 A x1 y1 x2 R)). Qed.
Lemma lem7207593 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term447 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (eq_refl (term447 R x1 y1 x2 y2)). Qed.
Lemma lem7207594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207595 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term453 R x1 y1 x2 y2) = (term454 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7207594) (@lem7207593 R x1 y1 x2 y2)). Qed.
Lemma lem7207596 {A : Type'} (R : type1626) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7207597 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term455 A x1 y1 x2 y2 R) = (term456 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7207595 R x1 y1 x2 y2) (@lem7207596 A R)). Qed.
Lemma lem7207598 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term457 A x1 y1 x2 R) = (term458 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : real => @lem7207597 A x1 y1 x2 y2 R)). Qed.
Lemma lem7207599 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207600 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term446 A x1 y1 x2 R) = (term459 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7207599) (@lem7207598 A x1 y1 x2 R)). Qed.
Lemma lem7207601 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : ((term445 A x1 y1 x2 R) = (term446 A x1 y1 x2 R)) = ((term441 A x1 y1 x2 R) = (term459 A x1 y1 x2 R)).
Proof. exact (MK_COMB (@lem7207592 A x1 y1 x2 R) (@lem7207600 A x1 y1 x2 R)). Qed.
Lemma lem7207602 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term441 A x1 y1 x2 R) = (term459 A x1 y1 x2 R).
Proof. exact (EQ_MP (@lem7207601 A x1 y1 x2 R) (@lem7207582 A x1 y1 x2 R)). Qed.
Lemma lem7207604 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7207605 {A : Type'} (P : Prop) (Q : type187 A) : (term460 A P Q) = (term461 A P Q).
Proof. exact (@lem7207604 (type711 A) P Q). Qed.
Lemma lem7207606 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term462 A x1 y1 x2 y2 R) = (term463 A x1 y1 x2 y2 R).
Proof. exact (@lem7207605 A (term205 R x1 y1 x2 y2) (term395 A R)). Qed.
Lemma lem7207607 {A : Type'} (x : type711 A) (R : type1626) : (term464 A R x) = (term393 A x R).
Proof. exact (eq_refl (term464 A R x)). Qed.
Lemma lem7207608 {A : Type'} (R : type1626) : (term465 A R) = (term395 A R).
Proof. exact (fun_ext (fun x : type711 A => @lem7207607 A x R)). Qed.
Lemma lem7207609 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7207610 {A : Type'} (R : type1626) : (term466 A R) = (term396 A R).
Proof. exact (MK_COMB (@lem7207609 A) (@lem7207608 A R)). Qed.
Lemma lem7207611 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term454 R x1 y1 x2 y2) = (term454 R x1 y1 x2 y2).
Proof. exact (eq_refl (term454 R x1 y1 x2 y2)). Qed.
Lemma lem7207612 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term462 A x1 y1 x2 y2 R) = (term456 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7207611 R x1 y1 x2 y2) (@lem7207610 A R)). Qed.
Lemma lem7207613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7207614 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term467 A x1 y1 x2 y2 R) = (term468 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7207613) (@lem7207612 A x1 y1 x2 y2 R)). Qed.
Lemma lem7207615 {A : Type'} (x : type711 A) (R : type1626) : (term464 A R x) = (term393 A x R).
Proof. exact (eq_refl (term464 A R x)). Qed.
Lemma lem7207616 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term454 R x1 y1 x2 y2) = (term454 R x1 y1 x2 y2).
Proof. exact (eq_refl (term454 R x1 y1 x2 y2)). Qed.
Lemma lem7207617 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) : (term469 A x1 y1 x2 y2 R x) = (term470 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7207616 R x1 y1 x2 y2) (@lem7207615 A x R)). Qed.
Lemma lem7207618 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term471 A x1 y1 x2 y2 R) = (term472 A x1 y1 x2 y2 R).
Proof. exact (fun_ext (fun x : type711 A => @lem7207617 A x1 y1 x2 y2 x R)). Qed.
Lemma lem7207619 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7207620 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term463 A x1 y1 x2 y2 R) = (term473 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7207619 A) (@lem7207618 A x1 y1 x2 y2 R)). Qed.
Lemma lem7207621 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : ((term462 A x1 y1 x2 y2 R) = (term463 A x1 y1 x2 y2 R)) = ((term456 A x1 y1 x2 y2 R) = (term473 A x1 y1 x2 y2 R)).
Proof. exact (MK_COMB (@lem7207614 A x1 y1 x2 y2 R) (@lem7207620 A x1 y1 x2 y2 R)). Qed.
Lemma lem7207622 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term456 A x1 y1 x2 y2 R) = (term473 A x1 y1 x2 y2 R).
Proof. exact (EQ_MP (@lem7207621 A x1 y1 x2 y2 R) (@lem7207606 A x1 y1 x2 y2 R)). Qed.
Lemma lem7207623 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term458 A x1 y1 x2 R) = (term474 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : real => @lem7207622 A x1 y1 x2 y2 R)). Qed.
Lemma lem7207624 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207625 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term459 A x1 y1 x2 R) = (term475 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7207624) (@lem7207623 A x1 y1 x2 R)). Qed.
Lemma lem7207626 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term441 A x1 y1 x2 R) = (term475 A x1 y1 x2 R).
Proof. exact (TRANS (@lem7207602 A x1 y1 x2 R) (@lem7207625 A x1 y1 x2 R)). Qed.
Lemma lem7207627 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term443 A x1 y1 R) = (term476 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : real => @lem7207626 A x1 y1 x2 R)). Qed.
Lemma lem7207628 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207629 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term444 A x1 y1 R) = (term477 A x1 y1 R).
Proof. exact (MK_COMB (@lem7207628) (@lem7207627 A x1 y1 R)). Qed.
Lemma lem7207630 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term426 A x1 y1 R) = (term477 A x1 y1 R).
Proof. exact (TRANS (@lem7207576 A x1 y1 R) (@lem7207629 A x1 y1 R)). Qed.
Lemma lem7207631 {A : Type'} (x1 : real) (R : type1626) : (term428 A x1 R) = (term478 A x1 R).
Proof. exact (fun_ext (fun y1 : real => @lem7207630 A x1 y1 R)). Qed.
Lemma lem7207632 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207633 {A : Type'} (x1 : real) (R : type1626) : (term429 A x1 R) = (term479 A x1 R).
Proof. exact (MK_COMB (@lem7207632) (@lem7207631 A x1 R)). Qed.
Lemma lem7207634 {A : Type'} (x1 : real) (R : type1626) : (term411 A x1 R) = (term479 A x1 R).
Proof. exact (TRANS (@lem7207550 A x1 R) (@lem7207633 A x1 R)). Qed.
Lemma lem7207635 {A : Type'} (R : type1626) : (term413 A R) = (term480 A R).
Proof. exact (fun_ext (fun x1 : real => @lem7207634 A x1 R)). Qed.
Lemma lem7207636 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7207637 {A : Type'} (R : type1626) : (term414 A R) = (term481 A R).
Proof. exact (MK_COMB (@lem7207636) (@lem7207635 A R)). Qed.
Lemma lem7207638 {A : Type'} (R : type1626) : (term397 A R) = (term481 A R).
Proof. exact (TRANS (@lem7207524 A R) (@lem7207637 A R)). Qed.
Lemma lem7207640 {A : Type'} (R : type1626) : (term272 A R) = (term481 A R).
Proof. exact (TRANS (@lem7207498 A R) (@lem7207638 A R)). Qed.
Lemma lem7207641 {A : Type'} (R : type1626) : (term158 A R) = (term481 A R).
Proof. exact (TRANS (@lem7207157 A R) (@lem7207640 A R)). Qed.
Lemma lem7207642 {A : Type'} (R : type1626) (h1 : term158 A R) : term481 A R.
Proof. exact (EQ_MP (@lem7207641 A R) (@lem7206913 A R h1)). Qed.
Lemma lem7207648 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7207654 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7207661 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term177 A s R f g x) = (term482 A s R f g x).
Proof. exact (@lem17265 (@IN A x s) (term240 A R f g x)). Qed.
Lemma lem7207662 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term178 A s R f g) = (term483 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207661 A s R f g x)). Qed.
Lemma lem7207663 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7207716 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term80 A s R f g) = (term484 A s R f g).
Proof. exact (MK_COMB (@lem7207663 A) (@lem7207662 A s R f g)). Qed.
Lemma lem7207717 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term484 A s R f g.
Proof. exact (EQ_MP (@lem7207716 A s R f g) (@lem7206916 A s R f g h1)). Qed.
Lemma lem7207723 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term191 A R f s g) : term191 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7207724 {A : Type'} (x1 : real) (R : type1626) (h1 : term479 A x1 R) : term479 A x1 R.
Proof. exact (h1). Qed.
Lemma lem7207725 {A : Type'} (x1 : real) (y1 : real) (R : type1626) (h1 : term477 A x1 y1 R) : term477 A x1 y1 R.
Proof. exact (h1). Qed.
Lemma lem7207726 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) (h1 : term475 A x1 y1 x2 R) : term475 A x1 y1 x2 R.
Proof. exact (h1). Qed.
Lemma lem7207727 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) (h1 : term473 A x1 y1 x2 y2 R) : term473 A x1 y1 x2 y2 R.
Proof. exact (h1). Qed.
Lemma lem7207728 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term470 A x1 y1 x2 y2 x R) : term470 A x1 y1 x2 y2 x R.
Proof. exact (h1). Qed.
Lemma lem7207729 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7207736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207737 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7207736 real (real -> real) f x). Qed.
Lemma lem7207738 (m : real) : (real_add m) = (@I (real -> real -> real) real_add m).
Proof. exact (@lem7207737 real_add m). Qed.
Lemma lem7207739 (m' : real) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem7207740 (m : real) (m' : real) : (real_add m m') = (@I (real -> real -> real) real_add m m').
Proof. exact (MK_COMB (@lem7207738 m) (@lem7207739 m')). Qed.
Lemma lem7207742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207743 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7207742 real real f x). Qed.
Lemma lem7207744 (m : real) (m' : real) : (@I (real -> real -> real) real_add m m') = (term485 m m').
Proof. exact (@lem7207743 (@I (real -> real -> real) real_add m) m'). Qed.
Lemma lem7207746 (m : real) (m' : real) : (real_add m m') = (term485 m m').
Proof. exact (TRANS (@lem7207740 m m') (@lem7207744 m m')). Qed.
Lemma lem7207753 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207754 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7207753 real (real -> real) f x). Qed.
Lemma lem7207755 (n : real) : (real_add n) = (@I (real -> real -> real) real_add n).
Proof. exact (@lem7207754 real_add n). Qed.
Lemma lem7207756 (n' : real) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7207757 (n : real) (n' : real) : (real_add n n') = (@I (real -> real -> real) real_add n n').
Proof. exact (MK_COMB (@lem7207755 n) (@lem7207756 n')). Qed.
Lemma lem7207759 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207760 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7207759 real real f x). Qed.
Lemma lem7207761 (n : real) (n' : real) : (@I (real -> real -> real) real_add n n') = (term485 n n').
Proof. exact (@lem7207760 (@I (real -> real -> real) real_add n) n'). Qed.
Lemma lem7207763 (n : real) (n' : real) : (real_add n n') = (term485 n n').
Proof. exact (TRANS (@lem7207757 n n') (@lem7207761 n n')). Qed.
Lemma lem7207764 (R : type1626) (m : real) (m' : real) : (term486 R m m') = (term487 R m m').
Proof. exact (MK_COMB (@lem7207729 R) (@lem7207746 m m')). Qed.
Lemma lem7207765 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term28 R m m' n n') = (term488 R m m' n n').
Proof. exact (MK_COMB (@lem7207764 R m m') (@lem7207763 n n')). Qed.
Lemma lem7207767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207768 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7207767 real (real -> Prop) f x). Qed.
Lemma lem7207769 (R : type1626) (m : real) (m' : real) : (term487 R m m') = (term489 R m m').
Proof. exact (@lem7207768 R (term485 m m')). Qed.
Lemma lem7207770 (n : real) (n' : real) : (term485 n n') = (term485 n n').
Proof. exact (eq_refl (term485 n n')). Qed.
Lemma lem7207771 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term488 R m m' n n') = (term490 R m m' n n').
Proof. exact (MK_COMB (@lem7207769 R m m') (@lem7207770 n n')). Qed.
Lemma lem7207773 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207774 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7207773 real Prop f x). Qed.
Lemma lem7207775 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term490 R m m' n n') = (term491 R m m' n n').
Proof. exact (@lem7207774 (term489 R m m') (term485 n n')). Qed.
Lemma lem7207776 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term488 R m m' n n') = (term491 R m m' n n').
Proof. exact (TRANS (@lem7207771 R m m' n n') (@lem7207775 R m m' n n')). Qed.
Lemma lem7207777 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term28 R m m' n n') = (term491 R m m' n n').
Proof. exact (TRANS (@lem7207765 R m m' n n') (@lem7207776 R m m' n n')). Qed.
Lemma lem7207778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207786 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7207785 real (real -> Prop) f x). Qed.
Lemma lem7207787 (R : type1626) (m' : real) : (R m') = (@I (real -> real -> Prop) R m').
Proof. exact (@lem7207786 R m'). Qed.
Lemma lem7207788 (n' : real) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7207789 (R : type1626) (m' : real) (n' : real) : (R m' n') = (@I (real -> real -> Prop) R m' n').
Proof. exact (MK_COMB (@lem7207787 R m') (@lem7207788 n')). Qed.
Lemma lem7207791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207792 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7207791 real Prop f x). Qed.
Lemma lem7207793 (R : type1626) (m' : real) (n' : real) : (@I (real -> real -> Prop) R m' n') = (term492 R m' n').
Proof. exact (@lem7207792 (@I (real -> real -> Prop) R m') n'). Qed.
Lemma lem7207795 (R : type1626) (m' : real) (n' : real) : (R m' n') = (term492 R m' n').
Proof. exact (TRANS (@lem7207789 R m' n') (@lem7207793 R m' n')). Qed.
Lemma lem7207796 (R : type1626) (m' : real) (n' : real) : (term493 R m' n') = (term494 R m' n').
Proof. exact (MK_COMB (@lem7207778) (@lem7207795 R m' n')). Qed.
Lemma lem7207797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207798 (R : type1626) (m' : real) (n' : real) : (term197 R m' n') = (term495 R m' n').
Proof. exact (MK_COMB (@lem7207797) (@lem7207796 R m' n')). Qed.
Lemma lem7207799 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term192 R m m' n n') = (term496 R m m' n n').
Proof. exact (MK_COMB (@lem7207798 R m' n') (@lem7207777 R m m' n n')). Qed.
Lemma lem7207800 (R : type1626) (m : real) (m' : real) (n : real) : (term193 R m m' n) = (term497 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7207799 R m m' n n')). Qed.
Lemma lem7207801 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7207802 (R : type1626) (m : real) (m' : real) (n : real) : (term194 R m m' n) = (term498 R m m' n).
Proof. exact (MK_COMB (@lem7207801) (@lem7207800 R m m' n)). Qed.
Lemma lem7207803 (R : type1626) (m : real) (n : real) : (term195 R m n) = (term499 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7207802 R m m' n)). Qed.
Lemma lem7207804 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7207805 (R : type1626) (m : real) (n : real) : (term196 R m n) = (term500 R m n).
Proof. exact (MK_COMB (@lem7207804) (@lem7207803 R m n)). Qed.
Lemma lem7207806 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207814 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7207813 real (real -> Prop) f x). Qed.
Lemma lem7207815 (R : type1626) (m : real) : (R m) = (@I (real -> real -> Prop) R m).
Proof. exact (@lem7207814 R m). Qed.
Lemma lem7207816 (n : real) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7207817 (R : type1626) (m : real) (n : real) : (R m n) = (@I (real -> real -> Prop) R m n).
Proof. exact (MK_COMB (@lem7207815 R m) (@lem7207816 n)). Qed.
Lemma lem7207819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207820 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7207819 real Prop f x). Qed.
Lemma lem7207821 (R : type1626) (m : real) (n : real) : (@I (real -> real -> Prop) R m n) = (term492 R m n).
Proof. exact (@lem7207820 (@I (real -> real -> Prop) R m) n). Qed.
Lemma lem7207823 (R : type1626) (m : real) (n : real) : (R m n) = (term492 R m n).
Proof. exact (TRANS (@lem7207817 R m n) (@lem7207821 R m n)). Qed.
Lemma lem7207824 (R : type1626) (m : real) (n : real) : (term493 R m n) = (term494 R m n).
Proof. exact (MK_COMB (@lem7207806) (@lem7207823 R m n)). Qed.
Lemma lem7207825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207826 (R : type1626) (m : real) (n : real) : (term197 R m n) = (term495 R m n).
Proof. exact (MK_COMB (@lem7207825) (@lem7207824 R m n)). Qed.
Lemma lem7207827 (R : type1626) (m : real) (n : real) : (term199 R m n) = (term501 R m n).
Proof. exact (MK_COMB (@lem7207826 R m n) (@lem7207805 R m n)). Qed.
Lemma lem7207828 (R : type1626) (m : real) : (term200 R m) = (term502 R m).
Proof. exact (fun_ext (fun n : real => @lem7207827 R m n)). Qed.
Lemma lem7207829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7207830 (R : type1626) (m : real) : (term201 R m) = (term503 R m).
Proof. exact (MK_COMB (@lem7207829) (@lem7207828 R m)). Qed.
Lemma lem7207831 (R : type1626) : (term202 R) = (term504 R).
Proof. exact (fun_ext (fun m : real => @lem7207830 R m)). Qed.
Lemma lem7207832 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7207833 (R : type1626) : (term203 R) = (term505 R).
Proof. exact (MK_COMB (@lem7207832) (@lem7207831 R)). Qed.
Lemma lem7207834 (R : type1626) (h1 : term71 R) : term505 R.
Proof. exact (EQ_MP (@lem7207833 R) (@lem7207055 R h1)). Qed.
Lemma lem7207839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207840 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7207839 (A -> Prop) Prop f x). Qed.
Lemma lem7207842 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7207840 A (@FINITE A) s). Qed.
Lemma lem7207851 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7207852 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7207857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207859 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7207857 A real f x). Qed.
Lemma lem7207864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207865 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7207864 A real f x). Qed.
Lemma lem7207867 {A : Type'} (g : A -> real) (x : A) : (g x) = (@I (A -> real) g x).
Proof. exact (@lem7207865 A g x). Qed.
Lemma lem7207868 {A : Type'} (R : type1626) (f : A -> real) (x : A) : (term506 A R f x) = (term507 A R f x).
Proof. exact (MK_COMB (@lem7207852 R) (@lem7207859 A f x)). Qed.
Lemma lem7207869 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term240 A R f g x) = (term508 A R f g x).
Proof. exact (MK_COMB (@lem7207868 A R f x) (@lem7207867 A g x)). Qed.
Lemma lem7207871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207872 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7207871 real (real -> Prop) f x). Qed.
Lemma lem7207873 {A : Type'} (R : type1626) (f : A -> real) (x : A) : (term507 A R f x) = (term509 A R f x).
Proof. exact (@lem7207872 R (@I (A -> real) f x)). Qed.
Lemma lem7207874 {A : Type'} (g : A -> real) (x : A) : (@I (A -> real) g x) = (@I (A -> real) g x).
Proof. exact (eq_refl (@I (A -> real) g x)). Qed.
Lemma lem7207875 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term508 A R f g x) = (term510 A R f g x).
Proof. exact (MK_COMB (@lem7207873 A R f x) (@lem7207874 A g x)). Qed.
Lemma lem7207877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207878 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7207877 real Prop f x). Qed.
Lemma lem7207879 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term510 A R f g x) = (term511 A R f g x).
Proof. exact (@lem7207878 (term509 A R f x) (@I (A -> real) g x)). Qed.
Lemma lem7207880 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term508 A R f g x) = (term511 A R f g x).
Proof. exact (TRANS (@lem7207875 A R f g x) (@lem7207879 A R f g x)). Qed.
Lemma lem7207881 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term240 A R f g x) = (term511 A R f g x).
Proof. exact (TRANS (@lem7207869 A R f g x) (@lem7207880 A R f g x)). Qed.
Lemma lem7207882 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207890 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7207889 A (type686 A) f x). Qed.
Lemma lem7207891 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7207890 A (@IN A) x). Qed.
Lemma lem7207892 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7207893 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7207891 A x) (@lem7207892 A s)). Qed.
Lemma lem7207895 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207896 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7207895 (A -> Prop) Prop f x). Qed.
Lemma lem7207897 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term512 A x s).
Proof. exact (@lem7207896 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7207899 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term512 A x s).
Proof. exact (TRANS (@lem7207893 A x s) (@lem7207897 A x s)). Qed.
Lemma lem7207900 {A : Type'} (x : A) (s : A -> Prop) : (term513 A x s) = (term514 A x s).
Proof. exact (MK_COMB (@lem7207882) (@lem7207899 A x s)). Qed.
Lemma lem7207901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7207902 {A : Type'} (x : A) (s : A -> Prop) : (term515 A x s) = (term516 A x s).
Proof. exact (MK_COMB (@lem7207901) (@lem7207900 A x s)). Qed.
Lemma lem7207903 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term482 A s R f g x) = (term517 A s R f g x).
Proof. exact (MK_COMB (@lem7207902 A x s) (@lem7207881 A R f g x)). Qed.
Lemma lem7207904 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term483 A s R f g) = (term518 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7207903 A s R f g x)). Qed.
Lemma lem7207905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7207906 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term484 A s R f g) = (term519 A s R f g).
Proof. exact (MK_COMB (@lem7207905 A) (@lem7207904 A s R f g)). Qed.
Lemma lem7207907 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term519 A s R f g.
Proof. exact (EQ_MP (@lem7207906 A s R f g) (@lem7207717 A s R f g h1)). Qed.
Lemma lem7207908 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7207909 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7207916 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207917 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7207916 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7207918 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7207917 A (@sum A) s). Qed.
Lemma lem7207919 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7207920 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7207918 A s) (@lem7207919 A f)). Qed.
Lemma lem7207922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207923 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7207922 (A -> real) real f x). Qed.
Lemma lem7207924 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term520 A s f).
Proof. exact (@lem7207923 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7207926 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term520 A s f).
Proof. exact (TRANS (@lem7207920 A s f) (@lem7207924 A s f)). Qed.
Lemma lem7207933 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207934 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7207933 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7207935 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7207934 A (@sum A) s). Qed.
Lemma lem7207936 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7207937 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g).
Proof. exact (MK_COMB (@lem7207935 A s) (@lem7207936 A g)). Qed.
Lemma lem7207939 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207940 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7207939 (A -> real) real f x). Qed.
Lemma lem7207941 {A : Type'} (s : A -> Prop) (g : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g) = (term520 A s g).
Proof. exact (@lem7207940 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) g). Qed.
Lemma lem7207943 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (term520 A s g).
Proof. exact (TRANS (@lem7207937 A s g) (@lem7207941 A s g)). Qed.
Lemma lem7207944 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term141 A R s f) = (term521 A R s f).
Proof. exact (MK_COMB (@lem7207909 R) (@lem7207926 A s f)). Qed.
Lemma lem7207945 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term522 A R f s g).
Proof. exact (MK_COMB (@lem7207944 A R s f) (@lem7207943 A s g)). Qed.
Lemma lem7207947 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207948 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7207947 real (real -> Prop) f x). Qed.
Lemma lem7207949 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term521 A R s f) = (term523 A R s f).
Proof. exact (@lem7207948 R (term520 A s f)). Qed.
Lemma lem7207950 {A : Type'} (s : A -> Prop) (g : A -> real) : (term520 A s g) = (term520 A s g).
Proof. exact (eq_refl (term520 A s g)). Qed.
Lemma lem7207951 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term522 A R f s g) = (term524 A R f s g).
Proof. exact (MK_COMB (@lem7207949 A R s f) (@lem7207950 A s g)). Qed.
Lemma lem7207953 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207954 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7207953 real Prop f x). Qed.
Lemma lem7207955 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term524 A R f s g) = (term525 A R f s g).
Proof. exact (@lem7207954 (term523 A R s f) (term520 A s g)). Qed.
Lemma lem7207956 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term522 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7207951 A R f s g) (@lem7207955 A R f s g)). Qed.
Lemma lem7207957 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7207945 A R f s g) (@lem7207956 A R f s g)). Qed.
Lemma lem7207958 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term191 A R f s g) = (term526 A R f s g).
Proof. exact (MK_COMB (@lem7207908) (@lem7207957 A R f s g)). Qed.
Lemma lem7207960 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7207967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207968 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7207967 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7207969 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7207968 A (@sum A) s). Qed.
Lemma lem7207970 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7207971 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7207969 A s) (@lem7207970 A f)). Qed.
Lemma lem7207973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207974 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7207973 (A -> real) real f x). Qed.
Lemma lem7207975 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term520 A s f).
Proof. exact (@lem7207974 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7207977 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term520 A s f).
Proof. exact (TRANS (@lem7207971 A s f) (@lem7207975 A s f)). Qed.
Lemma lem7207984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207985 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7207984 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7207986 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7207985 A (@sum A) s). Qed.
Lemma lem7207987 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7207988 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g).
Proof. exact (MK_COMB (@lem7207986 A s) (@lem7207987 A g)). Qed.
Lemma lem7207990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207991 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7207990 (A -> real) real f x). Qed.
Lemma lem7207992 {A : Type'} (s : A -> Prop) (g : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g) = (term520 A s g).
Proof. exact (@lem7207991 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) g). Qed.
Lemma lem7207994 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (term520 A s g).
Proof. exact (TRANS (@lem7207988 A s g) (@lem7207992 A s g)). Qed.
Lemma lem7207995 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term141 A R s f) = (term521 A R s f).
Proof. exact (MK_COMB (@lem7207960 R) (@lem7207977 A s f)). Qed.
Lemma lem7207996 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term522 A R f s g).
Proof. exact (MK_COMB (@lem7207995 A R s f) (@lem7207994 A s g)). Qed.
Lemma lem7207998 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7207999 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7207998 real (real -> Prop) f x). Qed.
Lemma lem7208000 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term521 A R s f) = (term523 A R s f).
Proof. exact (@lem7207999 R (term520 A s f)). Qed.
Lemma lem7208001 {A : Type'} (s : A -> Prop) (g : A -> real) : (term520 A s g) = (term520 A s g).
Proof. exact (eq_refl (term520 A s g)). Qed.
Lemma lem7208002 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term522 A R f s g) = (term524 A R f s g).
Proof. exact (MK_COMB (@lem7208000 A R s f) (@lem7208001 A s g)). Qed.
Lemma lem7208004 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208005 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7208004 real Prop f x). Qed.
Lemma lem7208006 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term524 A R f s g) = (term525 A R f s g).
Proof. exact (@lem7208005 (term523 A R s f) (term520 A s g)). Qed.
Lemma lem7208007 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term522 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7208002 A R f s g) (@lem7208006 A R f s g)). Qed.
Lemma lem7208008 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7207996 A R f s g) (@lem7208007 A R f s g)). Qed.
Lemma lem7208009 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7208010 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7208011 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7208020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208021 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7208020 (A -> real) (type710 A) f x). Qed.
Lemma lem7208022 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7208021 A x f). Qed.
Lemma lem7208023 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7208024 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7208022 A x f) (@lem7208023 A g)). Qed.
Lemma lem7208026 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208027 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7208026 (A -> real) (type684 A) f x). Qed.
Lemma lem7208028 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g) = (term527 A x f g).
Proof. exact (@lem7208027 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7208029 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (term527 A x f g).
Proof. exact (TRANS (@lem7208024 A x f g) (@lem7208028 A x f g)). Qed.
Lemma lem7208030 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7208031 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term528 A x f g s).
Proof. exact (MK_COMB (@lem7208029 A x f g) (@lem7208030 A s)). Qed.
Lemma lem7208033 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208034 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7208033 (A -> Prop) A f x). Qed.
Lemma lem7208035 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term528 A x f g s) = (term529 A x f g s).
Proof. exact (@lem7208034 A (term527 A x f g) s). Qed.
Lemma lem7208037 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term529 A x f g s).
Proof. exact (TRANS (@lem7208031 A x f g s) (@lem7208035 A x f g s)). Qed.
Lemma lem7208038 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term530 A x f g s) = (term531 A x f g s).
Proof. exact (MK_COMB (@lem7208011 A f) (@lem7208037 A x f g s)). Qed.
Lemma lem7208040 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208041 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7208040 A real f x). Qed.
Lemma lem7208042 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term531 A x f g s) = (term532 A x f g s).
Proof. exact (@lem7208041 A f (term529 A x f g s)). Qed.
Lemma lem7208043 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term530 A x f g s) = (term532 A x f g s).
Proof. exact (TRANS (@lem7208038 A x f g s) (@lem7208042 A x f g s)). Qed.
Lemma lem7208044 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7208053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208054 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7208053 (A -> real) (type710 A) f x). Qed.
Lemma lem7208055 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7208054 A x f). Qed.
Lemma lem7208056 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7208057 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7208055 A x f) (@lem7208056 A g)). Qed.
Lemma lem7208059 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208060 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7208059 (A -> real) (type684 A) f x). Qed.
Lemma lem7208061 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g) = (term527 A x f g).
Proof. exact (@lem7208060 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7208062 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (term527 A x f g).
Proof. exact (TRANS (@lem7208057 A x f g) (@lem7208061 A x f g)). Qed.
Lemma lem7208063 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7208064 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term528 A x f g s).
Proof. exact (MK_COMB (@lem7208062 A x f g) (@lem7208063 A s)). Qed.
Lemma lem7208066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208067 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7208066 (A -> Prop) A f x). Qed.
Lemma lem7208068 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term528 A x f g s) = (term529 A x f g s).
Proof. exact (@lem7208067 A (term527 A x f g) s). Qed.
Lemma lem7208070 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term529 A x f g s).
Proof. exact (TRANS (@lem7208064 A x f g s) (@lem7208068 A x f g s)). Qed.
Lemma lem7208071 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term533 A x f g s) = (term534 A x f g s).
Proof. exact (MK_COMB (@lem7208044 A g) (@lem7208070 A x f g s)). Qed.
Lemma lem7208073 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208074 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7208073 A real f x). Qed.
Lemma lem7208075 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term534 A x f g s) = (term535 A x f g s).
Proof. exact (@lem7208074 A g (term529 A x f g s)). Qed.
Lemma lem7208076 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term533 A x f g s) = (term535 A x f g s).
Proof. exact (TRANS (@lem7208071 A x f g s) (@lem7208075 A x f g s)). Qed.
Lemma lem7208077 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term536 A R x f g s) = (term537 A R x f g s).
Proof. exact (MK_COMB (@lem7208010 R) (@lem7208043 A x f g s)). Qed.
Lemma lem7208078 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term538 A R x f g s) = (term539 A R x f g s).
Proof. exact (MK_COMB (@lem7208077 A R x f g s) (@lem7208076 A x f g s)). Qed.
Lemma lem7208080 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208081 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7208080 real (real -> Prop) f x). Qed.
Lemma lem7208082 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term537 A R x f g s) = (term540 A R x f g s).
Proof. exact (@lem7208081 R (term532 A x f g s)). Qed.
Lemma lem7208083 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term535 A x f g s) = (term535 A x f g s).
Proof. exact (eq_refl (term535 A x f g s)). Qed.
Lemma lem7208084 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term539 A R x f g s) = (term541 A R x f g s).
Proof. exact (MK_COMB (@lem7208082 A R x f g s) (@lem7208083 A x f g s)). Qed.
Lemma lem7208086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208087 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7208086 real Prop f x). Qed.
Lemma lem7208088 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term541 A R x f g s) = (term542 A R x f g s).
Proof. exact (@lem7208087 (term540 A R x f g s) (term535 A x f g s)). Qed.
Lemma lem7208089 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term539 A R x f g s) = (term542 A R x f g s).
Proof. exact (TRANS (@lem7208084 A R x f g s) (@lem7208088 A R x f g s)). Qed.
Lemma lem7208090 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term538 A R x f g s) = (term542 A R x f g s).
Proof. exact (TRANS (@lem7208078 A R x f g s) (@lem7208089 A R x f g s)). Qed.
Lemma lem7208091 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term543 A R x f g s) = (term544 A R x f g s).
Proof. exact (MK_COMB (@lem7208009) (@lem7208090 A R x f g s)). Qed.
Lemma lem7208092 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7208101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208102 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7208101 (A -> real) (type710 A) f x). Qed.
Lemma lem7208103 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7208102 A x f). Qed.
Lemma lem7208104 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7208105 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7208103 A x f) (@lem7208104 A g)). Qed.
Lemma lem7208107 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208108 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7208107 (A -> real) (type684 A) f x). Qed.
Lemma lem7208109 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g) = (term527 A x f g).
Proof. exact (@lem7208108 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7208110 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (term527 A x f g).
Proof. exact (TRANS (@lem7208105 A x f g) (@lem7208109 A x f g)). Qed.
Lemma lem7208111 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7208112 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term528 A x f g s).
Proof. exact (MK_COMB (@lem7208110 A x f g) (@lem7208111 A s)). Qed.
Lemma lem7208114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208115 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7208114 (A -> Prop) A f x). Qed.
Lemma lem7208116 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term528 A x f g s) = (term529 A x f g s).
Proof. exact (@lem7208115 A (term527 A x f g) s). Qed.
Lemma lem7208118 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term529 A x f g s).
Proof. exact (TRANS (@lem7208112 A x f g s) (@lem7208116 A x f g s)). Qed.
Lemma lem7208119 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7208120 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term545 A x f g s) = (term546 A x f g s).
Proof. exact (MK_COMB (@lem7208092 A) (@lem7208118 A x f g s)). Qed.
Lemma lem7208121 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term547 A x f g s) = (term548 A x f g s).
Proof. exact (MK_COMB (@lem7208120 A x f g s) (@lem7208119 A s)). Qed.
Lemma lem7208123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208124 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7208123 A (type686 A) f x). Qed.
Lemma lem7208125 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term546 A x f g s) = (term549 A x f g s).
Proof. exact (@lem7208124 A (@IN A) (term529 A x f g s)). Qed.
Lemma lem7208126 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7208127 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term548 A x f g s) = (term550 A x f g s).
Proof. exact (MK_COMB (@lem7208125 A x f g s) (@lem7208126 A s)). Qed.
Lemma lem7208129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208130 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7208129 (A -> Prop) Prop f x). Qed.
Lemma lem7208131 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term550 A x f g s) = (term551 A x f g s).
Proof. exact (@lem7208130 A (term549 A x f g s) s). Qed.
Lemma lem7208132 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term548 A x f g s) = (term551 A x f g s).
Proof. exact (TRANS (@lem7208127 A x f g s) (@lem7208131 A x f g s)). Qed.
Lemma lem7208133 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term547 A x f g s) = (term551 A x f g s).
Proof. exact (TRANS (@lem7208121 A x f g s) (@lem7208132 A x f g s)). Qed.
Lemma lem7208134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7208135 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term552 A x f g s) = (term553 A x f g s).
Proof. exact (MK_COMB (@lem7208134) (@lem7208133 A x f g s)). Qed.
Lemma lem7208136 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term554 A R x f g s) = (term555 A R x f g s).
Proof. exact (MK_COMB (@lem7208135 A x f g s) (@lem7208091 A R x f g s)). Qed.
Lemma lem7208143 {A : Type'} (s : A -> Prop) : (term251 A s) = (term251 A s).
Proof. exact (eq_refl (term251 A s)). Qed.
Lemma lem7208144 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term556 A R x f g s) = (term557 A R x f g s).
Proof. exact (MK_COMB (@lem7208143 A s) (@lem7208136 A R x f g s)). Qed.
Lemma lem7208145 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7208150 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208151 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7208150 (A -> Prop) Prop f x). Qed.
Lemma lem7208153 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7208151 A (@FINITE A) s). Qed.
Lemma lem7208154 {A : Type'} (s : A -> Prop) : (term290 A s) = (term558 A s).
Proof. exact (MK_COMB (@lem7208145) (@lem7208153 A s)). Qed.
Lemma lem7208155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7208156 {A : Type'} (s : A -> Prop) : (term255 A s) = (term559 A s).
Proof. exact (MK_COMB (@lem7208155) (@lem7208154 A s)). Qed.
Lemma lem7208157 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term560 A R x f g s) = (term561 A R x f g s).
Proof. exact (MK_COMB (@lem7208156 A s) (@lem7208144 A R x f g s)). Qed.
Lemma lem7208158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7208159 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term562 A R x f g s) = (term563 A R x f g s).
Proof. exact (MK_COMB (@lem7208158) (@lem7208157 A R x f g s)). Qed.
Lemma lem7208160 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term564 A x R f s g) = (term565 A x R f s g).
Proof. exact (MK_COMB (@lem7208159 A R x f g s) (@lem7208008 A R f s g)). Qed.
Lemma lem7208161 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term566 A x R f g) = (term567 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7208160 A x R f s g)). Qed.
Lemma lem7208162 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7208163 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term568 A x R f g) = (term569 A x R f g).
Proof. exact (MK_COMB (@lem7208162 A) (@lem7208161 A x R f g)). Qed.
Lemma lem7208164 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term570 A x R f) = (term571 A x R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7208163 A x R f g)). Qed.
Lemma lem7208165 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7208166 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term389 A x R f) = (term572 A x R f).
Proof. exact (MK_COMB (@lem7208165 A) (@lem7208164 A x R f)). Qed.
Lemma lem7208167 {A : Type'} (x : type711 A) (R : type1626) : (term391 A x R) = (term573 A x R).
Proof. exact (fun_ext (fun f : A -> real => @lem7208166 A x R f)). Qed.
Lemma lem7208168 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7208169 {A : Type'} (x : type711 A) (R : type1626) : (term393 A x R) = (term574 A x R).
Proof. exact (MK_COMB (@lem7208168 A) (@lem7208167 A x R)). Qed.
Lemma lem7208170 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7208171 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7208178 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208179 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7208178 real (real -> real) f x). Qed.
Lemma lem7208180 (x1 : real) : (real_add x1) = (@I (real -> real -> real) real_add x1).
Proof. exact (@lem7208179 real_add x1). Qed.
Lemma lem7208181 (y1 : real) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem7208182 (x1 : real) (y1 : real) : (real_add x1 y1) = (@I (real -> real -> real) real_add x1 y1).
Proof. exact (MK_COMB (@lem7208180 x1) (@lem7208181 y1)). Qed.
Lemma lem7208184 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208185 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7208184 real real f x). Qed.
Lemma lem7208186 (x1 : real) (y1 : real) : (@I (real -> real -> real) real_add x1 y1) = (term485 x1 y1).
Proof. exact (@lem7208185 (@I (real -> real -> real) real_add x1) y1). Qed.
Lemma lem7208188 (x1 : real) (y1 : real) : (real_add x1 y1) = (term485 x1 y1).
Proof. exact (TRANS (@lem7208182 x1 y1) (@lem7208186 x1 y1)). Qed.
Lemma lem7208195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208196 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7208195 real (real -> real) f x). Qed.
Lemma lem7208197 (x2 : real) : (real_add x2) = (@I (real -> real -> real) real_add x2).
Proof. exact (@lem7208196 real_add x2). Qed.
Lemma lem7208198 (y2 : real) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7208199 (x2 : real) (y2 : real) : (real_add x2 y2) = (@I (real -> real -> real) real_add x2 y2).
Proof. exact (MK_COMB (@lem7208197 x2) (@lem7208198 y2)). Qed.
Lemma lem7208201 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208202 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7208201 real real f x). Qed.
Lemma lem7208203 (x2 : real) (y2 : real) : (@I (real -> real -> real) real_add x2 y2) = (term485 x2 y2).
Proof. exact (@lem7208202 (@I (real -> real -> real) real_add x2) y2). Qed.
Lemma lem7208205 (x2 : real) (y2 : real) : (real_add x2 y2) = (term485 x2 y2).
Proof. exact (TRANS (@lem7208199 x2 y2) (@lem7208203 x2 y2)). Qed.
Lemma lem7208206 (R : type1626) (x1 : real) (y1 : real) : (term486 R x1 y1) = (term487 R x1 y1).
Proof. exact (MK_COMB (@lem7208171 R) (@lem7208188 x1 y1)). Qed.
Lemma lem7208207 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term28 R x1 y1 x2 y2) = (term488 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7208206 R x1 y1) (@lem7208205 x2 y2)). Qed.
Lemma lem7208209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208210 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7208209 real (real -> Prop) f x). Qed.
Lemma lem7208211 (R : type1626) (x1 : real) (y1 : real) : (term487 R x1 y1) = (term489 R x1 y1).
Proof. exact (@lem7208210 R (term485 x1 y1)). Qed.
Lemma lem7208212 (x2 : real) (y2 : real) : (term485 x2 y2) = (term485 x2 y2).
Proof. exact (eq_refl (term485 x2 y2)). Qed.
Lemma lem7208213 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term488 R x1 y1 x2 y2) = (term490 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7208211 R x1 y1) (@lem7208212 x2 y2)). Qed.
Lemma lem7208215 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208216 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7208215 real Prop f x). Qed.
Lemma lem7208217 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term490 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (@lem7208216 (term489 R x1 y1) (term485 x2 y2)). Qed.
Lemma lem7208218 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term488 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7208213 R x1 y1 x2 y2) (@lem7208217 R x1 y1 x2 y2)). Qed.
Lemma lem7208219 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term28 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7208207 R x1 y1 x2 y2) (@lem7208218 R x1 y1 x2 y2)). Qed.
Lemma lem7208220 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term575 R x1 y1 x2 y2) = (term576 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7208170) (@lem7208219 R x1 y1 x2 y2)). Qed.
Lemma lem7208227 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208228 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7208227 real (real -> Prop) f x). Qed.
Lemma lem7208229 (R : type1626) (y1 : real) : (R y1) = (@I (real -> real -> Prop) R y1).
Proof. exact (@lem7208228 R y1). Qed.
Lemma lem7208230 (y2 : real) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7208231 (R : type1626) (y1 : real) (y2 : real) : (R y1 y2) = (@I (real -> real -> Prop) R y1 y2).
Proof. exact (MK_COMB (@lem7208229 R y1) (@lem7208230 y2)). Qed.
Lemma lem7208233 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208234 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7208233 real Prop f x). Qed.
Lemma lem7208235 (R : type1626) (y1 : real) (y2 : real) : (@I (real -> real -> Prop) R y1 y2) = (term492 R y1 y2).
Proof. exact (@lem7208234 (@I (real -> real -> Prop) R y1) y2). Qed.
Lemma lem7208237 (R : type1626) (y1 : real) (y2 : real) : (R y1 y2) = (term492 R y1 y2).
Proof. exact (TRANS (@lem7208231 R y1 y2) (@lem7208235 R y1 y2)). Qed.
Lemma lem7208244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208245 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7208244 real (real -> Prop) f x). Qed.
Lemma lem7208246 (R : type1626) (x1 : real) : (R x1) = (@I (real -> real -> Prop) R x1).
Proof. exact (@lem7208245 R x1). Qed.
Lemma lem7208247 (x2 : real) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem7208248 (R : type1626) (x1 : real) (x2 : real) : (R x1 x2) = (@I (real -> real -> Prop) R x1 x2).
Proof. exact (MK_COMB (@lem7208246 R x1) (@lem7208247 x2)). Qed.
Lemma lem7208250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7208251 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7208250 real Prop f x). Qed.
Lemma lem7208252 (R : type1626) (x1 : real) (x2 : real) : (@I (real -> real -> Prop) R x1 x2) = (term492 R x1 x2).
Proof. exact (@lem7208251 (@I (real -> real -> Prop) R x1) x2). Qed.
Lemma lem7208254 (R : type1626) (x1 : real) (x2 : real) : (R x1 x2) = (term492 R x1 x2).
Proof. exact (TRANS (@lem7208248 R x1 x2) (@lem7208252 R x1 x2)). Qed.
Lemma lem7208255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7208256 (R : type1626) (x1 : real) (x2 : real) : (term577 R x1 x2) = (term578 R x1 x2).
Proof. exact (MK_COMB (@lem7208255) (@lem7208254 R x1 x2)). Qed.
Lemma lem7208257 (x1 : real) (x2 : real) (R : type1626) (y1 : real) (y2 : real) : (term206 x1 x2 R y1 y2) = (term579 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7208256 R x1 x2) (@lem7208237 R y1 y2)). Qed.
Lemma lem7208258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7208259 (x1 : real) (x2 : real) (R : type1626) (y1 : real) (y2 : real) : (term580 x1 x2 R y1 y2) = (term581 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7208258) (@lem7208257 x1 x2 R y1 y2)). Qed.
Lemma lem7208260 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term205 R x1 y1 x2 y2) = (term582 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7208259 x1 x2 R y1 y2) (@lem7208220 R x1 y1 x2 y2)). Qed.
Lemma lem7208261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7208262 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term454 R x1 y1 x2 y2) = (term583 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7208261) (@lem7208260 R x1 y1 x2 y2)). Qed.
Lemma lem7208263 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) : (term470 A x1 y1 x2 y2 x R) = (term584 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7208262 R x1 y1 x2 y2) (@lem7208169 A x R)). Qed.
Lemma lem7208264 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term470 A x1 y1 x2 y2 x R) : term584 A x1 y1 x2 y2 x R.
Proof. exact (EQ_MP (@lem7208263 A x1 y1 x2 y2 x R) (@lem7207728 A x1 y1 x2 y2 x R h1)). Qed.
Lemma lem7208265 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term582 R x1 y1 x2 y2.
Proof. exact (h1). Qed.
Lemma lem7208266 {A : Type'} (x : type711 A) (R : type1626) (h1 : term574 A x R) : term574 A x R.
Proof. exact (h1). Qed.
Lemma lem7208268 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term579 x1 x2 R y1 y2.
Proof. exact (proj1 (@lem7208265 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208272 {A : Type'} (P : Prop) (Q : A -> Prop) : (term585 A P Q) = (term586 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7208273 (P : Prop) (Q : real -> Prop) : (term587 P Q) = (term588 P Q).
Proof. exact (@lem7208272 real P Q). Qed.
Lemma lem7208274 (R : type1626) (m : real) (n : real) : (term589 R m n) = (term590 R m n).
Proof. exact (@lem7208273 (term494 R m n) (term499 R m n)). Qed.
Lemma lem7208275 (R : type1626) (m : real) (m' : real) (n : real) : (term591 R m n m') = (term498 R m m' n).
Proof. exact (eq_refl (term591 R m n m')). Qed.
Lemma lem7208276 (R : type1626) (m : real) (n : real) : (term592 R m n) = (term499 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7208275 R m m' n)). Qed.
Lemma lem7208277 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208278 (R : type1626) (m : real) (n : real) : (term593 R m n) = (term500 R m n).
Proof. exact (MK_COMB (@lem7208277) (@lem7208276 R m n)). Qed.
Lemma lem7208279 (R : type1626) (m : real) (n : real) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7208280 (R : type1626) (m : real) (n : real) : (term589 R m n) = (term501 R m n).
Proof. exact (MK_COMB (@lem7208279 R m n) (@lem7208278 R m n)). Qed.
Lemma lem7208281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7208282 (R : type1626) (m : real) (n : real) : (term594 R m n) = (term595 R m n).
Proof. exact (MK_COMB (@lem7208281) (@lem7208280 R m n)). Qed.
Lemma lem7208283 (R : type1626) (m : real) (m' : real) (n : real) : (term591 R m n m') = (term498 R m m' n).
Proof. exact (eq_refl (term591 R m n m')). Qed.
Lemma lem7208284 (R : type1626) (m : real) (n : real) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7208285 (R : type1626) (m : real) (m' : real) (n : real) : (term596 R m n m') = (term597 R m m' n).
Proof. exact (MK_COMB (@lem7208284 R m n) (@lem7208283 R m m' n)). Qed.
Lemma lem7208286 (R : type1626) (m : real) (n : real) : (term598 R m n) = (term599 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7208285 R m m' n)). Qed.
Lemma lem7208287 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208288 (R : type1626) (m : real) (n : real) : (term590 R m n) = (term600 R m n).
Proof. exact (MK_COMB (@lem7208287) (@lem7208286 R m n)). Qed.
Lemma lem7208289 (R : type1626) (m : real) (n : real) : ((term589 R m n) = (term590 R m n)) = ((term501 R m n) = (term600 R m n)).
Proof. exact (MK_COMB (@lem7208282 R m n) (@lem7208288 R m n)). Qed.
Lemma lem7208290 (R : type1626) (m : real) (n : real) : (term501 R m n) = (term600 R m n).
Proof. exact (EQ_MP (@lem7208289 R m n) (@lem7208274 R m n)). Qed.
Lemma lem7208292 {A : Type'} (P : Prop) (Q : A -> Prop) : (term585 A P Q) = (term586 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7208293 (P : Prop) (Q : real -> Prop) : (term587 P Q) = (term588 P Q).
Proof. exact (@lem7208292 real P Q). Qed.
Lemma lem7208294 (R : type1626) (m : real) (m' : real) (n : real) : (term601 R m m' n) = (term602 R m m' n).
Proof. exact (@lem7208293 (term494 R m n) (term497 R m m' n)). Qed.
Lemma lem7208295 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term603 R m m' n n') = (term496 R m m' n n').
Proof. exact (eq_refl (term603 R m m' n n')). Qed.
Lemma lem7208296 (R : type1626) (m : real) (m' : real) (n : real) : (term604 R m m' n) = (term497 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7208295 R m m' n n')). Qed.
Lemma lem7208297 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208298 (R : type1626) (m : real) (m' : real) (n : real) : (term605 R m m' n) = (term498 R m m' n).
Proof. exact (MK_COMB (@lem7208297) (@lem7208296 R m m' n)). Qed.
Lemma lem7208299 (R : type1626) (m : real) (n : real) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7208300 (R : type1626) (m : real) (m' : real) (n : real) : (term601 R m m' n) = (term597 R m m' n).
Proof. exact (MK_COMB (@lem7208299 R m n) (@lem7208298 R m m' n)). Qed.
Lemma lem7208301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7208302 (R : type1626) (m : real) (m' : real) (n : real) : (term606 R m m' n) = (term607 R m m' n).
Proof. exact (MK_COMB (@lem7208301) (@lem7208300 R m m' n)). Qed.
Lemma lem7208303 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term603 R m m' n n') = (term496 R m m' n n').
Proof. exact (eq_refl (term603 R m m' n n')). Qed.
Lemma lem7208304 (R : type1626) (m : real) (n : real) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7208305 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term608 R m m' n n') = (term609 R m m' n n').
Proof. exact (MK_COMB (@lem7208304 R m n) (@lem7208303 R m m' n n')). Qed.
Lemma lem7208306 (R : type1626) (m : real) (m' : real) (n : real) : (term610 R m m' n) = (term611 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7208305 R m m' n n')). Qed.
Lemma lem7208307 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208308 (R : type1626) (m : real) (m' : real) (n : real) : (term602 R m m' n) = (term612 R m m' n).
Proof. exact (MK_COMB (@lem7208307) (@lem7208306 R m m' n)). Qed.
Lemma lem7208309 (R : type1626) (m : real) (m' : real) (n : real) : ((term601 R m m' n) = (term602 R m m' n)) = ((term597 R m m' n) = (term612 R m m' n)).
Proof. exact (MK_COMB (@lem7208302 R m m' n) (@lem7208308 R m m' n)). Qed.
Lemma lem7208310 (R : type1626) (m : real) (m' : real) (n : real) : (term597 R m m' n) = (term612 R m m' n).
Proof. exact (EQ_MP (@lem7208309 R m m' n) (@lem7208294 R m m' n)). Qed.
Lemma lem7208311 (R : type1626) (m : real) (n : real) : (term599 R m n) = (term613 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7208310 R m m' n)). Qed.
Lemma lem7208312 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208313 (R : type1626) (m : real) (n : real) : (term600 R m n) = (term614 R m n).
Proof. exact (MK_COMB (@lem7208312) (@lem7208311 R m n)). Qed.
Lemma lem7208314 (R : type1626) (m : real) (n : real) : (term501 R m n) = (term614 R m n).
Proof. exact (TRANS (@lem7208290 R m n) (@lem7208313 R m n)). Qed.
Lemma lem7208315 (R : type1626) (m : real) : (term502 R m) = (term615 R m).
Proof. exact (fun_ext (fun n : real => @lem7208314 R m n)). Qed.
Lemma lem7208316 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208317 (R : type1626) (m : real) : (term503 R m) = (term616 R m).
Proof. exact (MK_COMB (@lem7208316) (@lem7208315 R m)). Qed.
Lemma lem7208318 (R : type1626) : (term504 R) = (term617 R).
Proof. exact (fun_ext (fun m : real => @lem7208317 R m)). Qed.
Lemma lem7208319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208320 (R : type1626) : (term505 R) = (term618 R).
Proof. exact (MK_COMB (@lem7208319) (@lem7208318 R)). Qed.
Lemma lem7208333 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term609 R m m' n n') = (term609 R m m' n n').
Proof. exact (eq_refl (term609 R m m' n n')). Qed.
Lemma lem7208334 (R : type1626) (m : real) (m' : real) (n : real) : (term611 R m m' n) = (term611 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7208333 R m m' n n')). Qed.
Lemma lem7208335 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208336 (R : type1626) (m : real) (m' : real) (n : real) : (term612 R m m' n) = (term612 R m m' n).
Proof. exact (MK_COMB (@lem7208335) (@lem7208334 R m m' n)). Qed.
Lemma lem7208337 (R : type1626) (m : real) (n : real) : (term613 R m n) = (term613 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7208336 R m m' n)). Qed.
Lemma lem7208338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208339 (R : type1626) (m : real) (n : real) : (term614 R m n) = (term614 R m n).
Proof. exact (MK_COMB (@lem7208338) (@lem7208337 R m n)). Qed.
Lemma lem7208340 (R : type1626) (m : real) : (term615 R m) = (term615 R m).
Proof. exact (fun_ext (fun n : real => @lem7208339 R m n)). Qed.
Lemma lem7208341 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208342 (R : type1626) (m : real) : (term616 R m) = (term616 R m).
Proof. exact (MK_COMB (@lem7208341) (@lem7208340 R m)). Qed.
Lemma lem7208343 (R : type1626) : (term617 R) = (term617 R).
Proof. exact (fun_ext (fun m : real => @lem7208342 R m)). Qed.
Lemma lem7208344 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7208345 (R : type1626) : (term618 R) = (term618 R).
Proof. exact (MK_COMB (@lem7208344) (@lem7208343 R)). Qed.
Lemma lem7208346 (R : type1626) : (term505 R) = (term618 R).
Proof. exact (TRANS (@lem7208320 R) (@lem7208345 R)). Qed.
Lemma lem7208347 (R : type1626) (h1 : term71 R) : term618 R.
Proof. exact (EQ_MP (@lem7208346 R) (@lem7207834 R h1)). Qed.
Lemma lem7208469 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7208477 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term517 A s R f g x) = (term517 A s R f g x).
Proof. exact (eq_refl (term517 A s R f g x)). Qed.
Lemma lem7208478 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term518 A s R f g) = (term518 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7208477 A s R f g x)). Qed.
Lemma lem7208479 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7208481 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term519 A s R f g) = (term519 A s R f g).
Proof. exact (MK_COMB (@lem7208479 A) (@lem7208478 A s R f g)). Qed.
Lemma lem7208482 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term519 A s R f g.
Proof. exact (EQ_MP (@lem7208481 A s R f g) (@lem7207907 A s R f g h1)). Qed.
Lemma lem7208488 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term525 A R f s g) = (term525 A R f s g).
Proof. exact (eq_refl (term525 A R f s g)). Qed.
Lemma lem7208505 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term557 A R x f g s) = (term619 A R x f g s).
Proof. exact (@lem19490 (term551 A x f g s) (s = (@EMPTY A)) (term544 A R x f g s)). Qed.
Lemma lem7208508 {A : Type'} (s : A -> Prop) : (term559 A s) = (term559 A s).
Proof. exact (eq_refl (term559 A s)). Qed.
Lemma lem7208509 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term561 A R x f g s) = (term620 A R x f g s).
Proof. exact (MK_COMB (@lem7208508 A s) (@lem7208505 A R x f g s)). Qed.
Lemma lem7208516 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term620 A R x f g s) = (term621 A R x f g s).
Proof. exact (@lem19490 (term622 A x f g s) (term558 A s) (term623 A R x f g s)). Qed.
Lemma lem7208517 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term561 A R x f g s) = (term621 A R x f g s).
Proof. exact (TRANS (@lem7208509 A R x f g s) (@lem7208516 A R x f g s)). Qed.
Lemma lem7208518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7208519 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term563 A R x f g s) = (term624 A R x f g s).
Proof. exact (MK_COMB (@lem7208518) (@lem7208517 A R x f g s)). Qed.
Lemma lem7208520 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term565 A x R f s g) = (term625 A x R f s g).
Proof. exact (MK_COMB (@lem7208519 A R x f g s) (@lem7208488 A R f s g)). Qed.
Lemma lem7208527 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term625 A x R f s g) = (term626 A x R f s g).
Proof. exact (@lem19699 (term627 A x f g s) (term628 A R x f g s) (term525 A R f s g)). Qed.
Lemma lem7208528 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term565 A x R f s g) = (term626 A x R f s g).
Proof. exact (TRANS (@lem7208520 A x R f s g) (@lem7208527 A x R f s g)). Qed.
Lemma lem7208529 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term567 A x R f g) = (term629 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7208528 A x R f s g)). Qed.
Lemma lem7208530 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7208531 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term569 A x R f g) = (term630 A x R f g).
Proof. exact (MK_COMB (@lem7208530 A) (@lem7208529 A x R f g)). Qed.
Lemma lem7208532 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term571 A x R f) = (term631 A x R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7208531 A x R f g)). Qed.
Lemma lem7208533 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7208534 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term572 A x R f) = (term632 A x R f).
Proof. exact (MK_COMB (@lem7208533 A) (@lem7208532 A x R f)). Qed.
Lemma lem7208535 {A : Type'} (x : type711 A) (R : type1626) : (term573 A x R) = (term633 A x R).
Proof. exact (fun_ext (fun f : A -> real => @lem7208534 A x R f)). Qed.
Lemma lem7208536 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7208538 {A : Type'} (x : type711 A) (R : type1626) : (term574 A x R) = (term634 A x R).
Proof. exact (MK_COMB (@lem7208536 A) (@lem7208535 A x R)). Qed.
Lemma lem7208539 {A : Type'} (x : type711 A) (R : type1626) (h1 : term574 A x R) : term634 A x R.
Proof. exact (EQ_MP (@lem7208538 A x R) (@lem7208266 A x R h1)). Qed.
Lemma lem7208540 (_96508 : real) (R : type1626) (h1 : term71 R) : term635 R _96508.
Proof. exact (@lem7208347 R h1 _96508). Qed.
Lemma lem7208541 (R : type1626) (_96508 : real) : (term635 R _96508) = (term616 R _96508).
Proof. exact (eq_refl (term635 R _96508)). Qed.
Lemma lem7208542 (_96508 : real) (R : type1626) (h1 : term71 R) : term616 R _96508.
Proof. exact (EQ_MP (@lem7208541 R _96508) (@lem7208540 _96508 R h1)). Qed.
Lemma lem7208543 (_96508 : real) (_96509 : real) (R : type1626) (h1 : term71 R) : term636 R _96508 _96509.
Proof. exact (@lem7208542 _96508 R h1 _96509). Qed.
Lemma lem7208544 (R : type1626) (_96508 : real) (_96509 : real) : (term636 R _96508 _96509) = (term614 R _96508 _96509).
Proof. exact (eq_refl (term636 R _96508 _96509)). Qed.
Lemma lem7208545 (_96508 : real) (_96509 : real) (R : type1626) (h1 : term71 R) : term614 R _96508 _96509.
Proof. exact (EQ_MP (@lem7208544 R _96508 _96509) (@lem7208543 _96508 _96509 R h1)). Qed.
Lemma lem7208546 (_96508 : real) (_96509 : real) (_96510 : real) (R : type1626) (h1 : term71 R) : term637 R _96508 _96509 _96510.
Proof. exact (@lem7208545 _96508 _96509 R h1 _96510). Qed.
Lemma lem7208547 (R : type1626) (_96508 : real) (_96510 : real) (_96509 : real) : (term637 R _96508 _96509 _96510) = (term612 R _96508 _96510 _96509).
Proof. exact (eq_refl (term637 R _96508 _96509 _96510)). Qed.
Lemma lem7208548 (_96508 : real) (_96510 : real) (_96509 : real) (R : type1626) (h1 : term71 R) : term612 R _96508 _96510 _96509.
Proof. exact (EQ_MP (@lem7208547 R _96508 _96510 _96509) (@lem7208546 _96508 _96509 _96510 R h1)). Qed.
Lemma lem7208549 (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) (R : type1626) (h1 : term71 R) : term638 R _96508 _96510 _96509 _96511.
Proof. exact (@lem7208548 _96508 _96510 _96509 R h1 _96511). Qed.
Lemma lem7208550 (R : type1626) (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) : (term638 R _96508 _96510 _96509 _96511) = (term609 R _96508 _96510 _96509 _96511).
Proof. exact (eq_refl (term638 R _96508 _96510 _96509 _96511)). Qed.
Lemma lem7208567 {A : Type'} (_96517 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term639 A s R f g _96517.
Proof. exact (@lem7208482 A s R f g h1 _96517). Qed.
Lemma lem7208568 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) : (term639 A s R f g _96517) = (term517 A s R f g _96517).
Proof. exact (eq_refl (term639 A s R f g _96517)). Qed.
Lemma lem7208570 {A : Type'} (_96518 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term640 A x R _96518.
Proof. exact (@lem7208539 A x R h1 _96518). Qed.
Lemma lem7208571 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) : (term640 A x R _96518) = (term632 A x R _96518).
Proof. exact (eq_refl (term640 A x R _96518)). Qed.
Lemma lem7208572 {A : Type'} (_96518 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term632 A x R _96518.
Proof. exact (EQ_MP (@lem7208571 A x R _96518) (@lem7208570 A _96518 x R h1)). Qed.
Lemma lem7208573 {A : Type'} (_96518 : A -> real) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term641 A x R _96518 _96519.
Proof. exact (@lem7208572 A _96518 x R h1 _96519). Qed.
Lemma lem7208574 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) : (term641 A x R _96518 _96519) = (term630 A x R _96518 _96519).
Proof. exact (eq_refl (term641 A x R _96518 _96519)). Qed.
Lemma lem7208575 {A : Type'} (_96518 : A -> real) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term630 A x R _96518 _96519.
Proof. exact (EQ_MP (@lem7208574 A x R _96518 _96519) (@lem7208573 A _96518 _96519 x R h1)). Qed.
Lemma lem7208576 {A : Type'} (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term642 A x R _96518 _96519 _96520.
Proof. exact (@lem7208575 A _96518 _96519 x R h1 _96520). Qed.
Lemma lem7208577 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term642 A x R _96518 _96519 _96520) = (term626 A x R _96518 _96520 _96519).
Proof. exact (eq_refl (term642 A x R _96518 _96519 _96520)). Qed.
Lemma lem7208578 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term626 A x R _96518 _96520 _96519.
Proof. exact (EQ_MP (@lem7208577 A x R _96518 _96520 _96519) (@lem7208576 A _96518 _96519 _96520 x R h1)). Qed.
Lemma lem7208579 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term643 A x R _96518 _96520 _96519.
Proof. exact (proj2 (@lem7208578 A _96518 _96520 _96519 x R h1)). Qed.
Lemma lem7208580 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term644 A x R _96518 _96520 _96519.
Proof. exact (proj1 (@lem7208578 A _96518 _96520 _96519 x R h1)). Qed.
Lemma lem7208590 (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) (R : type1626) (h1 : term71 R) : term609 R _96508 _96510 _96509 _96511.
Proof. exact (EQ_MP (@lem7208550 R _96508 _96510 _96509 _96511) (@lem7208549 _96508 _96510 _96509 _96511 R h1)). Qed.
Lemma lem7208604 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term576 R x1 y1 x2 y2.
Proof. exact (proj2 (@lem7208265 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208622 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7208628 {A : Type'} (_96517 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term517 A s R f g _96517.
Proof. exact (EQ_MP (@lem7208568 A s R f g _96517) (@lem7208567 A _96517 s R f g h1)). Qed.
Lemma lem7208630 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term191 A R f s g) : term526 A R f s g.
Proof. exact (EQ_MP (@lem7207958 A R f s g) (@lem7207723 A R f s g h1)). Qed.
Lemma lem7208634 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term644 A x R _96518 _96520 _96519) = (term645 A x R _96518 _96520 _96519).
Proof. exact (@lem7205608 (term558 A _96520) (term622 A x _96518 _96519 _96520) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7208641 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term646 A x R _96518 _96520 _96519) = (term647 A x R _96518 _96520 _96519).
Proof. exact (@lem7205608 (_96520 = (@EMPTY A)) (term551 A x _96518 _96519 _96520) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7208642 {A : Type'} (_96520 : A -> Prop) : (term559 A _96520) = (term559 A _96520).
Proof. exact (eq_refl (term559 A _96520)). Qed.
Lemma lem7208645 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term645 A x R _96518 _96520 _96519) = (term648 A x R _96518 _96520 _96519).
Proof. exact (MK_COMB (@lem7208642 A _96520) (@lem7208641 A x R _96518 _96520 _96519)). Qed.
Lemma lem7208647 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term644 A x R _96518 _96520 _96519) = (term648 A x R _96518 _96520 _96519).
Proof. exact (TRANS (@lem7208634 A x R _96518 _96520 _96519) (@lem7208645 A x R _96518 _96520 _96519)). Qed.
Lemma lem7208648 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term648 A x R _96518 _96520 _96519.
Proof. exact (EQ_MP (@lem7208647 A x R _96518 _96520 _96519) (@lem7208580 A _96518 _96520 _96519 x R h1)). Qed.
Lemma lem7208652 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term643 A x R _96518 _96520 _96519) = (term649 A x R _96518 _96520 _96519).
Proof. exact (@lem7205608 (term558 A _96520) (term623 A R x _96518 _96519 _96520) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7208659 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term650 A x R _96518 _96520 _96519) = (term651 A x R _96518 _96520 _96519).
Proof. exact (@lem7205608 (_96520 = (@EMPTY A)) (term544 A R x _96518 _96519 _96520) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7208660 {A : Type'} (_96520 : A -> Prop) : (term559 A _96520) = (term559 A _96520).
Proof. exact (eq_refl (term559 A _96520)). Qed.
Lemma lem7208663 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term649 A x R _96518 _96520 _96519) = (term652 A x R _96518 _96520 _96519).
Proof. exact (MK_COMB (@lem7208660 A _96520) (@lem7208659 A x R _96518 _96520 _96519)). Qed.
Lemma lem7208665 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term643 A x R _96518 _96520 _96519) = (term652 A x R _96518 _96520 _96519).
Proof. exact (TRANS (@lem7208652 A x R _96518 _96520 _96519) (@lem7208663 A x R _96518 _96520 _96519)). Qed.
Lemma lem7208666 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term652 A x R _96518 _96520 _96519.
Proof. exact (EQ_MP (@lem7208665 A x R _96518 _96520 _96519) (@lem7208579 A _96518 _96520 _96519 x R h1)). Qed.
Lemma lem7208835 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term492 R x1 x2.
Proof. exact (proj1 (@lem7208268 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208836 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term653 R x1 x2.
Proof. exact (fun h0 : term494 R x1 x2 => @lem7208835 R x1 y1 x2 y2 h1). Qed.
Lemma lem7208838 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7208839 (R : type1626) (x1 : real) (x2 : real) : (term653 R x1 x2) = (term492 R x1 x2).
Proof. exact (@lem7208838 (term492 R x1 x2)). Qed.
Lemma lem7208840 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term492 R x1 x2.
Proof. exact (EQ_MP (@lem7208839 R x1 x2) (@lem7208836 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208842 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term492 R y1 y2.
Proof. exact (proj2 (@lem7208268 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208843 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term653 R y1 y2.
Proof. exact (fun h0 : term494 R y1 y2 => @lem7208842 R x1 y1 x2 y2 h1). Qed.
Lemma lem7208845 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7208846 (R : type1626) (y1 : real) (y2 : real) : (term653 R y1 y2) = (term492 R y1 y2).
Proof. exact (@lem7208845 (term492 R y1 y2)). Qed.
Lemma lem7208847 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term492 R y1 y2.
Proof. exact (EQ_MP (@lem7208846 R y1 y2) (@lem7208843 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208863 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7208864 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term496 R _96508 _96510 _96509 _96511) = (term655 _96508 _96509 R _96510 _96511).
Proof. exact (@lem7208863 (term491 R _96508 _96510 _96509 _96511) (term494 R _96510 _96511)). Qed.
Lemma lem7208870 (R : type1626) (_96508 : real) (_96509 : real) : (term495 R _96508 _96509) = (term495 R _96508 _96509).
Proof. exact (eq_refl (term495 R _96508 _96509)). Qed.
Lemma lem7208871 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term609 R _96508 _96510 _96509 _96511) = (term656 _96508 _96509 R _96510 _96511).
Proof. exact (MK_COMB (@lem7208870 R _96508 _96509) (@lem7208864 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208875 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7208876 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term656 _96508 _96509 R _96510 _96511) = (term657 _96508 _96509 R _96510 _96511).
Proof. exact (@lem7208875 (term491 R _96508 _96510 _96509 _96511) (term494 R _96508 _96509) (term494 R _96510 _96511)). Qed.
Lemma lem7208892 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term609 R _96508 _96510 _96509 _96511) = (term657 _96508 _96509 R _96510 _96511).
Proof. exact (TRANS (@lem7208871 _96508 _96509 R _96510 _96511) (@lem7208876 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7208894 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term658 R _96508 _96510 _96509 _96511) = (term659 _96508 _96509 R _96510 _96511).
Proof. exact (MK_COMB (@lem7208893) (@lem7208892 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208910 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term657 _96508 _96509 R _96510 _96511) = (term657 _96508 _96509 R _96510 _96511).
Proof. exact (eq_refl (term657 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208911 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : ((term609 R _96508 _96510 _96509 _96511) = (term657 _96508 _96509 R _96510 _96511)) = ((term657 _96508 _96509 R _96510 _96511) = (term657 _96508 _96509 R _96510 _96511)).
Proof. exact (MK_COMB (@lem7208894 _96508 _96509 R _96510 _96511) (@lem7208910 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7208914 (x : Prop) : (x = x) = True.
Proof. exact (@lem7208913 Prop x). Qed.
Lemma lem7208915 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : ((term657 _96508 _96509 R _96510 _96511) = (term657 _96508 _96509 R _96510 _96511)) = True.
Proof. exact (@lem7208914 (term657 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208916 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : ((term609 R _96508 _96510 _96509 _96511) = (term657 _96508 _96509 R _96510 _96511)) = True.
Proof. exact (TRANS (@lem7208911 _96508 _96509 R _96510 _96511) (@lem7208915 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208917 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : True = ((term609 R _96508 _96510 _96509 _96511) = (term657 _96508 _96509 R _96510 _96511)).
Proof. exact (SYM (@lem7208916 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208918 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term609 R _96508 _96510 _96509 _96511) = (term657 _96508 _96509 R _96510 _96511).
Proof. exact (EQ_MP (@lem7208917 _96508 _96509 R _96510 _96511) (@lem0)). Qed.
Lemma lem7208919 (_96508 : real) (_96509 : real) (_96510 : real) (_96511 : real) (R : type1626) (h1 : term71 R) : term657 _96508 _96509 R _96510 _96511.
Proof. exact (EQ_MP (@lem7208918 _96508 _96509 R _96510 _96511) (@lem7208590 _96508 _96510 _96509 _96511 R h1)). Qed.
Lemma lem7208921 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7208922 (R : type1626) (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) : (term657 _96508 _96509 R _96510 _96511) = (term661 R _96508 _96510 _96509 _96511).
Proof. exact (@lem7208921 (term662 _96508 _96509 R _96510 _96511) (term491 R _96508 _96510 _96509 _96511)). Qed.
Lemma lem7208924 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7208925 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term665 _96508 _96509 R _96510 _96511) = (term666 _96508 _96509 R _96510 _96511).
Proof. exact (@lem7208924 (term494 R _96508 _96509) (term494 R _96510 _96511)). Qed.
Lemma lem7208927 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7208928 (R : type1626) (_96508 : real) (_96509 : real) : (term667 R _96508 _96509) = (term492 R _96508 _96509).
Proof. exact (@lem7208927 (term492 R _96508 _96509)). Qed.
Lemma lem7208929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7208930 (R : type1626) (_96508 : real) (_96509 : real) : (term668 R _96508 _96509) = (term578 R _96508 _96509).
Proof. exact (MK_COMB (@lem7208929) (@lem7208928 R _96508 _96509)). Qed.
Lemma lem7208932 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7208933 (R : type1626) (_96510 : real) (_96511 : real) : (term667 R _96510 _96511) = (term492 R _96510 _96511).
Proof. exact (@lem7208932 (term492 R _96510 _96511)). Qed.
Lemma lem7208934 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term666 _96508 _96509 R _96510 _96511) = (term579 _96508 _96509 R _96510 _96511).
Proof. exact (MK_COMB (@lem7208930 R _96508 _96509) (@lem7208933 R _96510 _96511)). Qed.
Lemma lem7208935 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term665 _96508 _96509 R _96510 _96511) = (term579 _96508 _96509 R _96510 _96511).
Proof. exact (TRANS (@lem7208925 _96508 _96509 R _96510 _96511) (@lem7208934 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208936 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7208937 (_96508 : real) (_96509 : real) (R : type1626) (_96510 : real) (_96511 : real) : (term669 _96508 _96509 R _96510 _96511) = (term670 _96508 _96509 R _96510 _96511).
Proof. exact (MK_COMB (@lem7208936) (@lem7208935 _96508 _96509 R _96510 _96511)). Qed.
Lemma lem7208938 (R : type1626) (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) : (term491 R _96508 _96510 _96509 _96511) = (term491 R _96508 _96510 _96509 _96511).
Proof. exact (eq_refl (term491 R _96508 _96510 _96509 _96511)). Qed.
Lemma lem7208939 (R : type1626) (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) : (term661 R _96508 _96510 _96509 _96511) = (term671 R _96508 _96510 _96509 _96511).
Proof. exact (MK_COMB (@lem7208937 _96508 _96509 R _96510 _96511) (@lem7208938 R _96508 _96510 _96509 _96511)). Qed.
Lemma lem7208940 (R : type1626) (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) : (term657 _96508 _96509 R _96510 _96511) = (term671 R _96508 _96510 _96509 _96511).
Proof. exact (TRANS (@lem7208922 R _96508 _96510 _96509 _96511) (@lem7208939 R _96508 _96510 _96509 _96511)). Qed.
Lemma lem7208942 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term579 x1 x2 R y1 y2.
Proof. exact (conj (@lem7208840 R x1 y1 x2 y2 h1) (@lem7208847 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208944 (_96508 : real) (_96510 : real) (_96509 : real) (_96511 : real) (R : type1626) (h1 : term71 R) : term671 R _96508 _96510 _96509 _96511.
Proof. exact (EQ_MP (@lem7208940 R _96508 _96510 _96509 _96511) (@lem7208919 _96508 _96509 _96510 _96511 R h1)). Qed.
Lemma lem7208945 (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) (h1 : term71 R) : term671 R x1 y1 x2 y2.
Proof. exact (@lem7208944 x1 y1 x2 y2 R h1). Qed.
Lemma lem7208948 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term491 R x1 y1 x2 y2.
Proof. exact (@lem7208945 x1 y1 x2 y2 R h1 (@lem7208942 R x1 y1 x2 y2 h2)). Qed.
Lemma lem7208949 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term672 R x1 y1 x2 y2.
Proof. exact (fun h0 : term576 R x1 y1 x2 y2 => @lem7208948 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7208951 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7208952 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term672 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (@lem7208951 (term491 R x1 y1 x2 y2)). Qed.
Lemma lem7208953 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term491 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7208952 R x1 y1 x2 y2) (@lem7208949 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7208956 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7208958 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term576 R x1 y1 x2 y2) = (term673 R x1 y1 x2 y2).
Proof. exact (@lem7208956 (term491 R x1 y1 x2 y2)). Qed.
Lemma lem7208961 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term582 R x1 y1 x2 y2) : term673 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7208958 R x1 y1 x2 y2) (@lem7208604 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7208964 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : False.
Proof. exact (@lem7208961 R x1 y1 x2 y2 h2 (@lem7208953 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7208965 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term674.
Proof. exact (fun h0 : ~ False => @lem7208964 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7208967 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7208968 : term674 = False.
Proof. exact (@lem7208967 False). Qed.
Lemma lem7208969 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : False.
Proof. exact (EQ_MP (@lem7208968) (@lem7208965 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7209189 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7207842 A s) (@lem7207648 A s h1)). Qed.
Lemma lem7209190 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term675 A s.
Proof. exact (fun h0 : term558 A s => @lem7209189 A s h1). Qed.
Lemma lem7209192 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7209193 {A : Type'} (s : A -> Prop) : (term675 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7209192 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7209194 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7209193 A s) (@lem7209190 A s h1)). Qed.
Lemma lem7209196 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7209197 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term676 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem7209196 A s h1). Qed.
Lemma lem7209199 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7209200 {A : Type'} (s : A -> Prop) : (term676 A s) = (term79 A s).
Proof. exact (@lem7209199 (s = (@EMPTY A))). Qed.
Lemma lem7209201 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (EQ_MP (@lem7209200 A s) (@lem7209197 A s h1)). Qed.
Lemma lem7209203 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7207842 A s) (@lem7207648 A s h1)). Qed.
Lemma lem7209204 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term675 A s.
Proof. exact (fun h0 : term558 A s => @lem7209203 A s h1). Qed.
Lemma lem7209206 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7209207 {A : Type'} (s : A -> Prop) : (term675 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7209206 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7209208 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7209207 A s) (@lem7209204 A s h1)). Qed.
Lemma lem7209210 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7209211 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term676 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem7209210 A s h1). Qed.
Lemma lem7209213 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7209214 {A : Type'} (s : A -> Prop) : (term676 A s) = (term79 A s).
Proof. exact (@lem7209213 (s = (@EMPTY A))). Qed.
Lemma lem7209215 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (EQ_MP (@lem7209214 A s) (@lem7209211 A s h1)). Qed.
Lemma lem7209218 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term526 A R f s g) : term526 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7209219 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term526 A R f s g) : term678 A R f s g.
Proof. exact (fun h0 : term525 A R f s g => @lem7209218 A R f s g h1). Qed.
Lemma lem7209221 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7209222 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term678 A R f s g) = (term526 A R f s g).
Proof. exact (@lem7209221 (term525 A R f s g)). Qed.
Lemma lem7209223 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term526 A R f s g) : term526 A R f s g.
Proof. exact (EQ_MP (@lem7209222 A R f s g) (@lem7209219 A R f s g h1)). Qed.
Lemma lem7209229 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209230 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term648 A x R _96518 _96520 _96519) = (term679 A x R _96518 _96520 _96519).
Proof. exact (@lem7209229 (_96520 = (@EMPTY A)) (term558 A _96520) (term680 A x R _96518 _96520 _96519)). Qed.
Lemma lem7209246 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209247 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term681 A x R _96518 _96520 _96519) = (term682 A x R _96518 _96520 _96519).
Proof. exact (@lem7209246 (term551 A x _96518 _96519 _96520) (term558 A _96520) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7209261 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7209262 {A : Type'} (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term683 A R _96518 _96520 _96519) = (term684 A R _96518 _96519 _96520).
Proof. exact (@lem7209261 (term525 A R _96518 _96520 _96519) (term558 A _96520)). Qed.
Lemma lem7209268 {A : Type'} (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term685 A x _96518 _96519 _96520) = (term685 A x _96518 _96519 _96520).
Proof. exact (eq_refl (term685 A x _96518 _96519 _96520)). Qed.
Lemma lem7209269 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term682 A x R _96518 _96520 _96519) = (term686 A x R _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209268 A x _96518 _96519 _96520) (@lem7209262 A R _96518 _96519 _96520)). Qed.
Lemma lem7209280 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term681 A x R _96518 _96520 _96519) = (term686 A x R _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209247 A x R _96518 _96520 _96519) (@lem7209269 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209281 {A : Type'} (_96520 : A -> Prop) : (term251 A _96520) = (term251 A _96520).
Proof. exact (eq_refl (term251 A _96520)). Qed.
Lemma lem7209282 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term679 A x R _96518 _96520 _96519) = (term687 A x R _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209281 A _96520) (@lem7209280 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209293 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term648 A x R _96518 _96520 _96519) = (term687 A x R _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209230 A x R _96518 _96520 _96519) (@lem7209282 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7209295 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term688 A x R _96518 _96520 _96519) = (term689 A x R _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209294) (@lem7209293 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209309 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209310 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term690 A R _96518 _96520 _96519) = (term691 A R _96518 _96520 _96519).
Proof. exact (@lem7209309 (_96520 = (@EMPTY A)) (term558 A _96520) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7209326 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7209327 {A : Type'} (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term683 A R _96518 _96520 _96519) = (term684 A R _96518 _96519 _96520).
Proof. exact (@lem7209326 (term525 A R _96518 _96520 _96519) (term558 A _96520)). Qed.
Lemma lem7209333 {A : Type'} (_96520 : A -> Prop) : (term251 A _96520) = (term251 A _96520).
Proof. exact (eq_refl (term251 A _96520)). Qed.
Lemma lem7209334 {A : Type'} (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term691 A R _96518 _96520 _96519) = (term692 A R _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209333 A _96520) (@lem7209327 A R _96518 _96519 _96520)). Qed.
Lemma lem7209345 {A : Type'} (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term690 A R _96518 _96520 _96519) = (term692 A R _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209310 A R _96518 _96520 _96519) (@lem7209334 A R _96518 _96519 _96520)). Qed.
Lemma lem7209346 {A : Type'} (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term685 A x _96518 _96519 _96520) = (term685 A x _96518 _96519 _96520).
Proof. exact (eq_refl (term685 A x _96518 _96519 _96520)). Qed.
Lemma lem7209347 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term693 A x R _96518 _96520 _96519) = (term694 A x R _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209346 A x _96518 _96519 _96520) (@lem7209345 A R _96518 _96519 _96520)). Qed.
Lemma lem7209351 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209352 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term694 A x R _96518 _96519 _96520) = (term687 A x R _96518 _96519 _96520).
Proof. exact (@lem7209351 (_96520 = (@EMPTY A)) (term551 A x _96518 _96519 _96520) (term684 A R _96518 _96519 _96520)). Qed.
Lemma lem7209380 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term693 A x R _96518 _96520 _96519) = (term687 A x R _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209347 A x R _96518 _96519 _96520) (@lem7209352 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209381 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : ((term648 A x R _96518 _96520 _96519) = (term693 A x R _96518 _96520 _96519)) = ((term687 A x R _96518 _96519 _96520) = (term687 A x R _96518 _96519 _96520)).
Proof. exact (MK_COMB (@lem7209295 A x R _96518 _96519 _96520) (@lem7209380 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7209384 (x : Prop) : (x = x) = True.
Proof. exact (@lem7209383 Prop x). Qed.
Lemma lem7209385 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : ((term687 A x R _96518 _96519 _96520) = (term687 A x R _96518 _96519 _96520)) = True.
Proof. exact (@lem7209384 (term687 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209386 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : ((term648 A x R _96518 _96520 _96519) = (term693 A x R _96518 _96520 _96519)) = True.
Proof. exact (TRANS (@lem7209381 A x R _96518 _96519 _96520) (@lem7209385 A x R _96518 _96519 _96520)). Qed.
Lemma lem7209387 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : True = ((term648 A x R _96518 _96520 _96519) = (term693 A x R _96518 _96520 _96519)).
Proof. exact (SYM (@lem7209386 A x R _96518 _96520 _96519)). Qed.
Lemma lem7209388 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term648 A x R _96518 _96520 _96519) = (term693 A x R _96518 _96520 _96519).
Proof. exact (EQ_MP (@lem7209387 A x R _96518 _96520 _96519) (@lem0)). Qed.
Lemma lem7209389 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term693 A x R _96518 _96520 _96519.
Proof. exact (EQ_MP (@lem7209388 A x R _96518 _96520 _96519) (@lem7208648 A _96518 _96520 _96519 x R h1)). Qed.
Lemma lem7209391 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7209392 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term693 A x R _96518 _96520 _96519) = (term695 A R x _96518 _96519 _96520).
Proof. exact (@lem7209391 (term690 A R _96518 _96520 _96519) (term551 A x _96518 _96519 _96520)). Qed.
Lemma lem7209394 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7209395 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term696 A R _96518 _96520 _96519) = (term697 A R _96518 _96520 _96519).
Proof. exact (@lem7209394 (term558 A _96520) (term698 A R _96518 _96520 _96519)). Qed.
Lemma lem7209397 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7209398 {A : Type'} (_96520 : A -> Prop) : (term699 A _96520) = (@I ((A -> Prop) -> Prop) (@FINITE A) _96520).
Proof. exact (@lem7209397 (@I ((A -> Prop) -> Prop) (@FINITE A) _96520)). Qed.
Lemma lem7209399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7209400 {A : Type'} (_96520 : A -> Prop) : (term700 A _96520) = (term701 A _96520).
Proof. exact (MK_COMB (@lem7209399) (@lem7209398 A _96520)). Qed.
Lemma lem7209402 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7209403 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term702 A R _96518 _96520 _96519) = (term703 A R _96518 _96520 _96519).
Proof. exact (@lem7209402 (_96520 = (@EMPTY A)) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7209404 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term697 A R _96518 _96520 _96519) = (term704 A R _96518 _96520 _96519).
Proof. exact (MK_COMB (@lem7209400 A _96520) (@lem7209403 A R _96518 _96520 _96519)). Qed.
Lemma lem7209405 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term696 A R _96518 _96520 _96519) = (term704 A R _96518 _96520 _96519).
Proof. exact (TRANS (@lem7209395 A R _96518 _96520 _96519) (@lem7209404 A R _96518 _96520 _96519)). Qed.
Lemma lem7209406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7209407 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term705 A R _96518 _96520 _96519) = (term706 A R _96518 _96520 _96519).
Proof. exact (MK_COMB (@lem7209406) (@lem7209405 A R _96518 _96520 _96519)). Qed.
Lemma lem7209408 {A : Type'} (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term551 A x _96518 _96519 _96520) = (term551 A x _96518 _96519 _96520).
Proof. exact (eq_refl (term551 A x _96518 _96519 _96520)). Qed.
Lemma lem7209409 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term695 A R x _96518 _96519 _96520) = (term707 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209407 A R _96518 _96520 _96519) (@lem7209408 A x _96518 _96519 _96520)). Qed.
Lemma lem7209410 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term693 A x R _96518 _96520 _96519) = (term707 A R x _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209392 A R x _96518 _96519 _96520) (@lem7209409 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209412 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term79 A s) (h2 : term526 A R f s g) : term703 A R f s g.
Proof. exact (conj (@lem7209215 A s h1) (@lem7209223 A R f s g h2)). Qed.
Lemma lem7209413 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : @FINITE A s) (h2 : term79 A s) (h3 : term526 A R f s g) : term704 A R f s g.
Proof. exact (conj (@lem7209208 A s h1) (@lem7209412 A R f s g h2 h3)). Qed.
Lemma lem7209415 {A : Type'} (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term707 A R x _96518 _96519 _96520.
Proof. exact (EQ_MP (@lem7209410 A R x _96518 _96519 _96520) (@lem7209389 A _96518 _96520 _96519 x R h1)). Qed.
Lemma lem7209416 {A : Type'} (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term707 A R x _96518 _96519 _96520.
Proof. exact (@lem7209415 A _96518 _96519 _96520 x R h1). Qed.
Lemma lem7209417 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term707 A R x f g s.
Proof. exact (@lem7209416 A f g s x R h1). Qed.
Lemma lem7209420 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term574 A x R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term526 A R f s g) : term551 A x f g s.
Proof. exact (@lem7209417 A f g s x R h1 (@lem7209413 A R f s g h2 h3 h4)). Qed.
Lemma lem7209421 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term574 A x R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term526 A R f s g) : term708 A x f g s.
Proof. exact (fun h0 : term709 A x f g s => @lem7209420 A x R f s g h1 h2 h3 h4). Qed.
Lemma lem7209423 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7209424 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term708 A x f g s) = (term551 A x f g s).
Proof. exact (@lem7209423 (term551 A x f g s)). Qed.
Lemma lem7209425 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term574 A x R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term526 A R f s g) : term551 A x f g s.
Proof. exact (EQ_MP (@lem7209424 A x f g s) (@lem7209421 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7209431 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7209432 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : (term517 A s R f g _96517) = (term710 A R f g _96517 s).
Proof. exact (@lem7209431 (term511 A R f g _96517) (term514 A _96517 s)). Qed.
Lemma lem7209438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7209439 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : (term711 A s R f g _96517) = (term712 A R f g _96517 s).
Proof. exact (MK_COMB (@lem7209438) (@lem7209432 A R f g _96517 s)). Qed.
Lemma lem7209445 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : (term710 A R f g _96517 s) = (term710 A R f g _96517 s).
Proof. exact (eq_refl (term710 A R f g _96517 s)). Qed.
Lemma lem7209446 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : ((term517 A s R f g _96517) = (term710 A R f g _96517 s)) = ((term710 A R f g _96517 s) = (term710 A R f g _96517 s)).
Proof. exact (MK_COMB (@lem7209439 A R f g _96517 s) (@lem7209445 A R f g _96517 s)). Qed.
Lemma lem7209448 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7209449 (x : Prop) : (x = x) = True.
Proof. exact (@lem7209448 Prop x). Qed.
Lemma lem7209450 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : ((term710 A R f g _96517 s) = (term710 A R f g _96517 s)) = True.
Proof. exact (@lem7209449 (term710 A R f g _96517 s)). Qed.
Lemma lem7209451 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : ((term517 A s R f g _96517) = (term710 A R f g _96517 s)) = True.
Proof. exact (TRANS (@lem7209446 A R f g _96517 s) (@lem7209450 A R f g _96517 s)). Qed.
Lemma lem7209452 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : True = ((term517 A s R f g _96517) = (term710 A R f g _96517 s)).
Proof. exact (SYM (@lem7209451 A R f g _96517 s)). Qed.
Lemma lem7209453 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) (s : A -> Prop) : (term517 A s R f g _96517) = (term710 A R f g _96517 s).
Proof. exact (EQ_MP (@lem7209452 A R f g _96517 s) (@lem0)). Qed.
Lemma lem7209454 {A : Type'} (_96517 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term710 A R f g _96517 s.
Proof. exact (EQ_MP (@lem7209453 A R f g _96517 s) (@lem7208628 A _96517 s R f g h1)). Qed.
Lemma lem7209456 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7209457 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) : (term710 A R f g _96517 s) = (term713 A s R f g _96517).
Proof. exact (@lem7209456 (term514 A _96517 s) (term511 A R f g _96517)). Qed.
Lemma lem7209459 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7209460 {A : Type'} (_96517 : A) (s : A -> Prop) : (term714 A _96517 s) = (term512 A _96517 s).
Proof. exact (@lem7209459 (term512 A _96517 s)). Qed.
Lemma lem7209461 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7209462 {A : Type'} (_96517 : A) (s : A -> Prop) : (term715 A _96517 s) = (term716 A _96517 s).
Proof. exact (MK_COMB (@lem7209461) (@lem7209460 A _96517 s)). Qed.
Lemma lem7209463 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) : (term511 A R f g _96517) = (term511 A R f g _96517).
Proof. exact (eq_refl (term511 A R f g _96517)). Qed.
Lemma lem7209464 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) : (term713 A s R f g _96517) = (term717 A s R f g _96517).
Proof. exact (MK_COMB (@lem7209462 A _96517 s) (@lem7209463 A R f g _96517)). Qed.
Lemma lem7209465 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96517 : A) : (term710 A R f g _96517 s) = (term717 A s R f g _96517).
Proof. exact (TRANS (@lem7209457 A s R f g _96517) (@lem7209464 A s R f g _96517)). Qed.
Lemma lem7209468 {A : Type'} (_96517 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term717 A s R f g _96517.
Proof. exact (EQ_MP (@lem7209465 A s R f g _96517) (@lem7209454 A _96517 s R f g h1)). Qed.
Lemma lem7209469 {A : Type'} (_96517 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term717 A s R f g _96517.
Proof. exact (@lem7209468 A _96517 s R f g h1). Qed.
Lemma lem7209470 {A : Type'} (x : type711 A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term718 A R x f g s.
Proof. exact (@lem7209469 A (term529 A x f g s) s R f g h1). Qed.
Lemma lem7209473 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term542 A R x f g s.
Proof. exact (@lem7209470 A x s R f g h1 (@lem7209425 A x R f s g h2 h3 h4 h5)). Qed.
Lemma lem7209474 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term719 A R x f g s.
Proof. exact (fun h0 : term544 A R x f g s => @lem7209473 A x R f s g h1 h2 h3 h4 h5). Qed.
Lemma lem7209476 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7209477 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term719 A R x f g s) = (term542 A R x f g s).
Proof. exact (@lem7209476 (term542 A R x f g s)). Qed.
Lemma lem7209478 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term542 A R x f g s.
Proof. exact (EQ_MP (@lem7209477 A R x f g s) (@lem7209474 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7209484 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209485 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term652 A x R _96518 _96520 _96519) = (term720 A x R _96518 _96520 _96519).
Proof. exact (@lem7209484 (_96520 = (@EMPTY A)) (term558 A _96520) (term721 A x R _96518 _96520 _96519)). Qed.
Lemma lem7209511 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7209512 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term721 A x R _96518 _96520 _96519) = (term722 A R x _96518 _96519 _96520).
Proof. exact (@lem7209511 (term525 A R _96518 _96520 _96519) (term544 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209518 {A : Type'} (_96520 : A -> Prop) : (term559 A _96520) = (term559 A _96520).
Proof. exact (eq_refl (term559 A _96520)). Qed.
Lemma lem7209519 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term723 A x R _96518 _96520 _96519) = (term724 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209518 A _96520) (@lem7209512 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209523 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209524 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term724 A R x _96518 _96519 _96520) = (term725 A R x _96518 _96519 _96520).
Proof. exact (@lem7209523 (term525 A R _96518 _96520 _96519) (term558 A _96520) (term544 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209540 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term723 A x R _96518 _96520 _96519) = (term725 A R x _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209519 A R x _96518 _96519 _96520) (@lem7209524 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209541 {A : Type'} (_96520 : A -> Prop) : (term251 A _96520) = (term251 A _96520).
Proof. exact (eq_refl (term251 A _96520)). Qed.
Lemma lem7209542 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term720 A x R _96518 _96520 _96519) = (term726 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209541 A _96520) (@lem7209540 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209553 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term652 A x R _96518 _96520 _96519) = (term726 A R x _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209485 A x R _96518 _96520 _96519) (@lem7209542 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7209555 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term727 A x R _96518 _96520 _96519) = (term728 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209554) (@lem7209553 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209569 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209570 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term628 A R x _96518 _96519 _96520) = (term729 A R x _96518 _96519 _96520).
Proof. exact (@lem7209569 (_96520 = (@EMPTY A)) (term558 A _96520) (term544 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209588 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term730 A R _96518 _96520 _96519) = (term730 A R _96518 _96520 _96519).
Proof. exact (eq_refl (term730 A R _96518 _96520 _96519)). Qed.
Lemma lem7209589 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term731 A R x _96518 _96519 _96520) = (term732 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209588 A R _96518 _96520 _96519) (@lem7209570 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209593 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7209594 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term732 A R x _96518 _96519 _96520) = (term726 A R x _96518 _96519 _96520).
Proof. exact (@lem7209593 (_96520 = (@EMPTY A)) (term525 A R _96518 _96520 _96519) (term733 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209622 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term731 A R x _96518 _96519 _96520) = (term726 A R x _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209589 A R x _96518 _96519 _96520) (@lem7209594 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209623 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : ((term652 A x R _96518 _96520 _96519) = (term731 A R x _96518 _96519 _96520)) = ((term726 A R x _96518 _96519 _96520) = (term726 A R x _96518 _96519 _96520)).
Proof. exact (MK_COMB (@lem7209555 A R x _96518 _96519 _96520) (@lem7209622 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209625 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7209626 (x : Prop) : (x = x) = True.
Proof. exact (@lem7209625 Prop x). Qed.
Lemma lem7209627 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : ((term726 A R x _96518 _96519 _96520) = (term726 A R x _96518 _96519 _96520)) = True.
Proof. exact (@lem7209626 (term726 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209628 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : ((term652 A x R _96518 _96520 _96519) = (term731 A R x _96518 _96519 _96520)) = True.
Proof. exact (TRANS (@lem7209623 A R x _96518 _96519 _96520) (@lem7209627 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209629 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : True = ((term652 A x R _96518 _96520 _96519) = (term731 A R x _96518 _96519 _96520)).
Proof. exact (SYM (@lem7209628 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209630 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term652 A x R _96518 _96520 _96519) = (term731 A R x _96518 _96519 _96520).
Proof. exact (EQ_MP (@lem7209629 A R x _96518 _96519 _96520) (@lem0)). Qed.
Lemma lem7209631 {A : Type'} (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term731 A R x _96518 _96519 _96520.
Proof. exact (EQ_MP (@lem7209630 A R x _96518 _96519 _96520) (@lem7208666 A _96518 _96520 _96519 x R h1)). Qed.
Lemma lem7209633 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7209634 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term731 A R x _96518 _96519 _96520) = (term734 A x R _96518 _96520 _96519).
Proof. exact (@lem7209633 (term628 A R x _96518 _96519 _96520) (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7209636 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7209637 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term735 A R x _96518 _96519 _96520) = (term736 A R x _96518 _96519 _96520).
Proof. exact (@lem7209636 (term558 A _96520) (term623 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209639 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7209640 {A : Type'} (_96520 : A -> Prop) : (term699 A _96520) = (@I ((A -> Prop) -> Prop) (@FINITE A) _96520).
Proof. exact (@lem7209639 (@I ((A -> Prop) -> Prop) (@FINITE A) _96520)). Qed.
Lemma lem7209641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7209642 {A : Type'} (_96520 : A -> Prop) : (term700 A _96520) = (term701 A _96520).
Proof. exact (MK_COMB (@lem7209641) (@lem7209640 A _96520)). Qed.
Lemma lem7209644 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7209645 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term737 A R x _96518 _96519 _96520) = (term738 A R x _96518 _96519 _96520).
Proof. exact (@lem7209644 (_96520 = (@EMPTY A)) (term544 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209647 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7209648 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term739 A R x _96518 _96519 _96520) = (term542 A R x _96518 _96519 _96520).
Proof. exact (@lem7209647 (term542 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209649 {A : Type'} (_96520 : A -> Prop) : (term182 A _96520) = (term182 A _96520).
Proof. exact (eq_refl (term182 A _96520)). Qed.
Lemma lem7209650 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term738 A R x _96518 _96519 _96520) = (term740 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209649 A _96520) (@lem7209648 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209651 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term737 A R x _96518 _96519 _96520) = (term740 A R x _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209645 A R x _96518 _96519 _96520) (@lem7209650 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209652 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term736 A R x _96518 _96519 _96520) = (term741 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209642 A _96520) (@lem7209651 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209653 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term735 A R x _96518 _96519 _96520) = (term741 A R x _96518 _96519 _96520).
Proof. exact (TRANS (@lem7209637 A R x _96518 _96519 _96520) (@lem7209652 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209654 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7209655 {A : Type'} (R : type1626) (x : type711 A) (_96518 : A -> real) (_96519 : A -> real) (_96520 : A -> Prop) : (term742 A R x _96518 _96519 _96520) = (term743 A R x _96518 _96519 _96520).
Proof. exact (MK_COMB (@lem7209654) (@lem7209653 A R x _96518 _96519 _96520)). Qed.
Lemma lem7209656 {A : Type'} (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term525 A R _96518 _96520 _96519) = (term525 A R _96518 _96520 _96519).
Proof. exact (eq_refl (term525 A R _96518 _96520 _96519)). Qed.
Lemma lem7209657 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term734 A x R _96518 _96520 _96519) = (term744 A x R _96518 _96520 _96519).
Proof. exact (MK_COMB (@lem7209655 A R x _96518 _96519 _96520) (@lem7209656 A R _96518 _96520 _96519)). Qed.
Lemma lem7209658 {A : Type'} (x : type711 A) (R : type1626) (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) : (term731 A R x _96518 _96519 _96520) = (term744 A x R _96518 _96520 _96519).
Proof. exact (TRANS (@lem7209634 A x R _96518 _96520 _96519) (@lem7209657 A x R _96518 _96520 _96519)). Qed.
Lemma lem7209660 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term740 A R x f g s.
Proof. exact (conj (@lem7209201 A s h4) (@lem7209478 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7209661 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term741 A R x f g s.
Proof. exact (conj (@lem7209194 A s h3) (@lem7209660 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7209663 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term744 A x R _96518 _96520 _96519.
Proof. exact (EQ_MP (@lem7209658 A x R _96518 _96520 _96519) (@lem7209631 A _96518 _96519 _96520 x R h1)). Qed.
Lemma lem7209664 {A : Type'} (_96518 : A -> real) (_96520 : A -> Prop) (_96519 : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term744 A x R _96518 _96520 _96519.
Proof. exact (@lem7209663 A _96518 _96520 _96519 x R h1). Qed.
Lemma lem7209665 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x : type711 A) (R : type1626) (h1 : term574 A x R) : term744 A x R f s g.
Proof. exact (@lem7209664 A f s g x R h1). Qed.
Lemma lem7209668 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term525 A R f s g.
Proof. exact (@lem7209665 A f s g x R h2 (@lem7209661 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7209669 {A : Type'} (f : A -> real) (g : A -> real) (x : type711 A) (R : type1626) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) : term745 A R f s g.
Proof. exact (fun h0 : term526 A R f s g => @lem7209668 A x R f s g h1 h2 h3 h4 h0). Qed.
Lemma lem7209671 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7209672 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term745 A R f s g) = (term525 A R f s g).
Proof. exact (@lem7209671 (term525 A R f s g)). Qed.
Lemma lem7209673 {A : Type'} (f : A -> real) (g : A -> real) (x : type711 A) (R : type1626) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) : term525 A R f s g.
Proof. exact (EQ_MP (@lem7209672 A R f s g) (@lem7209669 A f g x R s h1 h2 h3 h4)). Qed.
Lemma lem7209676 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7209678 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term526 A R f s g) = (term746 A R f s g).
Proof. exact (@lem7209676 (term525 A R f s g)). Qed.
Lemma lem7209681 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term191 A R f s g) : term746 A R f s g.
Proof. exact (EQ_MP (@lem7209678 A R f s g) (@lem7208630 A R f s g h1)). Qed.
Lemma lem7209684 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (@lem7209681 A R f s g h5 (@lem7209673 A f g x R s h1 h2 h3 h4)). Qed.
Lemma lem7209685 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : term674.
Proof. exact (fun h0 : ~ False => @lem7209684 A x R f s g h1 h2 h3 h4 h5). Qed.
Lemma lem7209687 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7209688 : term674 = False.
Proof. exact (@lem7209687 False). Qed.
Lemma lem7209689 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7209688) (@lem7209685 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7209690 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : (term79 A s) = False.
Proof. exact (prop_ext (fun h6 : term79 A s => @lem7209689 A x R f s g h1 h2 h3 h4 h5) (fun h6 : False => @lem7208622 A s h4)). Qed.
Lemma lem7209691 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7209690 A x R f s g h1 h2 h3 h4 h5) (@lem7208622 A s h4)). Qed.
Lemma lem7209692 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : (term79 A s) = False.
Proof. exact (prop_ext (fun h6 : term79 A s => @lem7209691 A x R f s g h1 h2 h3 h4 h5) (fun h6 : False => @lem7208469 A s h4)). Qed.
Lemma lem7209693 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7209692 A x R f s g h1 h2 h3 h4 h5) (@lem7208469 A s h4)). Qed.
Lemma lem7209694 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : (term79 A s) = False.
Proof. exact (prop_ext (fun h6 : term79 A s => @lem7209693 A x R f s g h1 h2 h3 h4 h5) (fun h6 : False => @lem7208469 A s h4)). Qed.
Lemma lem7209695 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7209694 A x R f s g h1 h2 h3 h4 h5) (@lem7208469 A s h4)). Qed.
Lemma lem7209696 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term470 A x1 y1 x2 y2 x R) : False.
Proof. exact (or_elim (@lem7208264 A x1 y1 x2 y2 x R h6) (fun h0 : term582 R x1 y1 x2 y2 => @lem7208969 R x1 y1 x2 y2 h2 h0) (fun h0 : term574 A x R => @lem7209695 A x R f s g h1 h0 h3 h4 h5)). Qed.
Lemma lem7209697 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term470 A x1 y1 x2 y2 x R) : (term79 A s) = False.
Proof. exact (prop_ext (fun h7 : term79 A s => @lem7209696 A f s g x1 y1 x2 y2 x R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7207851 A s h4)). Qed.
Lemma lem7209698 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term470 A x1 y1 x2 y2 x R) : False.
Proof. exact (EQ_MP (@lem7209697 A f s g x1 y1 x2 y2 x R h1 h2 h3 h4 h5 h6) (@lem7207851 A s h4)). Qed.
Lemma lem7209699 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term473 A x1 y1 x2 y2 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7207727 A x1 y1 x2 y2 R h3) (fun x : type711 A => fun h0 : term472 A x1 y1 x2 y2 R x => @lem7209698 A f s g x1 y1 x2 y2 x R h1 h2 h4 h5 h6 h0)). Qed.
Lemma lem7209700 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term475 A x1 y1 x2 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7207726 A x1 y1 x2 R h3) (fun y2 : real => fun h0 : term474 A x1 y1 x2 R y2 => @lem7209699 A x1 y1 x2 y2 R f s g h1 h2 h0 h4 h5 h6)). Qed.
Lemma lem7209701 {A : Type'} (x1 : real) (y1 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term477 A x1 y1 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7207725 A x1 y1 R h3) (fun x2 : real => fun h0 : term476 A x1 y1 R x2 => @lem7209700 A x1 y1 x2 R f s g h1 h2 h0 h4 h5 h6)). Qed.
Lemma lem7209702 {A : Type'} (x1 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term479 A x1 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7207724 A x1 R h3) (fun y1 : real => fun h0 : term478 A x1 R y1 => @lem7209701 A x1 y1 R f s g h1 h2 h0 h4 h5 h6)). Qed.
Lemma lem7209703 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (ex_elim (@lem7207642 A R h6) (fun x1 : real => fun h0 : term480 A R x1 => @lem7209702 A x1 R f s g h1 h2 h0 h3 h4 h5)). Qed.
Lemma lem7209704 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (term191 A R f s g) = False.
Proof. exact (prop_ext (fun h7 : term191 A R f s g => @lem7209703 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7207723 A R f s g h5)). Qed.
Lemma lem7209705 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7209704 A f s g R h1 h2 h3 h4 h5 h6) (@lem7207723 A R f s g h5)). Qed.
Lemma lem7209706 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (term79 A s) = False.
Proof. exact (prop_ext (fun h7 : term79 A s => @lem7209705 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7207654 A s h4)). Qed.
Lemma lem7209707 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7209706 A f s g R h1 h2 h3 h4 h5 h6) (@lem7207654 A s h4)). Qed.
Lemma lem7209708 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE A s => @lem7209707 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7207648 A s h3)). Qed.
Lemma lem7209709 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7209708 A f s g R h1 h2 h3 h4 h5 h6) (@lem7207648 A s h3)). Qed.
Lemma lem7209710 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (term191 A R f s g) = False.
Proof. exact (prop_ext (fun h7 : term191 A R f s g => @lem7209709 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7206921 A R f s g h5)). Qed.
Lemma lem7209711 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7209710 A f s g R h1 h2 h3 h4 h5 h6) (@lem7206921 A R f s g h5)). Qed.
Lemma lem7209712 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term158 A R) : term190 A R f s g.
Proof. exact (fun h0 : term191 A R f s g => @lem7209711 A f s g R h1 h2 h3 h4 h0 h5). Qed.
Lemma lem7209713 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (R : type1626) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term158 A R) : term25 A R f s g.
Proof. exact (EQ_MP (@lem7206920 A R f s g) (@lem7209712 A f g s R h1 h2 h3 h4 h5)). Qed.
Lemma lem7209714 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (R : type1626) (h1 : term71 R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term158 A R) : term180 A R f s g.
Proof. exact (fun h0 : term80 A s R f g => @lem7209713 A f g s R h0 h1 h2 h3 h4). Qed.
Lemma lem7209715 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (R : type1626) (h1 : term71 R) (h2 : @FINITE A s) (h3 : term158 A R) : term78 A R f s g.
Proof. exact (fun h0 : term79 A s => @lem7209714 A f g s R h1 h2 h0 h3). Qed.
Lemma lem7209716 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term71 R) (h2 : term158 A R) : term82 A R f s g.
Proof. exact (fun h0 : @FINITE A s => @lem7209715 A f g s R h1 h0 h2). Qed.
Lemma lem7209721 {A : Type'} (f : A -> real) (g : A -> real) (R : type1626) (h1 : term71 R) (h2 : term158 A R) : term100 A R f g.
Proof. exact (fun s : A -> Prop => @lem7209716 A f s g R h1 h2). Qed.
Lemma lem7209726 {A : Type'} (f : A -> real) (R : type1626) (h1 : term71 R) (h2 : term158 A R) : term118 A R f.
Proof. exact (fun g : A -> real => @lem7209721 A f g R h1 h2). Qed.
Lemma lem7209731 {A : Type'} (R : type1626) (h1 : term71 R) (h2 : term158 A R) : term134 A R.
Proof. exact (fun f : A -> real => @lem7209726 A f R h1 h2). Qed.
Lemma lem7209732 {A : Type'} (R : type1626) (h1 : term71 R) : term162 A R.
Proof. exact (fun h0 : term158 A R => @lem7209731 A R h1 h0). Qed.
Lemma lem7209733 {A : Type'} (R : type1626) : term172 A R.
Proof. exact (fun h0 : term71 R => @lem7209732 A R h0). Qed.
Lemma lem7209738 {A : Type'} : term176 A.
Proof. exact (fun R : type1626 => @lem7209733 A R). Qed.
Lemma lem7209739 {A : Type'} : term175 A.
Proof. exact (EQ_MP (@lem7206911 A) (@lem7209738 A)). Qed.
Lemma lem7209740 {A : Type'} (R : type1626) : term747 A R.
Proof. exact (@lem7209739 A R). Qed.
Lemma lem7209741 {A : Type'} (R : type1626) : (term747 A R) = (term166 A R).
Proof. exact (eq_refl (term747 A R)). Qed.
Lemma lem7209742 {A : Type'} (R : type1626) : term166 A R.
Proof. exact (EQ_MP (@lem7209741 A R) (@lem7209740 A R)). Qed.
Lemma lem7209744 {A : Type'} (R : type1626) : term166 A R.
Proof. exact (@lem7206539 A R (@lem7209742 A R)). Qed.
Lemma lem7209745 {A : Type'} (R : type1626) (h1 : term71 R) : term164 A R.
Proof. exact (@lem7209744 A R (@lem7206381 R h1)). Qed.
Lemma lem7209746 {A : Type'} (R : type1626) (h1 : term71 R) (h2 : term165 A R) : False.
Proof. exact (@lem7209745 A R h1 (@lem7206523 A R h2)). Qed.
Lemma lem7209747 {A : Type'} (R : type1626) (h1 : term71 R) (h2 : term165 A R) : (term165 A R) = False.
Proof. exact (prop_ext (fun h3 : term165 A R => @lem7209746 A R h1 h2) (fun h3 : False => @lem7206523 A R h2)). Qed.
Lemma lem7209748 {A : Type'} (R : type1626) (h1 : term71 R) (h2 : term165 A R) : False.
Proof. exact (EQ_MP (@lem7209747 A R h1 h2) (@lem7206523 A R h2)). Qed.
Lemma lem7209749 {A : Type'} (R : type1626) (h1 : term71 R) : term164 A R.
Proof. exact (fun h0 : term165 A R => @lem7209748 A R h1 h0). Qed.
Lemma lem7209750 {A : Type'} (R : type1626) (h1 : term71 R) : term162 A R.
Proof. exact (EQ_MP (@lem7206522 A R) (@lem7209749 A R h1)). Qed.
Lemma lem7209751 {A : Type'} (R : type1626) (h1 : term71 R) : term161 A R.
Proof. exact (EQ_MP (@lem7206518 A R) (@lem7209750 A R h1)). Qed.
Lemma lem7209752 {A : Type'} (R : type1626) (h1 : term71 R) : term134 A R.
Proof. exact (@lem7209751 A R h1 (@lem7205625 A R)). Qed.
Lemma lem7209753 {A : Type'} (R : type1626) : term135 A R.
Proof. exact (fun h0 : term71 R => @lem7209752 A R h0). Qed.
Lemma lem7209758 {A : Type'} : term139 A.
Proof. exact (fun R : type1626 => @lem7209753 A R). Qed.
Lemma lem7209759 {A : Type'} : term138 A.
Proof. exact (EQ_MP (@lem7206380 A) (@lem7209758 A)). Qed.
