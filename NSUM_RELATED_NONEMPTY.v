Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_RELATED_NONEMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import ITERATE_RELATED_NONEMPTY_spec.
Require Import MONOIDAL_ADD_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import nsum_spec.
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
Lemma lem7036603 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7036604 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7036605 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7036604 t1) (@lem7036603 t1)). Qed.
Lemma lem7036606 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7036605 t1 t2). Qed.
Lemma lem7036607 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7036608 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7036607 t1 t2) (@lem7036606 t1 t2)). Qed.
Lemma lem7036609 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7036608 t1 t2 t3). Qed.
Lemma lem7036610 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7036611 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7036610 t1 t2 t3) (@lem7036609 t1 t2 t3)). Qed.
Lemma lem7036612 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7036611 t1 t2 t3)). Qed.
Lemma lem7036613 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (h1). Qed.
Lemma lem7036614 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (SYM (@lem7036613 _126417 h1)). Qed.
Lemma lem7036615 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (h1). Qed.
Lemma lem7036616 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (SYM (@lem7036615 _126417 h1)). Qed.
Lemma lem7036617 {_126417 : Type'} : ((@nsum _126417) = (@iterate nat _126417 Nat.add)) = ((@iterate nat _126417 Nat.add) = (@nsum _126417)).
Proof. exact (prop_ext (fun h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add) => @lem7036614 _126417 h1) (fun h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417) => @lem7036616 _126417 h1)). Qed.
Lemma lem7036619 {A B : Type'} (op : type1400 B) : term7 A B op.
Proof. exact (@lem5811935 A B op). Qed.
Lemma lem7036620 {A B : Type'} (op : type1400 B) : (term7 A B op) = (term8 A B op).
Proof. exact (eq_refl (term7 A B op)). Qed.
Lemma lem7036623 {A B : Type'} (op : type1400 B) : term8 A B op.
Proof. exact (EQ_MP (@lem7036620 A B op) (@lem7036619 A B op)). Qed.
Lemma lem7036624 {A : Type'} (op : type1606) : term9 A op.
Proof. exact (@lem7036623 A nat op). Qed.
Lemma lem7036625 {A : Type'} : term10 A.
Proof. exact (@lem7036624 A Nat.add). Qed.
Lemma lem7036626 {A : Type'} : term11 A.
Proof. exact (@lem7036625 A (@lem6924403)). Qed.
Lemma lem7036627 {A : Type'} (R : type1605) : term12 A R.
Proof. exact (@lem7036626 A R). Qed.
Lemma lem7036628 {A : Type'} (R : type1605) : (term12 A R) = (term13 A R).
Proof. exact (eq_refl (term12 A R)). Qed.
Lemma lem7036629 {A : Type'} (R : type1605) : term13 A R.
Proof. exact (EQ_MP (@lem7036628 A R) (@lem7036627 A R)). Qed.
Lemma lem7036630 {A : Type'} (P : Prop) : term14 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7036631 {A : Type'} (P : Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem7036632 {A : Type'} (P : Prop) : term15 A P.
Proof. exact (EQ_MP (@lem7036631 A P) (@lem7036630 A P)). Qed.
Lemma lem7036633 {A : Type'} (P : Prop) (Q : A -> Prop) : term16 A P Q.
Proof. exact (@lem7036632 A P Q). Qed.
Lemma lem7036634 {A : Type'} (P : Prop) (Q : A -> Prop) : (term16 A P Q) = ((term17 A P Q) = (term18 A P Q)).
Proof. exact (eq_refl (term16 A P Q)). Qed.
Lemma lem7036673 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7036674 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term21 A R f s g) = (term22 A R f s g).
Proof. exact (@lem7036673 (term23 R) (term24 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7036714 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7036715 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term26 R m m' n n') = (term27 R m m' n n').
Proof. exact (@lem7036714 (R m n) (R m' n') (term28 R m m' n n')). Qed.
Lemma lem7036720 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term29 R m m' n) = (term30 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7036715 R m m' n n')). Qed.
Lemma lem7036721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036722 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term31 R m m' n) = (term32 R m m' n).
Proof. exact (MK_COMB (@lem7036721) (@lem7036720 R m m' n)). Qed.
Lemma lem7036724 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7036634 A P Q) (@lem7036633 A P Q)). Qed.
Lemma lem7036725 (P : Prop) (Q : nat -> Prop) : (term33 P Q) = (term34 P Q).
Proof. exact (@lem7036724 nat P Q). Qed.
Lemma lem7036726 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term35 R m m' n) = (term36 R m m' n).
Proof. exact (@lem7036725 (R m n) (term37 R m m' n)). Qed.
Lemma lem7036727 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term38 R m m' n n') = (term39 R m m' n n').
Proof. exact (eq_refl (term38 R m m' n n')). Qed.
Lemma lem7036728 (R : type1605) (m : nat) (n : nat) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7036729 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term41 R m m' n n') = (term27 R m m' n n').
Proof. exact (MK_COMB (@lem7036728 R m n) (@lem7036727 R m m' n n')). Qed.
Lemma lem7036730 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term42 R m m' n) = (term30 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7036729 R m m' n n')). Qed.
Lemma lem7036731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036732 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term35 R m m' n) = (term32 R m m' n).
Proof. exact (MK_COMB (@lem7036731) (@lem7036730 R m m' n)). Qed.
Lemma lem7036733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7036734 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term43 R m m' n) = (term44 R m m' n).
Proof. exact (MK_COMB (@lem7036733) (@lem7036732 R m m' n)). Qed.
Lemma lem7036735 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term38 R m m' n n') = (term39 R m m' n n').
Proof. exact (eq_refl (term38 R m m' n n')). Qed.
Lemma lem7036736 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term45 R m m' n) = (term37 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7036735 R m m' n n')). Qed.
Lemma lem7036737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036738 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term46 R m m' n) = (term47 R m m' n).
Proof. exact (MK_COMB (@lem7036737) (@lem7036736 R m m' n)). Qed.
Lemma lem7036739 (R : type1605) (m : nat) (n : nat) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7036740 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term36 R m m' n) = (term48 R m m' n).
Proof. exact (MK_COMB (@lem7036739 R m n) (@lem7036738 R m m' n)). Qed.
Lemma lem7036741 (R : type1605) (m : nat) (m' : nat) (n : nat) : ((term35 R m m' n) = (term36 R m m' n)) = ((term32 R m m' n) = (term48 R m m' n)).
Proof. exact (MK_COMB (@lem7036734 R m m' n) (@lem7036740 R m m' n)). Qed.
Lemma lem7036742 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term32 R m m' n) = (term48 R m m' n).
Proof. exact (EQ_MP (@lem7036741 R m m' n) (@lem7036726 R m m' n)). Qed.
Lemma lem7036771 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term31 R m m' n) = (term48 R m m' n).
Proof. exact (TRANS (@lem7036722 R m m' n) (@lem7036742 R m m' n)). Qed.
Lemma lem7036772 (R : type1605) (m : nat) (n : nat) : (term49 R m n) = (term50 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7036771 R m m' n)). Qed.
Lemma lem7036773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036774 (R : type1605) (m : nat) (n : nat) : (term51 R m n) = (term52 R m n).
Proof. exact (MK_COMB (@lem7036773) (@lem7036772 R m n)). Qed.
Lemma lem7036776 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7036634 A P Q) (@lem7036633 A P Q)). Qed.
Lemma lem7036777 (P : Prop) (Q : nat -> Prop) : (term33 P Q) = (term34 P Q).
Proof. exact (@lem7036776 nat P Q). Qed.
Lemma lem7036778 (R : type1605) (m : nat) (n : nat) : (term53 R m n) = (term54 R m n).
Proof. exact (@lem7036777 (R m n) (term55 R m n)). Qed.
Lemma lem7036779 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term56 R m n m') = (term47 R m m' n).
Proof. exact (eq_refl (term56 R m n m')). Qed.
Lemma lem7036780 (R : type1605) (m : nat) (n : nat) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7036781 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term57 R m n m') = (term48 R m m' n).
Proof. exact (MK_COMB (@lem7036780 R m n) (@lem7036779 R m m' n)). Qed.
Lemma lem7036782 (R : type1605) (m : nat) (n : nat) : (term58 R m n) = (term50 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7036781 R m m' n)). Qed.
Lemma lem7036783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036784 (R : type1605) (m : nat) (n : nat) : (term53 R m n) = (term52 R m n).
Proof. exact (MK_COMB (@lem7036783) (@lem7036782 R m n)). Qed.
Lemma lem7036785 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7036786 (R : type1605) (m : nat) (n : nat) : (term59 R m n) = (term60 R m n).
Proof. exact (MK_COMB (@lem7036785) (@lem7036784 R m n)). Qed.
Lemma lem7036787 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term56 R m n m') = (term47 R m m' n).
Proof. exact (eq_refl (term56 R m n m')). Qed.
Lemma lem7036788 (R : type1605) (m : nat) (n : nat) : (term61 R m n) = (term55 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7036787 R m m' n)). Qed.
Lemma lem7036789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036790 (R : type1605) (m : nat) (n : nat) : (term62 R m n) = (term63 R m n).
Proof. exact (MK_COMB (@lem7036789) (@lem7036788 R m n)). Qed.
Lemma lem7036791 (R : type1605) (m : nat) (n : nat) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7036792 (R : type1605) (m : nat) (n : nat) : (term54 R m n) = (term64 R m n).
Proof. exact (MK_COMB (@lem7036791 R m n) (@lem7036790 R m n)). Qed.
Lemma lem7036793 (R : type1605) (m : nat) (n : nat) : ((term53 R m n) = (term54 R m n)) = ((term52 R m n) = (term64 R m n)).
Proof. exact (MK_COMB (@lem7036786 R m n) (@lem7036792 R m n)). Qed.
Lemma lem7036794 (R : type1605) (m : nat) (n : nat) : (term52 R m n) = (term64 R m n).
Proof. exact (EQ_MP (@lem7036793 R m n) (@lem7036778 R m n)). Qed.
Lemma lem7036827 (R : type1605) (m : nat) (n : nat) : (term51 R m n) = (term64 R m n).
Proof. exact (TRANS (@lem7036774 R m n) (@lem7036794 R m n)). Qed.
Lemma lem7036828 (R : type1605) (m : nat) : (term65 R m) = (term66 R m).
Proof. exact (fun_ext (fun n : nat => @lem7036827 R m n)). Qed.
Lemma lem7036829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036830 (R : type1605) (m : nat) : (term67 R m) = (term68 R m).
Proof. exact (MK_COMB (@lem7036829) (@lem7036828 R m)). Qed.
Lemma lem7036855 (R : type1605) : (term69 R) = (term70 R).
Proof. exact (fun_ext (fun m : nat => @lem7036830 R m)). Qed.
Lemma lem7036856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7036857 (R : type1605) : (term23 R) = (term71 R).
Proof. exact (MK_COMB (@lem7036856) (@lem7036855 R)). Qed.
Lemma lem7036862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7036863 (R : type1605) : (term72 R) = (term73 R).
Proof. exact (MK_COMB (@lem7036862) (@lem7036857 R)). Qed.
Lemma lem7036865 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7036866 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term74 A R f s g) = (term75 A R f s g).
Proof. exact (@lem7036865 (@FINITE A s) (term76 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7036870 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7036871 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term77 A R f s g) = (term78 A R f s g).
Proof. exact (@lem7036870 (term79 A s) (term80 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7036904 {A : Type'} (s : A -> Prop) : (term81 A s) = (term81 A s).
Proof. exact (eq_refl (term81 A s)). Qed.
Lemma lem7036905 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term75 A R f s g) = (term82 A R f s g).
Proof. exact (MK_COMB (@lem7036904 A s) (@lem7036871 A R f s g)). Qed.
Lemma lem7036908 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term74 A R f s g) = (term82 A R f s g).
Proof. exact (TRANS (@lem7036866 A R f s g) (@lem7036905 A R f s g)). Qed.
Lemma lem7036909 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term22 A R f s g) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7036863 R) (@lem7036908 A R f s g)). Qed.
Lemma lem7036912 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term21 A R f s g) = (term83 A R f s g).
Proof. exact (TRANS (@lem7036674 A R f s g) (@lem7036909 A R f s g)). Qed.
Lemma lem7036913 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term84 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7036912 A R f s g)). Qed.
Lemma lem7036914 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7036915 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term86 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7036914 A) (@lem7036913 A R f g)). Qed.
Lemma lem7036917 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7036634 A P Q) (@lem7036633 A P Q)). Qed.
Lemma lem7036918 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem7036917 (A -> Prop) P Q). Qed.
Lemma lem7036919 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term90 A R f g) = (term91 A R f g).
Proof. exact (@lem7036918 A (term71 R) (term92 A R f g)). Qed.
Lemma lem7036920 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term93 A R f g s) = (term82 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7036921 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7036922 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term94 A R f g s) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7036921 R) (@lem7036920 A R f s g)). Qed.
Lemma lem7036923 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term95 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7036922 A R f s g)). Qed.
Lemma lem7036924 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7036925 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term90 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7036924 A) (@lem7036923 A R f g)). Qed.
Lemma lem7036926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7036927 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term96 A R f g) = (term97 A R f g).
Proof. exact (MK_COMB (@lem7036926) (@lem7036925 A R f g)). Qed.
Lemma lem7036928 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term93 A R f g s) = (term82 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7036929 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term98 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7036928 A R f s g)). Qed.
Lemma lem7036930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7036931 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term99 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7036930 A) (@lem7036929 A R f g)). Qed.
Lemma lem7036932 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7036933 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term91 A R f g) = (term101 A R f g).
Proof. exact (MK_COMB (@lem7036932 R) (@lem7036931 A R f g)). Qed.
Lemma lem7036934 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : ((term90 A R f g) = (term91 A R f g)) = ((term87 A R f g) = (term101 A R f g)).
Proof. exact (MK_COMB (@lem7036927 A R f g) (@lem7036933 A R f g)). Qed.
Lemma lem7036935 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term87 A R f g) = (term101 A R f g).
Proof. exact (EQ_MP (@lem7036934 A R f g) (@lem7036919 A R f g)). Qed.
Lemma lem7037056 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term86 A R f g) = (term101 A R f g).
Proof. exact (TRANS (@lem7036915 A R f g) (@lem7036935 A R f g)). Qed.
Lemma lem7037057 {A : Type'} (R : type1605) (f : A -> nat) : (term102 A R f) = (term103 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7037056 A R f g)). Qed.
Lemma lem7037058 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037059 {A : Type'} (R : type1605) (f : A -> nat) : (term104 A R f) = (term105 A R f).
Proof. exact (MK_COMB (@lem7037058 A) (@lem7037057 A R f)). Qed.
Lemma lem7037061 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7036634 A P Q) (@lem7036633 A P Q)). Qed.
Lemma lem7037062 {A : Type'} (P : Prop) (Q : type704 A) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem7037061 (A -> nat) P Q). Qed.
Lemma lem7037063 {A : Type'} (R : type1605) (f : A -> nat) : (term108 A R f) = (term109 A R f).
Proof. exact (@lem7037062 A (term71 R) (term110 A R f)). Qed.
Lemma lem7037064 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term111 A R f g) = (term100 A R f g).
Proof. exact (eq_refl (term111 A R f g)). Qed.
Lemma lem7037065 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7037066 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term112 A R f g) = (term101 A R f g).
Proof. exact (MK_COMB (@lem7037065 R) (@lem7037064 A R f g)). Qed.
Lemma lem7037067 {A : Type'} (R : type1605) (f : A -> nat) : (term113 A R f) = (term103 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7037066 A R f g)). Qed.
Lemma lem7037068 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037069 {A : Type'} (R : type1605) (f : A -> nat) : (term108 A R f) = (term105 A R f).
Proof. exact (MK_COMB (@lem7037068 A) (@lem7037067 A R f)). Qed.
Lemma lem7037070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7037071 {A : Type'} (R : type1605) (f : A -> nat) : (term114 A R f) = (term115 A R f).
Proof. exact (MK_COMB (@lem7037070) (@lem7037069 A R f)). Qed.
Lemma lem7037072 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term111 A R f g) = (term100 A R f g).
Proof. exact (eq_refl (term111 A R f g)). Qed.
Lemma lem7037073 {A : Type'} (R : type1605) (f : A -> nat) : (term116 A R f) = (term110 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7037072 A R f g)). Qed.
Lemma lem7037074 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037075 {A : Type'} (R : type1605) (f : A -> nat) : (term117 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7037074 A) (@lem7037073 A R f)). Qed.
Lemma lem7037076 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7037077 {A : Type'} (R : type1605) (f : A -> nat) : (term109 A R f) = (term119 A R f).
Proof. exact (MK_COMB (@lem7037076 R) (@lem7037075 A R f)). Qed.
Lemma lem7037078 {A : Type'} (R : type1605) (f : A -> nat) : ((term108 A R f) = (term109 A R f)) = ((term105 A R f) = (term119 A R f)).
Proof. exact (MK_COMB (@lem7037071 A R f) (@lem7037077 A R f)). Qed.
Lemma lem7037079 {A : Type'} (R : type1605) (f : A -> nat) : (term105 A R f) = (term119 A R f).
Proof. exact (EQ_MP (@lem7037078 A R f) (@lem7037063 A R f)). Qed.
Lemma lem7037204 {A : Type'} (R : type1605) (f : A -> nat) : (term104 A R f) = (term119 A R f).
Proof. exact (TRANS (@lem7037059 A R f) (@lem7037079 A R f)). Qed.
Lemma lem7037205 {A : Type'} (R : type1605) : (term120 A R) = (term121 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7037204 A R f)). Qed.
Lemma lem7037206 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037207 {A : Type'} (R : type1605) : (term122 A R) = (term123 A R).
Proof. exact (MK_COMB (@lem7037206 A) (@lem7037205 A R)). Qed.
Lemma lem7037209 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7036634 A P Q) (@lem7036633 A P Q)). Qed.
Lemma lem7037210 {A : Type'} (P : Prop) (Q : type704 A) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem7037209 (A -> nat) P Q). Qed.
Lemma lem7037211 {A : Type'} (R : type1605) : (term124 A R) = (term125 A R).
Proof. exact (@lem7037210 A (term71 R) (term126 A R)). Qed.
Lemma lem7037212 {A : Type'} (R : type1605) (f : A -> nat) : (term127 A R f) = (term118 A R f).
Proof. exact (eq_refl (term127 A R f)). Qed.
Lemma lem7037213 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7037214 {A : Type'} (R : type1605) (f : A -> nat) : (term128 A R f) = (term119 A R f).
Proof. exact (MK_COMB (@lem7037213 R) (@lem7037212 A R f)). Qed.
Lemma lem7037215 {A : Type'} (R : type1605) : (term129 A R) = (term121 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7037214 A R f)). Qed.
Lemma lem7037216 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037217 {A : Type'} (R : type1605) : (term124 A R) = (term123 A R).
Proof. exact (MK_COMB (@lem7037216 A) (@lem7037215 A R)). Qed.
Lemma lem7037218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7037219 {A : Type'} (R : type1605) : (term130 A R) = (term131 A R).
Proof. exact (MK_COMB (@lem7037218) (@lem7037217 A R)). Qed.
Lemma lem7037220 {A : Type'} (R : type1605) (f : A -> nat) : (term127 A R f) = (term118 A R f).
Proof. exact (eq_refl (term127 A R f)). Qed.
Lemma lem7037221 {A : Type'} (R : type1605) : (term132 A R) = (term126 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7037220 A R f)). Qed.
Lemma lem7037222 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037223 {A : Type'} (R : type1605) : (term133 A R) = (term134 A R).
Proof. exact (MK_COMB (@lem7037222 A) (@lem7037221 A R)). Qed.
Lemma lem7037224 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7037225 {A : Type'} (R : type1605) : (term125 A R) = (term135 A R).
Proof. exact (MK_COMB (@lem7037224 R) (@lem7037223 A R)). Qed.
Lemma lem7037226 {A : Type'} (R : type1605) : ((term124 A R) = (term125 A R)) = ((term123 A R) = (term135 A R)).
Proof. exact (MK_COMB (@lem7037219 A R) (@lem7037225 A R)). Qed.
Lemma lem7037227 {A : Type'} (R : type1605) : (term123 A R) = (term135 A R).
Proof. exact (EQ_MP (@lem7037226 A R) (@lem7037211 A R)). Qed.
Lemma lem7037356 {A : Type'} (R : type1605) : (term122 A R) = (term135 A R).
Proof. exact (TRANS (@lem7037207 A R) (@lem7037227 A R)). Qed.
Lemma lem7037357 {A : Type'} : (term136 A) = (term137 A).
Proof. exact (fun_ext (fun R : type1605 => @lem7037356 A R)). Qed.
Lemma lem7037358 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem7037359 {A : Type'} : (term138 A) = (term139 A).
Proof. exact (MK_COMB (@lem7037358) (@lem7037357 A)). Qed.
Lemma lem7037384 {A : Type'} : (term139 A) = (term138 A).
Proof. exact (SYM (@lem7037359 A)). Qed.
Lemma lem7037385 (R : type1605) (h1 : term71 R) : term71 R.
Proof. exact (h1). Qed.
Lemma lem7037445 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem7036617 _126417) (@lem6920372 _126417)). Qed.
Lemma lem7037446 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem7037445 A). Qed.
Lemma lem7037447 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7037448 {A : Type'} (s : A -> Prop) : (@iterate nat A Nat.add s) = (@nsum A s).
Proof. exact (MK_COMB (@lem7037446 A) (@lem7037447 A s)). Qed.
Lemma lem7037449 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7037450 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@iterate nat A Nat.add s f) = (@nsum A s f).
Proof. exact (MK_COMB (@lem7037448 A s) (@lem7037449 A f)). Qed.
Lemma lem7037451 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7037452 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term140 A R s f) = (term141 A R s f).
Proof. exact (MK_COMB (@lem7037451 R) (@lem7037450 A s f)). Qed.
Lemma lem7037454 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem7036617 _126417) (@lem6920372 _126417)). Qed.
Lemma lem7037455 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem7037454 A). Qed.
Lemma lem7037456 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7037457 {A : Type'} (s : A -> Prop) : (@iterate nat A Nat.add s) = (@nsum A s).
Proof. exact (MK_COMB (@lem7037455 A) (@lem7037456 A s)). Qed.
Lemma lem7037458 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7037459 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@iterate nat A Nat.add s g) = (@nsum A s g).
Proof. exact (MK_COMB (@lem7037457 A s) (@lem7037458 A g)). Qed.
Lemma lem7037460 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term142 A R f s g) = (term25 A R f s g).
Proof. exact (MK_COMB (@lem7037452 A R s f) (@lem7037459 A s g)). Qed.
Lemma lem7037461 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term143 A s R f g) = (term143 A s R f g).
Proof. exact (eq_refl (term143 A s R f g)). Qed.
Lemma lem7037462 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term144 A R f s g) = (term74 A R f s g).
Proof. exact (MK_COMB (@lem7037461 A s R f g) (@lem7037460 A R f s g)). Qed.
Lemma lem7037465 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term145 A R f g) = (term146 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7037462 A R f s g)). Qed.
Lemma lem7037466 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7037467 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term147 A R f g) = (term148 A R f g).
Proof. exact (MK_COMB (@lem7037466 A) (@lem7037465 A R f g)). Qed.
Lemma lem7037472 {A : Type'} (R : type1605) (f : A -> nat) : (term149 A R f) = (term150 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7037467 A R f g)). Qed.
Lemma lem7037473 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037474 {A : Type'} (R : type1605) (f : A -> nat) : (term151 A R f) = (term152 A R f).
Proof. exact (MK_COMB (@lem7037473 A) (@lem7037472 A R f)). Qed.
Lemma lem7037479 {A : Type'} (R : type1605) : (term153 A R) = (term154 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7037474 A R f)). Qed.
Lemma lem7037480 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037481 {A : Type'} (R : type1605) : (term155 A R) = (term156 A R).
Proof. exact (MK_COMB (@lem7037480 A) (@lem7037479 A R)). Qed.
Lemma lem7037486 (R : type1605) : (term157 R) = (term157 R).
Proof. exact (eq_refl (term157 R)). Qed.
Lemma lem7037487 {A : Type'} (R : type1605) : (term13 A R) = (term158 A R).
Proof. exact (MK_COMB (@lem7037486 R) (@lem7037481 A R)). Qed.
Lemma lem7037490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7037491 {A : Type'} (R : type1605) : (term159 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7037490) (@lem7037487 A R)). Qed.
Lemma lem7037518 {A : Type'} (R : type1605) : (term134 A R) = (term134 A R).
Proof. exact (eq_refl (term134 A R)). Qed.
Lemma lem7037519 {A : Type'} (R : type1605) : (term161 A R) = (term162 A R).
Proof. exact (MK_COMB (@lem7037491 A R) (@lem7037518 A R)). Qed.
Lemma lem7037522 {A : Type'} (R : type1605) : (term162 A R) = (term161 A R).
Proof. exact (SYM (@lem7037519 A R)). Qed.
Lemma lem7037524 (p : Prop) : p = (term163 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7037525 {A : Type'} (R : type1605) : (term162 A R) = (term164 A R).
Proof. exact (@lem7037524 (term162 A R)). Qed.
Lemma lem7037526 {A : Type'} (R : type1605) : (term164 A R) = (term162 A R).
Proof. exact (SYM (@lem7037525 A R)). Qed.
Lemma lem7037527 {A : Type'} (R : type1605) (h1 : term165 A R) : term165 A R.
Proof. exact (h1). Qed.
Lemma lem7037530 {A : Type'} (R : type1605) (h1 : term166 A R) : term166 A R.
Proof. exact (h1). Qed.
Lemma lem7037531 {A : Type'} (R : type1605) : term167 A R.
Proof. exact (fun h0 : term166 A R => @lem7037530 A R h0). Qed.
Lemma lem7037532 {A : Type'} (R : type1605) (h1 : term167 A R) : term167 A R.
Proof. exact (h1). Qed.
Lemma lem7037533 {A : Type'} (R : type1605) (h1 : term166 A R) : term166 A R.
Proof. exact (h1). Qed.
Lemma lem7037534 {A : Type'} (R : type1605) (h1 : term166 A R) (h2 : term167 A R) : term166 A R.
Proof. exact (@lem7037532 A R h2 (@lem7037533 A R h1)). Qed.
Lemma lem7037535 {A : Type'} (R : type1605) (h1 : term166 A R) : term168 A R.
Proof. exact (fun h0 : term167 A R => @lem7037534 A R h1 h0). Qed.
Lemma lem7037536 {A : Type'} (R : type1605) (h1 : term167 A R) : term167 A R.
Proof. exact (h1). Qed.
Lemma lem7037537 {A : Type'} (R : type1605) (h1 : term166 A R) (h2 : term167 A R) : term166 A R.
Proof. exact (@lem7037535 A R h1 (@lem7037536 A R h2)). Qed.
Lemma lem7037538 {A : Type'} (R : type1605) (h1 : term167 A R) : term167 A R.
Proof. exact (fun h0 : term166 A R => @lem7037537 A R h0 h1). Qed.
Lemma lem7037539 {A : Type'} (R : type1605) : term169 A R.
Proof. exact (fun h0 : term167 A R => @lem7037538 A R h0). Qed.
Lemma lem7037542 {A : Type'} (R : type1605) : term167 A R.
Proof. exact (@lem7037539 A R (@lem7037531 A R)). Qed.
Lemma lem7037543 {A : Type'} (R : type1605) : term167 A R.
Proof. exact (@lem7037542 A R). Qed.
Lemma lem7037571 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7037572 {A : Type'} (R : type1605) : (term164 A R) = (term170 A R).
Proof. exact (@lem7037571 (term165 A R)). Qed.
Lemma lem7037574 (t : Prop) : (term171 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7037575 {A : Type'} (R : type1605) : (term170 A R) = (term162 A R).
Proof. exact (@lem7037574 (term162 A R)). Qed.
Lemma lem7037578 {A : Type'} (R : type1605) : (term164 A R) = (term162 A R).
Proof. exact (TRANS (@lem7037572 A R) (@lem7037575 A R)). Qed.
Lemma lem7037649 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (eq_refl (term73 R)). Qed.
Lemma lem7037650 {A : Type'} (R : type1605) : (term166 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7037649 R) (@lem7037578 A R)). Qed.
Lemma lem7037653 {A : Type'} : (term173 A) = (term174 A).
Proof. exact (fun_ext (fun R : type1605 => @lem7037650 A R)). Qed.
Lemma lem7037654 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem7037663 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (MK_COMB (@lem7037654) (@lem7037653 A)). Qed.
Lemma lem7037664 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7037669 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term177 A s R f g x) = (term177 A s R f g x).
Proof. exact (eq_refl (term177 A s R f g x)). Qed.
Lemma lem7037670 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term178 A s R f g) = (term178 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7037669 A s R f g x)). Qed.
Lemma lem7037671 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7037672 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7037671 A) (@lem7037670 A s R f g)). Qed.
Lemma lem7037673 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7037674 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term179 A s R f g) = (term179 A s R f g).
Proof. exact (MK_COMB (@lem7037673) (@lem7037672 A s R f g)). Qed.
Lemma lem7037675 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term180 A R f s g) = (term180 A R f s g).
Proof. exact (MK_COMB (@lem7037674 A s R f g) (@lem7037664 A R f s g)). Qed.
Lemma lem7037680 {A : Type'} (s : A -> Prop) : (term181 A s) = (term181 A s).
Proof. exact (eq_refl (term181 A s)). Qed.
Lemma lem7037681 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term78 A R f s g) = (term78 A R f s g).
Proof. exact (MK_COMB (@lem7037680 A s) (@lem7037675 A R f s g)). Qed.
Lemma lem7037684 {A : Type'} (s : A -> Prop) : (term81 A s) = (term81 A s).
Proof. exact (eq_refl (term81 A s)). Qed.
Lemma lem7037685 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term82 A R f s g) = (term82 A R f s g).
Proof. exact (MK_COMB (@lem7037684 A s) (@lem7037681 A R f s g)). Qed.
Lemma lem7037686 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term92 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7037685 A R f s g)). Qed.
Lemma lem7037687 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7037688 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term100 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7037687 A) (@lem7037686 A R f g)). Qed.
Lemma lem7037689 {A : Type'} (R : type1605) (f : A -> nat) : (term110 A R f) = (term110 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7037688 A R f g)). Qed.
Lemma lem7037690 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037691 {A : Type'} (R : type1605) (f : A -> nat) : (term118 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7037690 A) (@lem7037689 A R f)). Qed.
Lemma lem7037692 {A : Type'} (R : type1605) : (term126 A R) = (term126 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7037691 A R f)). Qed.
Lemma lem7037693 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037694 {A : Type'} (R : type1605) : (term134 A R) = (term134 A R).
Proof. exact (MK_COMB (@lem7037693 A) (@lem7037692 A R)). Qed.
Lemma lem7037695 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7037700 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term177 A s R f g x) = (term177 A s R f g x).
Proof. exact (eq_refl (term177 A s R f g x)). Qed.
Lemma lem7037701 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term178 A s R f g) = (term178 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7037700 A s R f g x)). Qed.
Lemma lem7037702 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7037703 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7037702 A) (@lem7037701 A s R f g)). Qed.
Lemma lem7037708 {A : Type'} (s : A -> Prop) : (term182 A s) = (term182 A s).
Proof. exact (eq_refl (term182 A s)). Qed.
Lemma lem7037709 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term76 A s R f g) = (term76 A s R f g).
Proof. exact (MK_COMB (@lem7037708 A s) (@lem7037703 A s R f g)). Qed.
Lemma lem7037712 {A : Type'} (s : A -> Prop) : (term183 A s) = (term183 A s).
Proof. exact (eq_refl (term183 A s)). Qed.
Lemma lem7037713 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term24 A s R f g) = (term24 A s R f g).
Proof. exact (MK_COMB (@lem7037712 A s) (@lem7037709 A s R f g)). Qed.
Lemma lem7037714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7037715 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term143 A s R f g) = (term143 A s R f g).
Proof. exact (MK_COMB (@lem7037714) (@lem7037713 A s R f g)). Qed.
Lemma lem7037716 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term74 A R f s g) = (term74 A R f s g).
Proof. exact (MK_COMB (@lem7037715 A s R f g) (@lem7037695 A R f s g)). Qed.
Lemma lem7037717 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term146 A R f g) = (term146 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7037716 A R f s g)). Qed.
Lemma lem7037718 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7037719 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term148 A R f g) = (term148 A R f g).
Proof. exact (MK_COMB (@lem7037718 A) (@lem7037717 A R f g)). Qed.
Lemma lem7037720 {A : Type'} (R : type1605) (f : A -> nat) : (term150 A R f) = (term150 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7037719 A R f g)). Qed.
Lemma lem7037721 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037722 {A : Type'} (R : type1605) (f : A -> nat) : (term152 A R f) = (term152 A R f).
Proof. exact (MK_COMB (@lem7037721 A) (@lem7037720 A R f)). Qed.
Lemma lem7037723 {A : Type'} (R : type1605) : (term154 A R) = (term154 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7037722 A R f)). Qed.
Lemma lem7037724 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7037725 {A : Type'} (R : type1605) : (term156 A R) = (term156 A R).
Proof. exact (MK_COMB (@lem7037724 A) (@lem7037723 A R)). Qed.
Lemma lem7037734 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term26 R x1 y1 x2 y2) = (term26 R x1 y1 x2 y2).
Proof. exact (eq_refl (term26 R x1 y1 x2 y2)). Qed.
Lemma lem7037735 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term29 R x1 y1 x2) = (term29 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : nat => @lem7037734 R x1 y1 x2 y2)). Qed.
Lemma lem7037736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037737 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term31 R x1 y1 x2) = (term31 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7037736) (@lem7037735 R x1 y1 x2)). Qed.
Lemma lem7037738 (R : type1605) (x1 : nat) (y1 : nat) : (term184 R x1 y1) = (term184 R x1 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem7037737 R x1 y1 x2)). Qed.
Lemma lem7037739 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037740 (R : type1605) (x1 : nat) (y1 : nat) : (term185 R x1 y1) = (term185 R x1 y1).
Proof. exact (MK_COMB (@lem7037739) (@lem7037738 R x1 y1)). Qed.
Lemma lem7037741 (R : type1605) (x1 : nat) : (term186 R x1) = (term186 R x1).
Proof. exact (fun_ext (fun y1 : nat => @lem7037740 R x1 y1)). Qed.
Lemma lem7037742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037743 (R : type1605) (x1 : nat) : (term187 R x1) = (term187 R x1).
Proof. exact (MK_COMB (@lem7037742) (@lem7037741 R x1)). Qed.
Lemma lem7037744 (R : type1605) : (term188 R) = (term188 R).
Proof. exact (fun_ext (fun x1 : nat => @lem7037743 R x1)). Qed.
Lemma lem7037745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037746 (R : type1605) : (term189 R) = (term189 R).
Proof. exact (MK_COMB (@lem7037745) (@lem7037744 R)). Qed.
Lemma lem7037747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7037748 (R : type1605) : (term157 R) = (term157 R).
Proof. exact (MK_COMB (@lem7037747) (@lem7037746 R)). Qed.
Lemma lem7037749 {A : Type'} (R : type1605) : (term158 A R) = (term158 A R).
Proof. exact (MK_COMB (@lem7037748 R) (@lem7037725 A R)). Qed.
Lemma lem7037750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7037751 {A : Type'} (R : type1605) : (term160 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7037750) (@lem7037749 A R)). Qed.
Lemma lem7037752 {A : Type'} (R : type1605) : (term162 A R) = (term162 A R).
Proof. exact (MK_COMB (@lem7037751 A R) (@lem7037694 A R)). Qed.
Lemma lem7037757 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term39 R m m' n n') = (term39 R m m' n n').
Proof. exact (eq_refl (term39 R m m' n n')). Qed.
Lemma lem7037758 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term37 R m m' n) = (term37 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7037757 R m m' n n')). Qed.
Lemma lem7037759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037760 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term47 R m m' n) = (term47 R m m' n).
Proof. exact (MK_COMB (@lem7037759) (@lem7037758 R m m' n)). Qed.
Lemma lem7037761 (R : type1605) (m : nat) (n : nat) : (term55 R m n) = (term55 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7037760 R m m' n)). Qed.
Lemma lem7037762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037763 (R : type1605) (m : nat) (n : nat) : (term63 R m n) = (term63 R m n).
Proof. exact (MK_COMB (@lem7037762) (@lem7037761 R m n)). Qed.
Lemma lem7037766 (R : type1605) (m : nat) (n : nat) : (term40 R m n) = (term40 R m n).
Proof. exact (eq_refl (term40 R m n)). Qed.
Lemma lem7037767 (R : type1605) (m : nat) (n : nat) : (term64 R m n) = (term64 R m n).
Proof. exact (MK_COMB (@lem7037766 R m n) (@lem7037763 R m n)). Qed.
Lemma lem7037768 (R : type1605) (m : nat) : (term66 R m) = (term66 R m).
Proof. exact (fun_ext (fun n : nat => @lem7037767 R m n)). Qed.
Lemma lem7037769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037770 (R : type1605) (m : nat) : (term68 R m) = (term68 R m).
Proof. exact (MK_COMB (@lem7037769) (@lem7037768 R m)). Qed.
Lemma lem7037771 (R : type1605) : (term70 R) = (term70 R).
Proof. exact (fun_ext (fun m : nat => @lem7037770 R m)). Qed.
Lemma lem7037772 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037773 (R : type1605) : (term71 R) = (term71 R).
Proof. exact (MK_COMB (@lem7037772) (@lem7037771 R)). Qed.
Lemma lem7037774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7037775 (R : type1605) : (term73 R) = (term73 R).
Proof. exact (MK_COMB (@lem7037774) (@lem7037773 R)). Qed.
Lemma lem7037776 {A : Type'} (R : type1605) : (term172 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7037775 R) (@lem7037752 A R)). Qed.
Lemma lem7037777 {A : Type'} : (term174 A) = (term174 A).
Proof. exact (fun_ext (fun R : type1605 => @lem7037776 A R)). Qed.
Lemma lem7037778 : (@all (nat -> nat -> Prop)) = (@all (nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> Prop))). Qed.
Lemma lem7037779 {A : Type'} : (term176 A) = (term176 A).
Proof. exact (MK_COMB (@lem7037778) (@lem7037777 A)). Qed.
Lemma lem7037914 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (TRANS (@lem7037663 A) (@lem7037779 A)). Qed.
Lemma lem7037915 {A : Type'} : (term176 A) = (term175 A).
Proof. exact (SYM (@lem7037914 A)). Qed.
Lemma lem7037916 (R : type1605) (h1 : term71 R) : term71 R.
Proof. exact (h1). Qed.
Lemma lem7037917 {A : Type'} (R : type1605) (h1 : term158 A R) : term158 A R.
Proof. exact (h1). Qed.
Lemma lem7037920 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term80 A s R f g.
Proof. exact (h1). Qed.
Lemma lem7037922 (p : Prop) : p = (term163 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7037923 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term190 A R f s g).
Proof. exact (@lem7037922 (term25 A R f s g)). Qed.
Lemma lem7037924 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term190 A R f s g) = (term25 A R f s g).
Proof. exact (SYM (@lem7037923 A R f s g)). Qed.
Lemma lem7037925 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term191 A R f s g) : term191 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7037933 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term39 R m m' n n') = (term192 R m m' n n').
Proof. exact (@lem17265 (R m' n') (term28 R m m' n n')). Qed.
Lemma lem7037934 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term37 R m m' n) = (term193 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7037933 R m m' n n')). Qed.
Lemma lem7037935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037936 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term47 R m m' n) = (term194 R m m' n).
Proof. exact (MK_COMB (@lem7037935) (@lem7037934 R m m' n)). Qed.
Lemma lem7037937 (R : type1605) (m : nat) (n : nat) : (term55 R m n) = (term195 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7037936 R m m' n)). Qed.
Lemma lem7037938 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037939 (R : type1605) (m : nat) (n : nat) : (term63 R m n) = (term196 R m n).
Proof. exact (MK_COMB (@lem7037938) (@lem7037937 R m n)). Qed.
Lemma lem7037941 (R : type1605) (m : nat) (n : nat) : (term197 R m n) = (term197 R m n).
Proof. exact (eq_refl (term197 R m n)). Qed.
Lemma lem7037942 (R : type1605) (m : nat) (n : nat) : (term198 R m n) = (term199 R m n).
Proof. exact (MK_COMB (@lem7037941 R m n) (@lem7037939 R m n)). Qed.
Lemma lem7037943 (R : type1605) (m : nat) (n : nat) : (term64 R m n) = (term198 R m n).
Proof. exact (@lem17265 (R m n) (term63 R m n)). Qed.
Lemma lem7037944 (R : type1605) (m : nat) (n : nat) : (term64 R m n) = (term199 R m n).
Proof. exact (TRANS (@lem7037943 R m n) (@lem7037942 R m n)). Qed.
Lemma lem7037945 (R : type1605) (m : nat) : (term66 R m) = (term200 R m).
Proof. exact (fun_ext (fun n : nat => @lem7037944 R m n)). Qed.
Lemma lem7037946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7037947 (R : type1605) (m : nat) : (term68 R m) = (term201 R m).
Proof. exact (MK_COMB (@lem7037946) (@lem7037945 R m)). Qed.
Lemma lem7037948 (R : type1605) : (term70 R) = (term202 R).
Proof. exact (fun_ext (fun m : nat => @lem7037947 R m)). Qed.
Lemma lem7037949 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7038058 (R : type1605) : (term71 R) = (term203 R).
Proof. exact (MK_COMB (@lem7037949) (@lem7037948 R)). Qed.
Lemma lem7038059 (R : type1605) (h1 : term71 R) : term203 R.
Proof. exact (EQ_MP (@lem7038058 R) (@lem7037916 R h1)). Qed.
Lemma lem7038070 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term204 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (@lem17362 (term206 x1 x2 R y1 y2) (term28 R x1 y1 x2 y2)). Qed.
Lemma lem7038071 (P : nat -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7038072 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term209 R x1 y1 x2) = (term210 R x1 y1 x2).
Proof. exact (@lem7038071 (term29 R x1 y1 x2)). Qed.
Lemma lem7038073 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term211 R x1 y1 x2 y2) = (term26 R x1 y1 x2 y2).
Proof. exact (eq_refl (term211 R x1 y1 x2 y2)). Qed.
Lemma lem7038074 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038075 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term212 R x1 y1 x2 y2) = (term204 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7038074) (@lem7038073 R x1 y1 x2 y2)). Qed.
Lemma lem7038076 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term212 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7038075 R x1 y1 x2 y2) (@lem7038070 R x1 y1 x2 y2)). Qed.
Lemma lem7038077 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term213 R x1 y1 x2) = (term214 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : nat => @lem7038076 R x1 y1 x2 y2)). Qed.
Lemma lem7038078 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038079 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term210 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7038078) (@lem7038077 R x1 y1 x2)). Qed.
Lemma lem7038080 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term209 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (TRANS (@lem7038072 R x1 y1 x2) (@lem7038079 R x1 y1 x2)). Qed.
Lemma lem7038081 (P : nat -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7038082 (R : type1605) (x1 : nat) (y1 : nat) : (term216 R x1 y1) = (term217 R x1 y1).
Proof. exact (@lem7038081 (term184 R x1 y1)). Qed.
Lemma lem7038083 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term218 R x1 y1 x2) = (term31 R x1 y1 x2).
Proof. exact (eq_refl (term218 R x1 y1 x2)). Qed.
Lemma lem7038084 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038085 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term219 R x1 y1 x2) = (term209 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7038084) (@lem7038083 R x1 y1 x2)). Qed.
Lemma lem7038086 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term219 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (TRANS (@lem7038085 R x1 y1 x2) (@lem7038080 R x1 y1 x2)). Qed.
Lemma lem7038087 (R : type1605) (x1 : nat) (y1 : nat) : (term220 R x1 y1) = (term221 R x1 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem7038086 R x1 y1 x2)). Qed.
Lemma lem7038088 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038089 (R : type1605) (x1 : nat) (y1 : nat) : (term217 R x1 y1) = (term222 R x1 y1).
Proof. exact (MK_COMB (@lem7038088) (@lem7038087 R x1 y1)). Qed.
Lemma lem7038090 (R : type1605) (x1 : nat) (y1 : nat) : (term216 R x1 y1) = (term222 R x1 y1).
Proof. exact (TRANS (@lem7038082 R x1 y1) (@lem7038089 R x1 y1)). Qed.
Lemma lem7038091 (P : nat -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7038092 (R : type1605) (x1 : nat) : (term223 R x1) = (term224 R x1).
Proof. exact (@lem7038091 (term186 R x1)). Qed.
Lemma lem7038093 (R : type1605) (x1 : nat) (y1 : nat) : (term225 R x1 y1) = (term185 R x1 y1).
Proof. exact (eq_refl (term225 R x1 y1)). Qed.
Lemma lem7038094 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038095 (R : type1605) (x1 : nat) (y1 : nat) : (term226 R x1 y1) = (term216 R x1 y1).
Proof. exact (MK_COMB (@lem7038094) (@lem7038093 R x1 y1)). Qed.
Lemma lem7038096 (R : type1605) (x1 : nat) (y1 : nat) : (term226 R x1 y1) = (term222 R x1 y1).
Proof. exact (TRANS (@lem7038095 R x1 y1) (@lem7038090 R x1 y1)). Qed.
Lemma lem7038097 (R : type1605) (x1 : nat) : (term227 R x1) = (term228 R x1).
Proof. exact (fun_ext (fun y1 : nat => @lem7038096 R x1 y1)). Qed.
Lemma lem7038098 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038099 (R : type1605) (x1 : nat) : (term224 R x1) = (term229 R x1).
Proof. exact (MK_COMB (@lem7038098) (@lem7038097 R x1)). Qed.
Lemma lem7038100 (R : type1605) (x1 : nat) : (term223 R x1) = (term229 R x1).
Proof. exact (TRANS (@lem7038092 R x1) (@lem7038099 R x1)). Qed.
Lemma lem7038101 (P : nat -> Prop) : (term207 P) = (term208 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7038102 (R : type1605) : (term230 R) = (term231 R).
Proof. exact (@lem7038101 (term188 R)). Qed.
Lemma lem7038103 (R : type1605) (x1 : nat) : (term232 R x1) = (term187 R x1).
Proof. exact (eq_refl (term232 R x1)). Qed.
Lemma lem7038104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038105 (R : type1605) (x1 : nat) : (term233 R x1) = (term223 R x1).
Proof. exact (MK_COMB (@lem7038104) (@lem7038103 R x1)). Qed.
Lemma lem7038106 (R : type1605) (x1 : nat) : (term233 R x1) = (term229 R x1).
Proof. exact (TRANS (@lem7038105 R x1) (@lem7038100 R x1)). Qed.
Lemma lem7038107 (R : type1605) : (term234 R) = (term235 R).
Proof. exact (fun_ext (fun x1 : nat => @lem7038106 R x1)). Qed.
Lemma lem7038108 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038109 (R : type1605) : (term231 R) = (term236 R).
Proof. exact (MK_COMB (@lem7038108) (@lem7038107 R)). Qed.
Lemma lem7038110 (R : type1605) : (term230 R) = (term236 R).
Proof. exact (TRANS (@lem7038102 R) (@lem7038109 R)). Qed.
Lemma lem7038114 {A : Type'} (s : A -> Prop) : (term237 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem7038121 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term238 A s R f g x) = (term239 A s R f g x).
Proof. exact (@lem17362 (@IN A x s) (term240 A R f g x)). Qed.
Lemma lem7038122 {A : Type'} (P : A -> Prop) : (term241 A P) = (term242 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7038123 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term243 A s R f g) = (term244 A s R f g).
Proof. exact (@lem7038122 A (term178 A s R f g)). Qed.
Lemma lem7038124 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term245 A s R f g x) = (term177 A s R f g x).
Proof. exact (eq_refl (term245 A s R f g x)). Qed.
Lemma lem7038125 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038126 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term246 A s R f g x) = (term238 A s R f g x).
Proof. exact (MK_COMB (@lem7038125) (@lem7038124 A s R f g x)). Qed.
Lemma lem7038127 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term246 A s R f g x) = (term239 A s R f g x).
Proof. exact (TRANS (@lem7038126 A s R f g x) (@lem7038121 A s R f g x)). Qed.
Lemma lem7038128 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term247 A s R f g) = (term248 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038127 A s R f g x)). Qed.
Lemma lem7038129 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038130 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term244 A s R f g) = (term249 A s R f g).
Proof. exact (MK_COMB (@lem7038129 A) (@lem7038128 A s R f g)). Qed.
Lemma lem7038131 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term243 A s R f g) = (term249 A s R f g).
Proof. exact (TRANS (@lem7038123 A s R f g) (@lem7038130 A s R f g)). Qed.
Lemma lem7038132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038133 {A : Type'} (s : A -> Prop) : (term250 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem7038132) (@lem7038114 A s)). Qed.
Lemma lem7038134 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term252 A s R f g) = (term253 A s R f g).
Proof. exact (MK_COMB (@lem7038133 A s) (@lem7038131 A s R f g)). Qed.
Lemma lem7038135 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term254 A s R f g) = (term252 A s R f g).
Proof. exact (@lem17045 (term79 A s) (term80 A s R f g)). Qed.
Lemma lem7038136 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term254 A s R f g) = (term253 A s R f g).
Proof. exact (TRANS (@lem7038135 A s R f g) (@lem7038134 A s R f g)). Qed.
Lemma lem7038138 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7038139 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term256 A s R f g) = (term257 A s R f g).
Proof. exact (MK_COMB (@lem7038138 A s) (@lem7038136 A s R f g)). Qed.
Lemma lem7038140 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term258 A s R f g) = (term256 A s R f g).
Proof. exact (@lem17045 (@FINITE A s) (term76 A s R f g)). Qed.
Lemma lem7038141 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term258 A s R f g) = (term257 A s R f g).
Proof. exact (TRANS (@lem7038140 A s R f g) (@lem7038139 A s R f g)). Qed.
Lemma lem7038142 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7038143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038144 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term259 A s R f g) = (term260 A s R f g).
Proof. exact (MK_COMB (@lem7038143) (@lem7038141 A s R f g)). Qed.
Lemma lem7038145 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term261 A R f s g) = (term262 A R f s g).
Proof. exact (MK_COMB (@lem7038144 A s R f g) (@lem7038142 A R f s g)). Qed.
Lemma lem7038146 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term74 A R f s g) = (term261 A R f s g).
Proof. exact (@lem17265 (term24 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7038147 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term74 A R f s g) = (term262 A R f s g).
Proof. exact (TRANS (@lem7038146 A R f s g) (@lem7038145 A R f s g)). Qed.
Lemma lem7038148 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term146 A R f g) = (term263 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7038147 A R f s g)). Qed.
Lemma lem7038149 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7038150 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term148 A R f g) = (term264 A R f g).
Proof. exact (MK_COMB (@lem7038149 A) (@lem7038148 A R f g)). Qed.
Lemma lem7038151 {A : Type'} (R : type1605) (f : A -> nat) : (term150 A R f) = (term265 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7038150 A R f g)). Qed.
Lemma lem7038152 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038153 {A : Type'} (R : type1605) (f : A -> nat) : (term152 A R f) = (term266 A R f).
Proof. exact (MK_COMB (@lem7038152 A) (@lem7038151 A R f)). Qed.
Lemma lem7038154 {A : Type'} (R : type1605) : (term154 A R) = (term267 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7038153 A R f)). Qed.
Lemma lem7038155 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038156 {A : Type'} (R : type1605) : (term156 A R) = (term268 A R).
Proof. exact (MK_COMB (@lem7038155 A) (@lem7038154 A R)). Qed.
Lemma lem7038157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038158 (R : type1605) : (term269 R) = (term270 R).
Proof. exact (MK_COMB (@lem7038157) (@lem7038110 R)). Qed.
Lemma lem7038159 {A : Type'} (R : type1605) : (term271 A R) = (term272 A R).
Proof. exact (MK_COMB (@lem7038158 R) (@lem7038156 A R)). Qed.
Lemma lem7038160 {A : Type'} (R : type1605) : (term158 A R) = (term271 A R).
Proof. exact (@lem17265 (term189 R) (term156 A R)). Qed.
Lemma lem7038161 {A : Type'} (R : type1605) : (term158 A R) = (term272 A R).
Proof. exact (TRANS (@lem7038160 A R) (@lem7038159 A R)). Qed.
Lemma lem7038328 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7038329 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (@lem7038328 A P Q). Qed.
Lemma lem7038330 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term275 A s R f g) = (term276 A s R f g).
Proof. exact (@lem7038329 A (s = (@EMPTY A)) (term248 A s R f g)). Qed.
Lemma lem7038331 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term277 A s R f g x) = (term239 A s R f g x).
Proof. exact (eq_refl (term277 A s R f g x)). Qed.
Lemma lem7038332 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term278 A s R f g) = (term248 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038331 A s R f g x)). Qed.
Lemma lem7038333 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038334 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term279 A s R f g) = (term249 A s R f g).
Proof. exact (MK_COMB (@lem7038333 A) (@lem7038332 A s R f g)). Qed.
Lemma lem7038335 {A : Type'} (s : A -> Prop) : (term251 A s) = (term251 A s).
Proof. exact (eq_refl (term251 A s)). Qed.
Lemma lem7038336 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term275 A s R f g) = (term253 A s R f g).
Proof. exact (MK_COMB (@lem7038335 A s) (@lem7038334 A s R f g)). Qed.
Lemma lem7038337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038338 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term280 A s R f g) = (term281 A s R f g).
Proof. exact (MK_COMB (@lem7038337) (@lem7038336 A s R f g)). Qed.
Lemma lem7038339 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term277 A s R f g x) = (term239 A s R f g x).
Proof. exact (eq_refl (term277 A s R f g x)). Qed.
Lemma lem7038340 {A : Type'} (s : A -> Prop) : (term251 A s) = (term251 A s).
Proof. exact (eq_refl (term251 A s)). Qed.
Lemma lem7038341 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term282 A s R f g x) = (term283 A s R f g x).
Proof. exact (MK_COMB (@lem7038340 A s) (@lem7038339 A s R f g x)). Qed.
Lemma lem7038342 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term284 A s R f g) = (term285 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038341 A s R f g x)). Qed.
Lemma lem7038343 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038344 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term276 A s R f g) = (term286 A s R f g).
Proof. exact (MK_COMB (@lem7038343 A) (@lem7038342 A s R f g)). Qed.
Lemma lem7038345 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : ((term275 A s R f g) = (term276 A s R f g)) = ((term253 A s R f g) = (term286 A s R f g)).
Proof. exact (MK_COMB (@lem7038338 A s R f g) (@lem7038344 A s R f g)). Qed.
Lemma lem7038346 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term253 A s R f g) = (term286 A s R f g).
Proof. exact (EQ_MP (@lem7038345 A s R f g) (@lem7038330 A s R f g)). Qed.
Lemma lem7038347 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7038348 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term257 A s R f g) = (term287 A s R f g).
Proof. exact (MK_COMB (@lem7038347 A s) (@lem7038346 A s R f g)). Qed.
Lemma lem7038350 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7038351 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (@lem7038350 A P Q). Qed.
Lemma lem7038352 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term288 A s R f g) = (term289 A s R f g).
Proof. exact (@lem7038351 A (term290 A s) (term285 A s R f g)). Qed.
Lemma lem7038353 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term291 A s R f g x) = (term283 A s R f g x).
Proof. exact (eq_refl (term291 A s R f g x)). Qed.
Lemma lem7038354 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term292 A s R f g) = (term285 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038353 A s R f g x)). Qed.
Lemma lem7038355 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038356 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term293 A s R f g) = (term286 A s R f g).
Proof. exact (MK_COMB (@lem7038355 A) (@lem7038354 A s R f g)). Qed.
Lemma lem7038357 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7038358 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term288 A s R f g) = (term287 A s R f g).
Proof. exact (MK_COMB (@lem7038357 A s) (@lem7038356 A s R f g)). Qed.
Lemma lem7038359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038360 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term294 A s R f g) = (term295 A s R f g).
Proof. exact (MK_COMB (@lem7038359) (@lem7038358 A s R f g)). Qed.
Lemma lem7038361 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term291 A s R f g x) = (term283 A s R f g x).
Proof. exact (eq_refl (term291 A s R f g x)). Qed.
Lemma lem7038362 {A : Type'} (s : A -> Prop) : (term255 A s) = (term255 A s).
Proof. exact (eq_refl (term255 A s)). Qed.
Lemma lem7038363 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term296 A s R f g x) = (term297 A s R f g x).
Proof. exact (MK_COMB (@lem7038362 A s) (@lem7038361 A s R f g x)). Qed.
Lemma lem7038364 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term298 A s R f g) = (term299 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038363 A s R f g x)). Qed.
Lemma lem7038365 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038366 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term289 A s R f g) = (term300 A s R f g).
Proof. exact (MK_COMB (@lem7038365 A) (@lem7038364 A s R f g)). Qed.
Lemma lem7038367 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : ((term288 A s R f g) = (term289 A s R f g)) = ((term287 A s R f g) = (term300 A s R f g)).
Proof. exact (MK_COMB (@lem7038360 A s R f g) (@lem7038366 A s R f g)). Qed.
Lemma lem7038368 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term287 A s R f g) = (term300 A s R f g).
Proof. exact (EQ_MP (@lem7038367 A s R f g) (@lem7038352 A s R f g)). Qed.
Lemma lem7038369 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term257 A s R f g) = (term300 A s R f g).
Proof. exact (TRANS (@lem7038348 A s R f g) (@lem7038368 A s R f g)). Qed.
Lemma lem7038370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038371 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term260 A s R f g) = (term301 A s R f g).
Proof. exact (MK_COMB (@lem7038370) (@lem7038369 A s R f g)). Qed.
Lemma lem7038372 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7038373 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term262 A R f s g) = (term302 A R f s g).
Proof. exact (MK_COMB (@lem7038371 A s R f g) (@lem7038372 A R f s g)). Qed.
Lemma lem7038375 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7038376 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (@lem7038375 A P Q). Qed.
Lemma lem7038377 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term305 A R f s g) = (term306 A R f s g).
Proof. exact (@lem7038376 A (term299 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7038378 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term307 A s R f g x) = (term297 A s R f g x).
Proof. exact (eq_refl (term307 A s R f g x)). Qed.
Lemma lem7038379 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term308 A s R f g) = (term299 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038378 A s R f g x)). Qed.
Lemma lem7038380 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038381 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term309 A s R f g) = (term300 A s R f g).
Proof. exact (MK_COMB (@lem7038380 A) (@lem7038379 A s R f g)). Qed.
Lemma lem7038382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038383 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term310 A s R f g) = (term301 A s R f g).
Proof. exact (MK_COMB (@lem7038382) (@lem7038381 A s R f g)). Qed.
Lemma lem7038384 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7038385 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term305 A R f s g) = (term302 A R f s g).
Proof. exact (MK_COMB (@lem7038383 A s R f g) (@lem7038384 A R f s g)). Qed.
Lemma lem7038386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038387 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term311 A R f s g) = (term312 A R f s g).
Proof. exact (MK_COMB (@lem7038386) (@lem7038385 A R f s g)). Qed.
Lemma lem7038388 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term307 A s R f g x) = (term297 A s R f g x).
Proof. exact (eq_refl (term307 A s R f g x)). Qed.
Lemma lem7038389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038390 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term313 A s R f g x) = (term314 A s R f g x).
Proof. exact (MK_COMB (@lem7038389) (@lem7038388 A s R f g x)). Qed.
Lemma lem7038391 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7038392 {A : Type'} (x : A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term315 A x R f s g) = (term316 A x R f s g).
Proof. exact (MK_COMB (@lem7038390 A s R f g x) (@lem7038391 A R f s g)). Qed.
Lemma lem7038393 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term317 A R f s g) = (term318 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7038392 A x R f s g)). Qed.
Lemma lem7038394 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038395 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term306 A R f s g) = (term319 A R f s g).
Proof. exact (MK_COMB (@lem7038394 A) (@lem7038393 A R f s g)). Qed.
Lemma lem7038396 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((term305 A R f s g) = (term306 A R f s g)) = ((term302 A R f s g) = (term319 A R f s g)).
Proof. exact (MK_COMB (@lem7038387 A R f s g) (@lem7038395 A R f s g)). Qed.
Lemma lem7038397 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term302 A R f s g) = (term319 A R f s g).
Proof. exact (EQ_MP (@lem7038396 A R f s g) (@lem7038377 A R f s g)). Qed.
Lemma lem7038398 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term262 A R f s g) = (term319 A R f s g).
Proof. exact (TRANS (@lem7038373 A R f s g) (@lem7038397 A R f s g)). Qed.
Lemma lem7038399 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term263 A R f g) = (term320 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7038398 A R f s g)). Qed.
Lemma lem7038400 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7038401 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term264 A R f g) = (term321 A R f g).
Proof. exact (MK_COMB (@lem7038400 A) (@lem7038399 A R f g)). Qed.
Lemma lem7038403 {A B : Type'} (P : type1413 A B) : (term322 A B P) = (term323 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7038404 {A : Type'} (P : type672 A) : (term324 A P) = (term325 A P).
Proof. exact (@lem7038403 (A -> Prop) A P). Qed.
Lemma lem7038405 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term326 A R f g) = (term327 A R f g).
Proof. exact (@lem7038404 A (term328 A R f g)). Qed.
Lemma lem7038406 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term329 A R f g s) = (term318 A R f s g).
Proof. exact (eq_refl (term329 A R f g s)). Qed.
Lemma lem7038407 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7038408 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term330 A R f g s x) = (term331 A R f s g x).
Proof. exact (MK_COMB (@lem7038406 A R f s g) (@lem7038407 A x)). Qed.
Lemma lem7038409 {A : Type'} (x : A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term331 A R f s g x) = (term316 A x R f s g).
Proof. exact (eq_refl (term331 A R f s g x)). Qed.
Lemma lem7038410 {A : Type'} (x : A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term330 A R f g s x) = (term316 A x R f s g).
Proof. exact (TRANS (@lem7038408 A R f s g x) (@lem7038409 A x R f s g)). Qed.
Lemma lem7038411 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term332 A R f g s) = (term318 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7038410 A x R f s g)). Qed.
Lemma lem7038412 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7038413 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term333 A R f g s) = (term319 A R f s g).
Proof. exact (MK_COMB (@lem7038412 A) (@lem7038411 A R f s g)). Qed.
Lemma lem7038414 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term334 A R f g) = (term320 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7038413 A R f s g)). Qed.
Lemma lem7038415 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7038416 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term326 A R f g) = (term321 A R f g).
Proof. exact (MK_COMB (@lem7038415 A) (@lem7038414 A R f g)). Qed.
Lemma lem7038417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038418 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term335 A R f g) = (term336 A R f g).
Proof. exact (MK_COMB (@lem7038417) (@lem7038416 A R f g)). Qed.
Lemma lem7038419 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term329 A R f g s) = (term318 A R f s g).
Proof. exact (eq_refl (term329 A R f g s)). Qed.
Lemma lem7038420 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7038421 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : type684 A) (s : A -> Prop) : (term337 A R f g x s) = (term338 A R f g x s).
Proof. exact (MK_COMB (@lem7038419 A R f s g) (@lem7038420 A x s)). Qed.
Lemma lem7038422 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term338 A R f g x s) = (term339 A x R f s g).
Proof. exact (eq_refl (term338 A R f g x s)). Qed.
Lemma lem7038423 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term337 A R f g x s) = (term339 A x R f s g).
Proof. exact (TRANS (@lem7038421 A R f g x s) (@lem7038422 A x R f s g)). Qed.
Lemma lem7038424 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term340 A R f g x) = (term341 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7038423 A x R f s g)). Qed.
Lemma lem7038425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7038426 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term342 A R f g x) = (term343 A x R f g).
Proof. exact (MK_COMB (@lem7038425 A) (@lem7038424 A x R f g)). Qed.
Lemma lem7038427 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term344 A R f g) = (term345 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7038426 A x R f g)). Qed.
Lemma lem7038428 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7038429 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term327 A R f g) = (term346 A R f g).
Proof. exact (MK_COMB (@lem7038428 A) (@lem7038427 A R f g)). Qed.
Lemma lem7038430 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : ((term326 A R f g) = (term327 A R f g)) = ((term321 A R f g) = (term346 A R f g)).
Proof. exact (MK_COMB (@lem7038418 A R f g) (@lem7038429 A R f g)). Qed.
Lemma lem7038431 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term321 A R f g) = (term346 A R f g).
Proof. exact (EQ_MP (@lem7038430 A R f g) (@lem7038405 A R f g)). Qed.
Lemma lem7038432 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term264 A R f g) = (term346 A R f g).
Proof. exact (TRANS (@lem7038401 A R f g) (@lem7038431 A R f g)). Qed.
Lemma lem7038433 {A : Type'} (R : type1605) (f : A -> nat) : (term265 A R f) = (term347 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7038432 A R f g)). Qed.
Lemma lem7038434 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038435 {A : Type'} (R : type1605) (f : A -> nat) : (term266 A R f) = (term348 A R f).
Proof. exact (MK_COMB (@lem7038434 A) (@lem7038433 A R f)). Qed.
Lemma lem7038437 {A B : Type'} (P : type1413 A B) : (term322 A B P) = (term323 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7038438 {A : Type'} (P : type690 A) : (term349 A P) = (term350 A P).
Proof. exact (@lem7038437 (A -> nat) (type684 A) P). Qed.
Lemma lem7038439 {A : Type'} (R : type1605) (f : A -> nat) : (term351 A R f) = (term352 A R f).
Proof. exact (@lem7038438 A (term353 A R f)). Qed.
Lemma lem7038440 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term354 A R f g) = (term345 A R f g).
Proof. exact (eq_refl (term354 A R f g)). Qed.
Lemma lem7038441 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7038442 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : type684 A) : (term355 A R f g x) = (term356 A R f g x).
Proof. exact (MK_COMB (@lem7038440 A R f g) (@lem7038441 A x)). Qed.
Lemma lem7038443 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term356 A R f g x) = (term343 A x R f g).
Proof. exact (eq_refl (term356 A R f g x)). Qed.
Lemma lem7038444 {A : Type'} (x : type684 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term355 A R f g x) = (term343 A x R f g).
Proof. exact (TRANS (@lem7038442 A R f g x) (@lem7038443 A x R f g)). Qed.
Lemma lem7038445 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term357 A R f g) = (term345 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7038444 A x R f g)). Qed.
Lemma lem7038446 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7038447 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term358 A R f g) = (term346 A R f g).
Proof. exact (MK_COMB (@lem7038446 A) (@lem7038445 A R f g)). Qed.
Lemma lem7038448 {A : Type'} (R : type1605) (f : A -> nat) : (term359 A R f) = (term347 A R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7038447 A R f g)). Qed.
Lemma lem7038449 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038450 {A : Type'} (R : type1605) (f : A -> nat) : (term351 A R f) = (term348 A R f).
Proof. exact (MK_COMB (@lem7038449 A) (@lem7038448 A R f)). Qed.
Lemma lem7038451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038452 {A : Type'} (R : type1605) (f : A -> nat) : (term360 A R f) = (term361 A R f).
Proof. exact (MK_COMB (@lem7038451) (@lem7038450 A R f)). Qed.
Lemma lem7038453 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) : (term354 A R f g) = (term345 A R f g).
Proof. exact (eq_refl (term354 A R f g)). Qed.
Lemma lem7038454 {A : Type'} (x : type694 A) (g : A -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7038455 {A : Type'} (R : type1605) (f : A -> nat) (x : type694 A) (g : A -> nat) : (term362 A R f x g) = (term363 A R f x g).
Proof. exact (MK_COMB (@lem7038453 A R f g) (@lem7038454 A x g)). Qed.
Lemma lem7038456 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term363 A R f x g) = (term364 A x R f g).
Proof. exact (eq_refl (term363 A R f x g)). Qed.
Lemma lem7038457 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term362 A R f x g) = (term364 A x R f g).
Proof. exact (TRANS (@lem7038455 A R f x g) (@lem7038456 A x R f g)). Qed.
Lemma lem7038458 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term365 A R f x) = (term366 A x R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7038457 A x R f g)). Qed.
Lemma lem7038459 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038460 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term367 A R f x) = (term368 A x R f).
Proof. exact (MK_COMB (@lem7038459 A) (@lem7038458 A x R f)). Qed.
Lemma lem7038461 {A : Type'} (R : type1605) (f : A -> nat) : (term369 A R f) = (term370 A R f).
Proof. exact (fun_ext (fun x : type694 A => @lem7038460 A x R f)). Qed.
Lemma lem7038462 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7038463 {A : Type'} (R : type1605) (f : A -> nat) : (term352 A R f) = (term371 A R f).
Proof. exact (MK_COMB (@lem7038462 A) (@lem7038461 A R f)). Qed.
Lemma lem7038464 {A : Type'} (R : type1605) (f : A -> nat) : ((term351 A R f) = (term352 A R f)) = ((term348 A R f) = (term371 A R f)).
Proof. exact (MK_COMB (@lem7038452 A R f) (@lem7038463 A R f)). Qed.
Lemma lem7038465 {A : Type'} (R : type1605) (f : A -> nat) : (term348 A R f) = (term371 A R f).
Proof. exact (EQ_MP (@lem7038464 A R f) (@lem7038439 A R f)). Qed.
Lemma lem7038466 {A : Type'} (R : type1605) (f : A -> nat) : (term266 A R f) = (term371 A R f).
Proof. exact (TRANS (@lem7038435 A R f) (@lem7038465 A R f)). Qed.
Lemma lem7038467 {A : Type'} (R : type1605) : (term267 A R) = (term372 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7038466 A R f)). Qed.
Lemma lem7038468 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038469 {A : Type'} (R : type1605) : (term268 A R) = (term373 A R).
Proof. exact (MK_COMB (@lem7038468 A) (@lem7038467 A R)). Qed.
Lemma lem7038471 {A B : Type'} (P : type1413 A B) : (term322 A B P) = (term323 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7038472 {A : Type'} (P : type691 A) : (term374 A P) = (term375 A P).
Proof. exact (@lem7038471 (A -> nat) (type694 A) P). Qed.
Lemma lem7038473 {A : Type'} (R : type1605) : (term376 A R) = (term377 A R).
Proof. exact (@lem7038472 A (term378 A R)). Qed.
Lemma lem7038474 {A : Type'} (R : type1605) (f : A -> nat) : (term379 A R f) = (term370 A R f).
Proof. exact (eq_refl (term379 A R f)). Qed.
Lemma lem7038475 {A : Type'} (x : type694 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7038476 {A : Type'} (R : type1605) (f : A -> nat) (x : type694 A) : (term380 A R f x) = (term381 A R f x).
Proof. exact (MK_COMB (@lem7038474 A R f) (@lem7038475 A x)). Qed.
Lemma lem7038477 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term381 A R f x) = (term368 A x R f).
Proof. exact (eq_refl (term381 A R f x)). Qed.
Lemma lem7038478 {A : Type'} (x : type694 A) (R : type1605) (f : A -> nat) : (term380 A R f x) = (term368 A x R f).
Proof. exact (TRANS (@lem7038476 A R f x) (@lem7038477 A x R f)). Qed.
Lemma lem7038479 {A : Type'} (R : type1605) (f : A -> nat) : (term382 A R f) = (term370 A R f).
Proof. exact (fun_ext (fun x : type694 A => @lem7038478 A x R f)). Qed.
Lemma lem7038480 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7038481 {A : Type'} (R : type1605) (f : A -> nat) : (term383 A R f) = (term371 A R f).
Proof. exact (MK_COMB (@lem7038480 A) (@lem7038479 A R f)). Qed.
Lemma lem7038482 {A : Type'} (R : type1605) : (term384 A R) = (term372 A R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7038481 A R f)). Qed.
Lemma lem7038483 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038484 {A : Type'} (R : type1605) : (term376 A R) = (term373 A R).
Proof. exact (MK_COMB (@lem7038483 A) (@lem7038482 A R)). Qed.
Lemma lem7038485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038486 {A : Type'} (R : type1605) : (term385 A R) = (term386 A R).
Proof. exact (MK_COMB (@lem7038485) (@lem7038484 A R)). Qed.
Lemma lem7038487 {A : Type'} (R : type1605) (f : A -> nat) : (term379 A R f) = (term370 A R f).
Proof. exact (eq_refl (term379 A R f)). Qed.
Lemma lem7038488 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7038489 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) : (term387 A R x f) = (term388 A R x f).
Proof. exact (MK_COMB (@lem7038487 A R f) (@lem7038488 A x f)). Qed.
Lemma lem7038490 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term388 A R x f) = (term389 A x R f).
Proof. exact (eq_refl (term388 A R x f)). Qed.
Lemma lem7038491 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term387 A R x f) = (term389 A x R f).
Proof. exact (TRANS (@lem7038489 A R x f) (@lem7038490 A x R f)). Qed.
Lemma lem7038492 {A : Type'} (x : type695 A) (R : type1605) : (term390 A R x) = (term391 A x R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7038491 A x R f)). Qed.
Lemma lem7038493 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7038494 {A : Type'} (x : type695 A) (R : type1605) : (term392 A R x) = (term393 A x R).
Proof. exact (MK_COMB (@lem7038493 A) (@lem7038492 A x R)). Qed.
Lemma lem7038495 {A : Type'} (R : type1605) : (term394 A R) = (term395 A R).
Proof. exact (fun_ext (fun x : type695 A => @lem7038494 A x R)). Qed.
Lemma lem7038496 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7038497 {A : Type'} (R : type1605) : (term377 A R) = (term396 A R).
Proof. exact (MK_COMB (@lem7038496 A) (@lem7038495 A R)). Qed.
Lemma lem7038498 {A : Type'} (R : type1605) : ((term376 A R) = (term377 A R)) = ((term373 A R) = (term396 A R)).
Proof. exact (MK_COMB (@lem7038486 A R) (@lem7038497 A R)). Qed.
Lemma lem7038499 {A : Type'} (R : type1605) : (term373 A R) = (term396 A R).
Proof. exact (EQ_MP (@lem7038498 A R) (@lem7038473 A R)). Qed.
Lemma lem7038500 {A : Type'} (R : type1605) : (term268 A R) = (term396 A R).
Proof. exact (TRANS (@lem7038469 A R) (@lem7038499 A R)). Qed.
Lemma lem7038501 (R : type1605) : (term270 R) = (term270 R).
Proof. exact (eq_refl (term270 R)). Qed.
Lemma lem7038502 {A : Type'} (R : type1605) : (term272 A R) = (term397 A R).
Proof. exact (MK_COMB (@lem7038501 R) (@lem7038500 A R)). Qed.
Lemma lem7038506 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7038507 (P : nat -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7038506 nat P Q). Qed.
Lemma lem7038508 {A : Type'} (R : type1605) : (term400 A R) = (term401 A R).
Proof. exact (@lem7038507 (term235 R) (term396 A R)). Qed.
Lemma lem7038509 (R : type1605) (x1 : nat) : (term402 R x1) = (term229 R x1).
Proof. exact (eq_refl (term402 R x1)). Qed.
Lemma lem7038510 (R : type1605) : (term403 R) = (term235 R).
Proof. exact (fun_ext (fun x1 : nat => @lem7038509 R x1)). Qed.
Lemma lem7038511 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038512 (R : type1605) : (term404 R) = (term236 R).
Proof. exact (MK_COMB (@lem7038511) (@lem7038510 R)). Qed.
Lemma lem7038513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038514 (R : type1605) : (term405 R) = (term270 R).
Proof. exact (MK_COMB (@lem7038513) (@lem7038512 R)). Qed.
Lemma lem7038515 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038516 {A : Type'} (R : type1605) : (term400 A R) = (term397 A R).
Proof. exact (MK_COMB (@lem7038514 R) (@lem7038515 A R)). Qed.
Lemma lem7038517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038518 {A : Type'} (R : type1605) : (term406 A R) = (term407 A R).
Proof. exact (MK_COMB (@lem7038517) (@lem7038516 A R)). Qed.
Lemma lem7038519 (R : type1605) (x1 : nat) : (term402 R x1) = (term229 R x1).
Proof. exact (eq_refl (term402 R x1)). Qed.
Lemma lem7038520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038521 (R : type1605) (x1 : nat) : (term408 R x1) = (term409 R x1).
Proof. exact (MK_COMB (@lem7038520) (@lem7038519 R x1)). Qed.
Lemma lem7038522 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038523 {A : Type'} (x1 : nat) (R : type1605) : (term410 A x1 R) = (term411 A x1 R).
Proof. exact (MK_COMB (@lem7038521 R x1) (@lem7038522 A R)). Qed.
Lemma lem7038524 {A : Type'} (R : type1605) : (term412 A R) = (term413 A R).
Proof. exact (fun_ext (fun x1 : nat => @lem7038523 A x1 R)). Qed.
Lemma lem7038525 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038526 {A : Type'} (R : type1605) : (term401 A R) = (term414 A R).
Proof. exact (MK_COMB (@lem7038525) (@lem7038524 A R)). Qed.
Lemma lem7038527 {A : Type'} (R : type1605) : ((term400 A R) = (term401 A R)) = ((term397 A R) = (term414 A R)).
Proof. exact (MK_COMB (@lem7038518 A R) (@lem7038526 A R)). Qed.
Lemma lem7038528 {A : Type'} (R : type1605) : (term397 A R) = (term414 A R).
Proof. exact (EQ_MP (@lem7038527 A R) (@lem7038508 A R)). Qed.
Lemma lem7038532 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7038533 (P : nat -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7038532 nat P Q). Qed.
Lemma lem7038534 {A : Type'} (x1 : nat) (R : type1605) : (term415 A x1 R) = (term416 A x1 R).
Proof. exact (@lem7038533 (term228 R x1) (term396 A R)). Qed.
Lemma lem7038535 (R : type1605) (x1 : nat) (y1 : nat) : (term417 R x1 y1) = (term222 R x1 y1).
Proof. exact (eq_refl (term417 R x1 y1)). Qed.
Lemma lem7038536 (R : type1605) (x1 : nat) : (term418 R x1) = (term228 R x1).
Proof. exact (fun_ext (fun y1 : nat => @lem7038535 R x1 y1)). Qed.
Lemma lem7038537 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038538 (R : type1605) (x1 : nat) : (term419 R x1) = (term229 R x1).
Proof. exact (MK_COMB (@lem7038537) (@lem7038536 R x1)). Qed.
Lemma lem7038539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038540 (R : type1605) (x1 : nat) : (term420 R x1) = (term409 R x1).
Proof. exact (MK_COMB (@lem7038539) (@lem7038538 R x1)). Qed.
Lemma lem7038541 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038542 {A : Type'} (x1 : nat) (R : type1605) : (term415 A x1 R) = (term411 A x1 R).
Proof. exact (MK_COMB (@lem7038540 R x1) (@lem7038541 A R)). Qed.
Lemma lem7038543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038544 {A : Type'} (x1 : nat) (R : type1605) : (term421 A x1 R) = (term422 A x1 R).
Proof. exact (MK_COMB (@lem7038543) (@lem7038542 A x1 R)). Qed.
Lemma lem7038545 (R : type1605) (x1 : nat) (y1 : nat) : (term417 R x1 y1) = (term222 R x1 y1).
Proof. exact (eq_refl (term417 R x1 y1)). Qed.
Lemma lem7038546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038547 (R : type1605) (x1 : nat) (y1 : nat) : (term423 R x1 y1) = (term424 R x1 y1).
Proof. exact (MK_COMB (@lem7038546) (@lem7038545 R x1 y1)). Qed.
Lemma lem7038548 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038549 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term425 A x1 y1 R) = (term426 A x1 y1 R).
Proof. exact (MK_COMB (@lem7038547 R x1 y1) (@lem7038548 A R)). Qed.
Lemma lem7038550 {A : Type'} (x1 : nat) (R : type1605) : (term427 A x1 R) = (term428 A x1 R).
Proof. exact (fun_ext (fun y1 : nat => @lem7038549 A x1 y1 R)). Qed.
Lemma lem7038551 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038552 {A : Type'} (x1 : nat) (R : type1605) : (term416 A x1 R) = (term429 A x1 R).
Proof. exact (MK_COMB (@lem7038551) (@lem7038550 A x1 R)). Qed.
Lemma lem7038553 {A : Type'} (x1 : nat) (R : type1605) : ((term415 A x1 R) = (term416 A x1 R)) = ((term411 A x1 R) = (term429 A x1 R)).
Proof. exact (MK_COMB (@lem7038544 A x1 R) (@lem7038552 A x1 R)). Qed.
Lemma lem7038554 {A : Type'} (x1 : nat) (R : type1605) : (term411 A x1 R) = (term429 A x1 R).
Proof. exact (EQ_MP (@lem7038553 A x1 R) (@lem7038534 A x1 R)). Qed.
Lemma lem7038558 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7038559 (P : nat -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7038558 nat P Q). Qed.
Lemma lem7038560 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term430 A x1 y1 R) = (term431 A x1 y1 R).
Proof. exact (@lem7038559 (term221 R x1 y1) (term396 A R)). Qed.
Lemma lem7038561 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term432 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (eq_refl (term432 R x1 y1 x2)). Qed.
Lemma lem7038562 (R : type1605) (x1 : nat) (y1 : nat) : (term433 R x1 y1) = (term221 R x1 y1).
Proof. exact (fun_ext (fun x2 : nat => @lem7038561 R x1 y1 x2)). Qed.
Lemma lem7038563 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038564 (R : type1605) (x1 : nat) (y1 : nat) : (term434 R x1 y1) = (term222 R x1 y1).
Proof. exact (MK_COMB (@lem7038563) (@lem7038562 R x1 y1)). Qed.
Lemma lem7038565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038566 (R : type1605) (x1 : nat) (y1 : nat) : (term435 R x1 y1) = (term424 R x1 y1).
Proof. exact (MK_COMB (@lem7038565) (@lem7038564 R x1 y1)). Qed.
Lemma lem7038567 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038568 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term430 A x1 y1 R) = (term426 A x1 y1 R).
Proof. exact (MK_COMB (@lem7038566 R x1 y1) (@lem7038567 A R)). Qed.
Lemma lem7038569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038570 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term436 A x1 y1 R) = (term437 A x1 y1 R).
Proof. exact (MK_COMB (@lem7038569) (@lem7038568 A x1 y1 R)). Qed.
Lemma lem7038571 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term432 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (eq_refl (term432 R x1 y1 x2)). Qed.
Lemma lem7038572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038573 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term438 R x1 y1 x2) = (term439 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7038572) (@lem7038571 R x1 y1 x2)). Qed.
Lemma lem7038574 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038575 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term440 A x1 y1 x2 R) = (term441 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7038573 R x1 y1 x2) (@lem7038574 A R)). Qed.
Lemma lem7038576 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term442 A x1 y1 R) = (term443 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : nat => @lem7038575 A x1 y1 x2 R)). Qed.
Lemma lem7038577 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038578 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term431 A x1 y1 R) = (term444 A x1 y1 R).
Proof. exact (MK_COMB (@lem7038577) (@lem7038576 A x1 y1 R)). Qed.
Lemma lem7038579 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : ((term430 A x1 y1 R) = (term431 A x1 y1 R)) = ((term426 A x1 y1 R) = (term444 A x1 y1 R)).
Proof. exact (MK_COMB (@lem7038570 A x1 y1 R) (@lem7038578 A x1 y1 R)). Qed.
Lemma lem7038580 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term426 A x1 y1 R) = (term444 A x1 y1 R).
Proof. exact (EQ_MP (@lem7038579 A x1 y1 R) (@lem7038560 A x1 y1 R)). Qed.
Lemma lem7038584 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7038585 (P : nat -> Prop) (Q : Prop) : (term398 P Q) = (term399 P Q).
Proof. exact (@lem7038584 nat P Q). Qed.
Lemma lem7038586 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term445 A x1 y1 x2 R) = (term446 A x1 y1 x2 R).
Proof. exact (@lem7038585 (term214 R x1 y1 x2) (term396 A R)). Qed.
Lemma lem7038587 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term447 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (eq_refl (term447 R x1 y1 x2 y2)). Qed.
Lemma lem7038588 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term448 R x1 y1 x2) = (term214 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : nat => @lem7038587 R x1 y1 x2 y2)). Qed.
Lemma lem7038589 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038590 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term449 R x1 y1 x2) = (term215 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7038589) (@lem7038588 R x1 y1 x2)). Qed.
Lemma lem7038591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038592 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) : (term450 R x1 y1 x2) = (term439 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7038591) (@lem7038590 R x1 y1 x2)). Qed.
Lemma lem7038593 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038594 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term445 A x1 y1 x2 R) = (term441 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7038592 R x1 y1 x2) (@lem7038593 A R)). Qed.
Lemma lem7038595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038596 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term451 A x1 y1 x2 R) = (term452 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7038595) (@lem7038594 A x1 y1 x2 R)). Qed.
Lemma lem7038597 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term447 R x1 y1 x2 y2) = (term205 R x1 y1 x2 y2).
Proof. exact (eq_refl (term447 R x1 y1 x2 y2)). Qed.
Lemma lem7038598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038599 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term453 R x1 y1 x2 y2) = (term454 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7038598) (@lem7038597 R x1 y1 x2 y2)). Qed.
Lemma lem7038600 {A : Type'} (R : type1605) : (term396 A R) = (term396 A R).
Proof. exact (eq_refl (term396 A R)). Qed.
Lemma lem7038601 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term455 A x1 y1 x2 y2 R) = (term456 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7038599 R x1 y1 x2 y2) (@lem7038600 A R)). Qed.
Lemma lem7038602 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term457 A x1 y1 x2 R) = (term458 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : nat => @lem7038601 A x1 y1 x2 y2 R)). Qed.
Lemma lem7038603 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038604 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term446 A x1 y1 x2 R) = (term459 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7038603) (@lem7038602 A x1 y1 x2 R)). Qed.
Lemma lem7038605 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : ((term445 A x1 y1 x2 R) = (term446 A x1 y1 x2 R)) = ((term441 A x1 y1 x2 R) = (term459 A x1 y1 x2 R)).
Proof. exact (MK_COMB (@lem7038596 A x1 y1 x2 R) (@lem7038604 A x1 y1 x2 R)). Qed.
Lemma lem7038606 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term441 A x1 y1 x2 R) = (term459 A x1 y1 x2 R).
Proof. exact (EQ_MP (@lem7038605 A x1 y1 x2 R) (@lem7038586 A x1 y1 x2 R)). Qed.
Lemma lem7038608 {A : Type'} (P : Prop) (Q : A -> Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7038609 {A : Type'} (P : Prop) (Q : type181 A) : (term460 A P Q) = (term461 A P Q).
Proof. exact (@lem7038608 (type695 A) P Q). Qed.
Lemma lem7038610 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term462 A x1 y1 x2 y2 R) = (term463 A x1 y1 x2 y2 R).
Proof. exact (@lem7038609 A (term205 R x1 y1 x2 y2) (term395 A R)). Qed.
Lemma lem7038611 {A : Type'} (x : type695 A) (R : type1605) : (term464 A R x) = (term393 A x R).
Proof. exact (eq_refl (term464 A R x)). Qed.
Lemma lem7038612 {A : Type'} (R : type1605) : (term465 A R) = (term395 A R).
Proof. exact (fun_ext (fun x : type695 A => @lem7038611 A x R)). Qed.
Lemma lem7038613 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7038614 {A : Type'} (R : type1605) : (term466 A R) = (term396 A R).
Proof. exact (MK_COMB (@lem7038613 A) (@lem7038612 A R)). Qed.
Lemma lem7038615 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term454 R x1 y1 x2 y2) = (term454 R x1 y1 x2 y2).
Proof. exact (eq_refl (term454 R x1 y1 x2 y2)). Qed.
Lemma lem7038616 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term462 A x1 y1 x2 y2 R) = (term456 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7038615 R x1 y1 x2 y2) (@lem7038614 A R)). Qed.
Lemma lem7038617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7038618 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term467 A x1 y1 x2 y2 R) = (term468 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7038617) (@lem7038616 A x1 y1 x2 y2 R)). Qed.
Lemma lem7038619 {A : Type'} (x : type695 A) (R : type1605) : (term464 A R x) = (term393 A x R).
Proof. exact (eq_refl (term464 A R x)). Qed.
Lemma lem7038620 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term454 R x1 y1 x2 y2) = (term454 R x1 y1 x2 y2).
Proof. exact (eq_refl (term454 R x1 y1 x2 y2)). Qed.
Lemma lem7038621 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) : (term469 A x1 y1 x2 y2 R x) = (term470 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7038620 R x1 y1 x2 y2) (@lem7038619 A x R)). Qed.
Lemma lem7038622 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term471 A x1 y1 x2 y2 R) = (term472 A x1 y1 x2 y2 R).
Proof. exact (fun_ext (fun x : type695 A => @lem7038621 A x1 y1 x2 y2 x R)). Qed.
Lemma lem7038623 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem7038624 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term463 A x1 y1 x2 y2 R) = (term473 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7038623 A) (@lem7038622 A x1 y1 x2 y2 R)). Qed.
Lemma lem7038625 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : ((term462 A x1 y1 x2 y2 R) = (term463 A x1 y1 x2 y2 R)) = ((term456 A x1 y1 x2 y2 R) = (term473 A x1 y1 x2 y2 R)).
Proof. exact (MK_COMB (@lem7038618 A x1 y1 x2 y2 R) (@lem7038624 A x1 y1 x2 y2 R)). Qed.
Lemma lem7038626 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) : (term456 A x1 y1 x2 y2 R) = (term473 A x1 y1 x2 y2 R).
Proof. exact (EQ_MP (@lem7038625 A x1 y1 x2 y2 R) (@lem7038610 A x1 y1 x2 y2 R)). Qed.
Lemma lem7038627 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term458 A x1 y1 x2 R) = (term474 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : nat => @lem7038626 A x1 y1 x2 y2 R)). Qed.
Lemma lem7038628 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038629 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term459 A x1 y1 x2 R) = (term475 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7038628) (@lem7038627 A x1 y1 x2 R)). Qed.
Lemma lem7038630 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) : (term441 A x1 y1 x2 R) = (term475 A x1 y1 x2 R).
Proof. exact (TRANS (@lem7038606 A x1 y1 x2 R) (@lem7038629 A x1 y1 x2 R)). Qed.
Lemma lem7038631 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term443 A x1 y1 R) = (term476 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : nat => @lem7038630 A x1 y1 x2 R)). Qed.
Lemma lem7038632 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038633 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term444 A x1 y1 R) = (term477 A x1 y1 R).
Proof. exact (MK_COMB (@lem7038632) (@lem7038631 A x1 y1 R)). Qed.
Lemma lem7038634 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) : (term426 A x1 y1 R) = (term477 A x1 y1 R).
Proof. exact (TRANS (@lem7038580 A x1 y1 R) (@lem7038633 A x1 y1 R)). Qed.
Lemma lem7038635 {A : Type'} (x1 : nat) (R : type1605) : (term428 A x1 R) = (term478 A x1 R).
Proof. exact (fun_ext (fun y1 : nat => @lem7038634 A x1 y1 R)). Qed.
Lemma lem7038636 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038637 {A : Type'} (x1 : nat) (R : type1605) : (term429 A x1 R) = (term479 A x1 R).
Proof. exact (MK_COMB (@lem7038636) (@lem7038635 A x1 R)). Qed.
Lemma lem7038638 {A : Type'} (x1 : nat) (R : type1605) : (term411 A x1 R) = (term479 A x1 R).
Proof. exact (TRANS (@lem7038554 A x1 R) (@lem7038637 A x1 R)). Qed.
Lemma lem7038639 {A : Type'} (R : type1605) : (term413 A R) = (term480 A R).
Proof. exact (fun_ext (fun x1 : nat => @lem7038638 A x1 R)). Qed.
Lemma lem7038640 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7038641 {A : Type'} (R : type1605) : (term414 A R) = (term481 A R).
Proof. exact (MK_COMB (@lem7038640) (@lem7038639 A R)). Qed.
Lemma lem7038642 {A : Type'} (R : type1605) : (term397 A R) = (term481 A R).
Proof. exact (TRANS (@lem7038528 A R) (@lem7038641 A R)). Qed.
Lemma lem7038644 {A : Type'} (R : type1605) : (term272 A R) = (term481 A R).
Proof. exact (TRANS (@lem7038502 A R) (@lem7038642 A R)). Qed.
Lemma lem7038645 {A : Type'} (R : type1605) : (term158 A R) = (term481 A R).
Proof. exact (TRANS (@lem7038161 A R) (@lem7038644 A R)). Qed.
Lemma lem7038646 {A : Type'} (R : type1605) (h1 : term158 A R) : term481 A R.
Proof. exact (EQ_MP (@lem7038645 A R) (@lem7037917 A R h1)). Qed.
Lemma lem7038652 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7038658 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7038665 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term177 A s R f g x) = (term482 A s R f g x).
Proof. exact (@lem17265 (@IN A x s) (term240 A R f g x)). Qed.
Lemma lem7038666 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term178 A s R f g) = (term483 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038665 A s R f g x)). Qed.
Lemma lem7038667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7038720 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term80 A s R f g) = (term484 A s R f g).
Proof. exact (MK_COMB (@lem7038667 A) (@lem7038666 A s R f g)). Qed.
Lemma lem7038721 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term484 A s R f g.
Proof. exact (EQ_MP (@lem7038720 A s R f g) (@lem7037920 A s R f g h1)). Qed.
Lemma lem7038727 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term191 A R f s g) : term191 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7038728 {A : Type'} (x1 : nat) (R : type1605) (h1 : term479 A x1 R) : term479 A x1 R.
Proof. exact (h1). Qed.
Lemma lem7038729 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) (h1 : term477 A x1 y1 R) : term477 A x1 y1 R.
Proof. exact (h1). Qed.
Lemma lem7038730 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) (h1 : term475 A x1 y1 x2 R) : term475 A x1 y1 x2 R.
Proof. exact (h1). Qed.
Lemma lem7038731 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) (h1 : term473 A x1 y1 x2 y2 R) : term473 A x1 y1 x2 y2 R.
Proof. exact (h1). Qed.
Lemma lem7038732 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term470 A x1 y1 x2 y2 x R) : term470 A x1 y1 x2 y2 x R.
Proof. exact (h1). Qed.
Lemma lem7038733 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7038740 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038741 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7038740 nat (nat -> nat) f x). Qed.
Lemma lem7038742 (m : nat) : (Nat.add m) = (@I (nat -> nat -> nat) Nat.add m).
Proof. exact (@lem7038741 Nat.add m). Qed.
Lemma lem7038743 (m' : nat) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem7038744 (m : nat) (m' : nat) : (Nat.add m m') = (@I (nat -> nat -> nat) Nat.add m m').
Proof. exact (MK_COMB (@lem7038742 m) (@lem7038743 m')). Qed.
Lemma lem7038746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038747 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7038746 nat nat f x). Qed.
Lemma lem7038748 (m : nat) (m' : nat) : (@I (nat -> nat -> nat) Nat.add m m') = (term485 m m').
Proof. exact (@lem7038747 (@I (nat -> nat -> nat) Nat.add m) m'). Qed.
Lemma lem7038750 (m : nat) (m' : nat) : (Nat.add m m') = (term485 m m').
Proof. exact (TRANS (@lem7038744 m m') (@lem7038748 m m')). Qed.
Lemma lem7038757 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038758 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7038757 nat (nat -> nat) f x). Qed.
Lemma lem7038759 (n : nat) : (Nat.add n) = (@I (nat -> nat -> nat) Nat.add n).
Proof. exact (@lem7038758 Nat.add n). Qed.
Lemma lem7038760 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7038761 (n : nat) (n' : nat) : (Nat.add n n') = (@I (nat -> nat -> nat) Nat.add n n').
Proof. exact (MK_COMB (@lem7038759 n) (@lem7038760 n')). Qed.
Lemma lem7038763 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038764 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7038763 nat nat f x). Qed.
Lemma lem7038765 (n : nat) (n' : nat) : (@I (nat -> nat -> nat) Nat.add n n') = (term485 n n').
Proof. exact (@lem7038764 (@I (nat -> nat -> nat) Nat.add n) n'). Qed.
Lemma lem7038767 (n : nat) (n' : nat) : (Nat.add n n') = (term485 n n').
Proof. exact (TRANS (@lem7038761 n n') (@lem7038765 n n')). Qed.
Lemma lem7038768 (R : type1605) (m : nat) (m' : nat) : (term486 R m m') = (term487 R m m').
Proof. exact (MK_COMB (@lem7038733 R) (@lem7038750 m m')). Qed.
Lemma lem7038769 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term28 R m m' n n') = (term488 R m m' n n').
Proof. exact (MK_COMB (@lem7038768 R m m') (@lem7038767 n n')). Qed.
Lemma lem7038771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038772 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7038771 nat (nat -> Prop) f x). Qed.
Lemma lem7038773 (R : type1605) (m : nat) (m' : nat) : (term487 R m m') = (term489 R m m').
Proof. exact (@lem7038772 R (term485 m m')). Qed.
Lemma lem7038774 (n : nat) (n' : nat) : (term485 n n') = (term485 n n').
Proof. exact (eq_refl (term485 n n')). Qed.
Lemma lem7038775 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term488 R m m' n n') = (term490 R m m' n n').
Proof. exact (MK_COMB (@lem7038773 R m m') (@lem7038774 n n')). Qed.
Lemma lem7038777 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038778 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7038777 nat Prop f x). Qed.
Lemma lem7038779 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term490 R m m' n n') = (term491 R m m' n n').
Proof. exact (@lem7038778 (term489 R m m') (term485 n n')). Qed.
Lemma lem7038780 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term488 R m m' n n') = (term491 R m m' n n').
Proof. exact (TRANS (@lem7038775 R m m' n n') (@lem7038779 R m m' n n')). Qed.
Lemma lem7038781 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term28 R m m' n n') = (term491 R m m' n n').
Proof. exact (TRANS (@lem7038769 R m m' n n') (@lem7038780 R m m' n n')). Qed.
Lemma lem7038782 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038790 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7038789 nat (nat -> Prop) f x). Qed.
Lemma lem7038791 (R : type1605) (m' : nat) : (R m') = (@I (nat -> nat -> Prop) R m').
Proof. exact (@lem7038790 R m'). Qed.
Lemma lem7038792 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7038793 (R : type1605) (m' : nat) (n' : nat) : (R m' n') = (@I (nat -> nat -> Prop) R m' n').
Proof. exact (MK_COMB (@lem7038791 R m') (@lem7038792 n')). Qed.
Lemma lem7038795 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038796 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7038795 nat Prop f x). Qed.
Lemma lem7038797 (R : type1605) (m' : nat) (n' : nat) : (@I (nat -> nat -> Prop) R m' n') = (term492 R m' n').
Proof. exact (@lem7038796 (@I (nat -> nat -> Prop) R m') n'). Qed.
Lemma lem7038799 (R : type1605) (m' : nat) (n' : nat) : (R m' n') = (term492 R m' n').
Proof. exact (TRANS (@lem7038793 R m' n') (@lem7038797 R m' n')). Qed.
Lemma lem7038800 (R : type1605) (m' : nat) (n' : nat) : (term493 R m' n') = (term494 R m' n').
Proof. exact (MK_COMB (@lem7038782) (@lem7038799 R m' n')). Qed.
Lemma lem7038801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038802 (R : type1605) (m' : nat) (n' : nat) : (term197 R m' n') = (term495 R m' n').
Proof. exact (MK_COMB (@lem7038801) (@lem7038800 R m' n')). Qed.
Lemma lem7038803 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term192 R m m' n n') = (term496 R m m' n n').
Proof. exact (MK_COMB (@lem7038802 R m' n') (@lem7038781 R m m' n n')). Qed.
Lemma lem7038804 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term193 R m m' n) = (term497 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7038803 R m m' n n')). Qed.
Lemma lem7038805 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7038806 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term194 R m m' n) = (term498 R m m' n).
Proof. exact (MK_COMB (@lem7038805) (@lem7038804 R m m' n)). Qed.
Lemma lem7038807 (R : type1605) (m : nat) (n : nat) : (term195 R m n) = (term499 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7038806 R m m' n)). Qed.
Lemma lem7038808 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7038809 (R : type1605) (m : nat) (n : nat) : (term196 R m n) = (term500 R m n).
Proof. exact (MK_COMB (@lem7038808) (@lem7038807 R m n)). Qed.
Lemma lem7038810 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038817 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038818 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7038817 nat (nat -> Prop) f x). Qed.
Lemma lem7038819 (R : type1605) (m : nat) : (R m) = (@I (nat -> nat -> Prop) R m).
Proof. exact (@lem7038818 R m). Qed.
Lemma lem7038820 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7038821 (R : type1605) (m : nat) (n : nat) : (R m n) = (@I (nat -> nat -> Prop) R m n).
Proof. exact (MK_COMB (@lem7038819 R m) (@lem7038820 n)). Qed.
Lemma lem7038823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038824 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7038823 nat Prop f x). Qed.
Lemma lem7038825 (R : type1605) (m : nat) (n : nat) : (@I (nat -> nat -> Prop) R m n) = (term492 R m n).
Proof. exact (@lem7038824 (@I (nat -> nat -> Prop) R m) n). Qed.
Lemma lem7038827 (R : type1605) (m : nat) (n : nat) : (R m n) = (term492 R m n).
Proof. exact (TRANS (@lem7038821 R m n) (@lem7038825 R m n)). Qed.
Lemma lem7038828 (R : type1605) (m : nat) (n : nat) : (term493 R m n) = (term494 R m n).
Proof. exact (MK_COMB (@lem7038810) (@lem7038827 R m n)). Qed.
Lemma lem7038829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038830 (R : type1605) (m : nat) (n : nat) : (term197 R m n) = (term495 R m n).
Proof. exact (MK_COMB (@lem7038829) (@lem7038828 R m n)). Qed.
Lemma lem7038831 (R : type1605) (m : nat) (n : nat) : (term199 R m n) = (term501 R m n).
Proof. exact (MK_COMB (@lem7038830 R m n) (@lem7038809 R m n)). Qed.
Lemma lem7038832 (R : type1605) (m : nat) : (term200 R m) = (term502 R m).
Proof. exact (fun_ext (fun n : nat => @lem7038831 R m n)). Qed.
Lemma lem7038833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7038834 (R : type1605) (m : nat) : (term201 R m) = (term503 R m).
Proof. exact (MK_COMB (@lem7038833) (@lem7038832 R m)). Qed.
Lemma lem7038835 (R : type1605) : (term202 R) = (term504 R).
Proof. exact (fun_ext (fun m : nat => @lem7038834 R m)). Qed.
Lemma lem7038836 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7038837 (R : type1605) : (term203 R) = (term505 R).
Proof. exact (MK_COMB (@lem7038836) (@lem7038835 R)). Qed.
Lemma lem7038838 (R : type1605) (h1 : term71 R) : term505 R.
Proof. exact (EQ_MP (@lem7038837 R) (@lem7038059 R h1)). Qed.
Lemma lem7038843 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038844 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7038843 (A -> Prop) Prop f x). Qed.
Lemma lem7038846 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7038844 A (@FINITE A) s). Qed.
Lemma lem7038855 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7038856 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7038861 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038863 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7038861 A nat f x). Qed.
Lemma lem7038868 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038869 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7038868 A nat f x). Qed.
Lemma lem7038871 {A : Type'} (g : A -> nat) (x : A) : (g x) = (@I (A -> nat) g x).
Proof. exact (@lem7038869 A g x). Qed.
Lemma lem7038872 {A : Type'} (R : type1605) (f : A -> nat) (x : A) : (term506 A R f x) = (term507 A R f x).
Proof. exact (MK_COMB (@lem7038856 R) (@lem7038863 A f x)). Qed.
Lemma lem7038873 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term240 A R f g x) = (term508 A R f g x).
Proof. exact (MK_COMB (@lem7038872 A R f x) (@lem7038871 A g x)). Qed.
Lemma lem7038875 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038876 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7038875 nat (nat -> Prop) f x). Qed.
Lemma lem7038877 {A : Type'} (R : type1605) (f : A -> nat) (x : A) : (term507 A R f x) = (term509 A R f x).
Proof. exact (@lem7038876 R (@I (A -> nat) f x)). Qed.
Lemma lem7038878 {A : Type'} (g : A -> nat) (x : A) : (@I (A -> nat) g x) = (@I (A -> nat) g x).
Proof. exact (eq_refl (@I (A -> nat) g x)). Qed.
Lemma lem7038879 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term508 A R f g x) = (term510 A R f g x).
Proof. exact (MK_COMB (@lem7038877 A R f x) (@lem7038878 A g x)). Qed.
Lemma lem7038881 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038882 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7038881 nat Prop f x). Qed.
Lemma lem7038883 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term510 A R f g x) = (term511 A R f g x).
Proof. exact (@lem7038882 (term509 A R f x) (@I (A -> nat) g x)). Qed.
Lemma lem7038884 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term508 A R f g x) = (term511 A R f g x).
Proof. exact (TRANS (@lem7038879 A R f g x) (@lem7038883 A R f g x)). Qed.
Lemma lem7038885 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term240 A R f g x) = (term511 A R f g x).
Proof. exact (TRANS (@lem7038873 A R f g x) (@lem7038884 A R f g x)). Qed.
Lemma lem7038886 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038893 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038894 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7038893 A (type686 A) f x). Qed.
Lemma lem7038895 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7038894 A (@IN A) x). Qed.
Lemma lem7038896 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7038897 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7038895 A x) (@lem7038896 A s)). Qed.
Lemma lem7038899 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038900 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7038899 (A -> Prop) Prop f x). Qed.
Lemma lem7038901 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term512 A x s).
Proof. exact (@lem7038900 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7038903 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term512 A x s).
Proof. exact (TRANS (@lem7038897 A x s) (@lem7038901 A x s)). Qed.
Lemma lem7038904 {A : Type'} (x : A) (s : A -> Prop) : (term513 A x s) = (term514 A x s).
Proof. exact (MK_COMB (@lem7038886) (@lem7038903 A x s)). Qed.
Lemma lem7038905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7038906 {A : Type'} (x : A) (s : A -> Prop) : (term515 A x s) = (term516 A x s).
Proof. exact (MK_COMB (@lem7038905) (@lem7038904 A x s)). Qed.
Lemma lem7038907 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term482 A s R f g x) = (term517 A s R f g x).
Proof. exact (MK_COMB (@lem7038906 A x s) (@lem7038885 A R f g x)). Qed.
Lemma lem7038908 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term483 A s R f g) = (term518 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7038907 A s R f g x)). Qed.
Lemma lem7038909 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7038910 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term484 A s R f g) = (term519 A s R f g).
Proof. exact (MK_COMB (@lem7038909 A) (@lem7038908 A s R f g)). Qed.
Lemma lem7038911 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term519 A s R f g.
Proof. exact (EQ_MP (@lem7038910 A s R f g) (@lem7038721 A s R f g h1)). Qed.
Lemma lem7038912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7038913 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7038920 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038921 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7038920 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7038922 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7038921 A (@nsum A) s). Qed.
Lemma lem7038923 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7038924 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f).
Proof. exact (MK_COMB (@lem7038922 A s) (@lem7038923 A f)). Qed.
Lemma lem7038926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038927 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7038926 (A -> nat) nat f x). Qed.
Lemma lem7038928 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f) = (term520 A s f).
Proof. exact (@lem7038927 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) f). Qed.
Lemma lem7038930 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term520 A s f).
Proof. exact (TRANS (@lem7038924 A s f) (@lem7038928 A s f)). Qed.
Lemma lem7038937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038938 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7038937 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7038939 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7038938 A (@nsum A) s). Qed.
Lemma lem7038940 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7038941 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g).
Proof. exact (MK_COMB (@lem7038939 A s) (@lem7038940 A g)). Qed.
Lemma lem7038943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038944 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7038943 (A -> nat) nat f x). Qed.
Lemma lem7038945 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g) = (term520 A s g).
Proof. exact (@lem7038944 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) g). Qed.
Lemma lem7038947 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (term520 A s g).
Proof. exact (TRANS (@lem7038941 A s g) (@lem7038945 A s g)). Qed.
Lemma lem7038948 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term141 A R s f) = (term521 A R s f).
Proof. exact (MK_COMB (@lem7038913 R) (@lem7038930 A s f)). Qed.
Lemma lem7038949 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term522 A R f s g).
Proof. exact (MK_COMB (@lem7038948 A R s f) (@lem7038947 A s g)). Qed.
Lemma lem7038951 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038952 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7038951 nat (nat -> Prop) f x). Qed.
Lemma lem7038953 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term521 A R s f) = (term523 A R s f).
Proof. exact (@lem7038952 R (term520 A s f)). Qed.
Lemma lem7038954 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term520 A s g) = (term520 A s g).
Proof. exact (eq_refl (term520 A s g)). Qed.
Lemma lem7038955 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term522 A R f s g) = (term524 A R f s g).
Proof. exact (MK_COMB (@lem7038953 A R s f) (@lem7038954 A s g)). Qed.
Lemma lem7038957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038958 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7038957 nat Prop f x). Qed.
Lemma lem7038959 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term524 A R f s g) = (term525 A R f s g).
Proof. exact (@lem7038958 (term523 A R s f) (term520 A s g)). Qed.
Lemma lem7038960 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term522 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7038955 A R f s g) (@lem7038959 A R f s g)). Qed.
Lemma lem7038961 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7038949 A R f s g) (@lem7038960 A R f s g)). Qed.
Lemma lem7038962 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term191 A R f s g) = (term526 A R f s g).
Proof. exact (MK_COMB (@lem7038912) (@lem7038961 A R f s g)). Qed.
Lemma lem7038964 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7038971 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038972 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7038971 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7038973 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7038972 A (@nsum A) s). Qed.
Lemma lem7038974 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7038975 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f).
Proof. exact (MK_COMB (@lem7038973 A s) (@lem7038974 A f)). Qed.
Lemma lem7038977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038978 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7038977 (A -> nat) nat f x). Qed.
Lemma lem7038979 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s f) = (term520 A s f).
Proof. exact (@lem7038978 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) f). Qed.
Lemma lem7038981 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term520 A s f).
Proof. exact (TRANS (@lem7038975 A s f) (@lem7038979 A s f)). Qed.
Lemma lem7038988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038989 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem7038988 (A -> Prop) (type705 A) f x). Qed.
Lemma lem7038990 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s).
Proof. exact (@lem7038989 A (@nsum A) s). Qed.
Lemma lem7038991 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7038992 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g).
Proof. exact (MK_COMB (@lem7038990 A s) (@lem7038991 A g)). Qed.
Lemma lem7038994 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7038995 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem7038994 (A -> nat) nat f x). Qed.
Lemma lem7038996 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s g) = (term520 A s g).
Proof. exact (@lem7038995 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) s) g). Qed.
Lemma lem7038998 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (term520 A s g).
Proof. exact (TRANS (@lem7038992 A s g) (@lem7038996 A s g)). Qed.
Lemma lem7038999 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term141 A R s f) = (term521 A R s f).
Proof. exact (MK_COMB (@lem7038964 R) (@lem7038981 A s f)). Qed.
Lemma lem7039000 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term522 A R f s g).
Proof. exact (MK_COMB (@lem7038999 A R s f) (@lem7038998 A s g)). Qed.
Lemma lem7039002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039003 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7039002 nat (nat -> Prop) f x). Qed.
Lemma lem7039004 {A : Type'} (R : type1605) (s : A -> Prop) (f : A -> nat) : (term521 A R s f) = (term523 A R s f).
Proof. exact (@lem7039003 R (term520 A s f)). Qed.
Lemma lem7039005 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term520 A s g) = (term520 A s g).
Proof. exact (eq_refl (term520 A s g)). Qed.
Lemma lem7039006 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term522 A R f s g) = (term524 A R f s g).
Proof. exact (MK_COMB (@lem7039004 A R s f) (@lem7039005 A s g)). Qed.
Lemma lem7039008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039009 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7039008 nat Prop f x). Qed.
Lemma lem7039010 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term524 A R f s g) = (term525 A R f s g).
Proof. exact (@lem7039009 (term523 A R s f) (term520 A s g)). Qed.
Lemma lem7039011 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term522 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7039006 A R f s g) (@lem7039010 A R f s g)). Qed.
Lemma lem7039012 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term25 A R f s g) = (term525 A R f s g).
Proof. exact (TRANS (@lem7039000 A R f s g) (@lem7039011 A R f s g)). Qed.
Lemma lem7039013 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7039014 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7039015 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7039024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039025 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7039024 (A -> nat) (type694 A) f x). Qed.
Lemma lem7039026 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7039025 A x f). Qed.
Lemma lem7039027 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7039028 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7039026 A x f) (@lem7039027 A g)). Qed.
Lemma lem7039030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039031 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7039030 (A -> nat) (type684 A) f x). Qed.
Lemma lem7039032 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g) = (term527 A x f g).
Proof. exact (@lem7039031 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7039033 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (term527 A x f g).
Proof. exact (TRANS (@lem7039028 A x f g) (@lem7039032 A x f g)). Qed.
Lemma lem7039034 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7039035 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term528 A x f g s).
Proof. exact (MK_COMB (@lem7039033 A x f g) (@lem7039034 A s)). Qed.
Lemma lem7039037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039038 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7039037 (A -> Prop) A f x). Qed.
Lemma lem7039039 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term528 A x f g s) = (term529 A x f g s).
Proof. exact (@lem7039038 A (term527 A x f g) s). Qed.
Lemma lem7039041 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term529 A x f g s).
Proof. exact (TRANS (@lem7039035 A x f g s) (@lem7039039 A x f g s)). Qed.
Lemma lem7039042 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term530 A x f g s) = (term531 A x f g s).
Proof. exact (MK_COMB (@lem7039015 A f) (@lem7039041 A x f g s)). Qed.
Lemma lem7039044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039045 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7039044 A nat f x). Qed.
Lemma lem7039046 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term531 A x f g s) = (term532 A x f g s).
Proof. exact (@lem7039045 A f (term529 A x f g s)). Qed.
Lemma lem7039047 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term530 A x f g s) = (term532 A x f g s).
Proof. exact (TRANS (@lem7039042 A x f g s) (@lem7039046 A x f g s)). Qed.
Lemma lem7039048 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7039057 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039058 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7039057 (A -> nat) (type694 A) f x). Qed.
Lemma lem7039059 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7039058 A x f). Qed.
Lemma lem7039060 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7039061 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7039059 A x f) (@lem7039060 A g)). Qed.
Lemma lem7039063 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039064 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7039063 (A -> nat) (type684 A) f x). Qed.
Lemma lem7039065 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g) = (term527 A x f g).
Proof. exact (@lem7039064 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7039066 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (term527 A x f g).
Proof. exact (TRANS (@lem7039061 A x f g) (@lem7039065 A x f g)). Qed.
Lemma lem7039067 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7039068 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term528 A x f g s).
Proof. exact (MK_COMB (@lem7039066 A x f g) (@lem7039067 A s)). Qed.
Lemma lem7039070 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039071 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7039070 (A -> Prop) A f x). Qed.
Lemma lem7039072 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term528 A x f g s) = (term529 A x f g s).
Proof. exact (@lem7039071 A (term527 A x f g) s). Qed.
Lemma lem7039074 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term529 A x f g s).
Proof. exact (TRANS (@lem7039068 A x f g s) (@lem7039072 A x f g s)). Qed.
Lemma lem7039075 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term533 A x f g s) = (term534 A x f g s).
Proof. exact (MK_COMB (@lem7039048 A g) (@lem7039074 A x f g s)). Qed.
Lemma lem7039077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039078 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7039077 A nat f x). Qed.
Lemma lem7039079 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term534 A x f g s) = (term535 A x f g s).
Proof. exact (@lem7039078 A g (term529 A x f g s)). Qed.
Lemma lem7039080 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term533 A x f g s) = (term535 A x f g s).
Proof. exact (TRANS (@lem7039075 A x f g s) (@lem7039079 A x f g s)). Qed.
Lemma lem7039081 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term536 A R x f g s) = (term537 A R x f g s).
Proof. exact (MK_COMB (@lem7039014 R) (@lem7039047 A x f g s)). Qed.
Lemma lem7039082 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term538 A R x f g s) = (term539 A R x f g s).
Proof. exact (MK_COMB (@lem7039081 A R x f g s) (@lem7039080 A x f g s)). Qed.
Lemma lem7039084 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039085 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7039084 nat (nat -> Prop) f x). Qed.
Lemma lem7039086 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term537 A R x f g s) = (term540 A R x f g s).
Proof. exact (@lem7039085 R (term532 A x f g s)). Qed.
Lemma lem7039087 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term535 A x f g s) = (term535 A x f g s).
Proof. exact (eq_refl (term535 A x f g s)). Qed.
Lemma lem7039088 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term539 A R x f g s) = (term541 A R x f g s).
Proof. exact (MK_COMB (@lem7039086 A R x f g s) (@lem7039087 A x f g s)). Qed.
Lemma lem7039090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039091 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7039090 nat Prop f x). Qed.
Lemma lem7039092 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term541 A R x f g s) = (term542 A R x f g s).
Proof. exact (@lem7039091 (term540 A R x f g s) (term535 A x f g s)). Qed.
Lemma lem7039093 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term539 A R x f g s) = (term542 A R x f g s).
Proof. exact (TRANS (@lem7039088 A R x f g s) (@lem7039092 A R x f g s)). Qed.
Lemma lem7039094 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term538 A R x f g s) = (term542 A R x f g s).
Proof. exact (TRANS (@lem7039082 A R x f g s) (@lem7039093 A R x f g s)). Qed.
Lemma lem7039095 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term543 A R x f g s) = (term544 A R x f g s).
Proof. exact (MK_COMB (@lem7039013) (@lem7039094 A R x f g s)). Qed.
Lemma lem7039096 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7039105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039106 {A : Type'} (f : type695 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7039105 (A -> nat) (type694 A) f x). Qed.
Lemma lem7039107 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7039106 A x f). Qed.
Lemma lem7039108 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7039109 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7039107 A x f) (@lem7039108 A g)). Qed.
Lemma lem7039111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039112 {A : Type'} (f : type694 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7039111 (A -> nat) (type684 A) f x). Qed.
Lemma lem7039113 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f g) = (term527 A x f g).
Proof. exact (@lem7039112 A (@I ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7039114 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) : (x f g) = (term527 A x f g).
Proof. exact (TRANS (@lem7039109 A x f g) (@lem7039113 A x f g)). Qed.
Lemma lem7039115 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7039116 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term528 A x f g s).
Proof. exact (MK_COMB (@lem7039114 A x f g) (@lem7039115 A s)). Qed.
Lemma lem7039118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039119 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7039118 (A -> Prop) A f x). Qed.
Lemma lem7039120 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term528 A x f g s) = (term529 A x f g s).
Proof. exact (@lem7039119 A (term527 A x f g) s). Qed.
Lemma lem7039122 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (x f g s) = (term529 A x f g s).
Proof. exact (TRANS (@lem7039116 A x f g s) (@lem7039120 A x f g s)). Qed.
Lemma lem7039123 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7039124 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term545 A x f g s) = (term546 A x f g s).
Proof. exact (MK_COMB (@lem7039096 A) (@lem7039122 A x f g s)). Qed.
Lemma lem7039125 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term547 A x f g s) = (term548 A x f g s).
Proof. exact (MK_COMB (@lem7039124 A x f g s) (@lem7039123 A s)). Qed.
Lemma lem7039127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039128 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7039127 A (type686 A) f x). Qed.
Lemma lem7039129 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term546 A x f g s) = (term549 A x f g s).
Proof. exact (@lem7039128 A (@IN A) (term529 A x f g s)). Qed.
Lemma lem7039130 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7039131 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term548 A x f g s) = (term550 A x f g s).
Proof. exact (MK_COMB (@lem7039129 A x f g s) (@lem7039130 A s)). Qed.
Lemma lem7039133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039134 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7039133 (A -> Prop) Prop f x). Qed.
Lemma lem7039135 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term550 A x f g s) = (term551 A x f g s).
Proof. exact (@lem7039134 A (term549 A x f g s) s). Qed.
Lemma lem7039136 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term548 A x f g s) = (term551 A x f g s).
Proof. exact (TRANS (@lem7039131 A x f g s) (@lem7039135 A x f g s)). Qed.
Lemma lem7039137 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term547 A x f g s) = (term551 A x f g s).
Proof. exact (TRANS (@lem7039125 A x f g s) (@lem7039136 A x f g s)). Qed.
Lemma lem7039138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7039139 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term552 A x f g s) = (term553 A x f g s).
Proof. exact (MK_COMB (@lem7039138) (@lem7039137 A x f g s)). Qed.
Lemma lem7039140 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term554 A R x f g s) = (term555 A R x f g s).
Proof. exact (MK_COMB (@lem7039139 A x f g s) (@lem7039095 A R x f g s)). Qed.
Lemma lem7039147 {A : Type'} (s : A -> Prop) : (term251 A s) = (term251 A s).
Proof. exact (eq_refl (term251 A s)). Qed.
Lemma lem7039148 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term556 A R x f g s) = (term557 A R x f g s).
Proof. exact (MK_COMB (@lem7039147 A s) (@lem7039140 A R x f g s)). Qed.
Lemma lem7039149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7039154 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039155 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7039154 (A -> Prop) Prop f x). Qed.
Lemma lem7039157 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7039155 A (@FINITE A) s). Qed.
Lemma lem7039158 {A : Type'} (s : A -> Prop) : (term290 A s) = (term558 A s).
Proof. exact (MK_COMB (@lem7039149) (@lem7039157 A s)). Qed.
Lemma lem7039159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7039160 {A : Type'} (s : A -> Prop) : (term255 A s) = (term559 A s).
Proof. exact (MK_COMB (@lem7039159) (@lem7039158 A s)). Qed.
Lemma lem7039161 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term560 A R x f g s) = (term561 A R x f g s).
Proof. exact (MK_COMB (@lem7039160 A s) (@lem7039148 A R x f g s)). Qed.
Lemma lem7039162 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7039163 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term562 A R x f g s) = (term563 A R x f g s).
Proof. exact (MK_COMB (@lem7039162) (@lem7039161 A R x f g s)). Qed.
Lemma lem7039164 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term564 A x R f s g) = (term565 A x R f s g).
Proof. exact (MK_COMB (@lem7039163 A R x f g s) (@lem7039012 A R f s g)). Qed.
Lemma lem7039165 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term566 A x R f g) = (term567 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7039164 A x R f s g)). Qed.
Lemma lem7039166 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7039167 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term568 A x R f g) = (term569 A x R f g).
Proof. exact (MK_COMB (@lem7039166 A) (@lem7039165 A x R f g)). Qed.
Lemma lem7039168 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term570 A x R f) = (term571 A x R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7039167 A x R f g)). Qed.
Lemma lem7039169 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7039170 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term389 A x R f) = (term572 A x R f).
Proof. exact (MK_COMB (@lem7039169 A) (@lem7039168 A x R f)). Qed.
Lemma lem7039171 {A : Type'} (x : type695 A) (R : type1605) : (term391 A x R) = (term573 A x R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7039170 A x R f)). Qed.
Lemma lem7039172 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7039173 {A : Type'} (x : type695 A) (R : type1605) : (term393 A x R) = (term574 A x R).
Proof. exact (MK_COMB (@lem7039172 A) (@lem7039171 A x R)). Qed.
Lemma lem7039174 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7039175 (R : type1605) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7039182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039183 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7039182 nat (nat -> nat) f x). Qed.
Lemma lem7039184 (x1 : nat) : (Nat.add x1) = (@I (nat -> nat -> nat) Nat.add x1).
Proof. exact (@lem7039183 Nat.add x1). Qed.
Lemma lem7039185 (y1 : nat) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem7039186 (x1 : nat) (y1 : nat) : (Nat.add x1 y1) = (@I (nat -> nat -> nat) Nat.add x1 y1).
Proof. exact (MK_COMB (@lem7039184 x1) (@lem7039185 y1)). Qed.
Lemma lem7039188 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039189 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7039188 nat nat f x). Qed.
Lemma lem7039190 (x1 : nat) (y1 : nat) : (@I (nat -> nat -> nat) Nat.add x1 y1) = (term485 x1 y1).
Proof. exact (@lem7039189 (@I (nat -> nat -> nat) Nat.add x1) y1). Qed.
Lemma lem7039192 (x1 : nat) (y1 : nat) : (Nat.add x1 y1) = (term485 x1 y1).
Proof. exact (TRANS (@lem7039186 x1 y1) (@lem7039190 x1 y1)). Qed.
Lemma lem7039199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039200 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7039199 nat (nat -> nat) f x). Qed.
Lemma lem7039201 (x2 : nat) : (Nat.add x2) = (@I (nat -> nat -> nat) Nat.add x2).
Proof. exact (@lem7039200 Nat.add x2). Qed.
Lemma lem7039202 (y2 : nat) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7039203 (x2 : nat) (y2 : nat) : (Nat.add x2 y2) = (@I (nat -> nat -> nat) Nat.add x2 y2).
Proof. exact (MK_COMB (@lem7039201 x2) (@lem7039202 y2)). Qed.
Lemma lem7039205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039206 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7039205 nat nat f x). Qed.
Lemma lem7039207 (x2 : nat) (y2 : nat) : (@I (nat -> nat -> nat) Nat.add x2 y2) = (term485 x2 y2).
Proof. exact (@lem7039206 (@I (nat -> nat -> nat) Nat.add x2) y2). Qed.
Lemma lem7039209 (x2 : nat) (y2 : nat) : (Nat.add x2 y2) = (term485 x2 y2).
Proof. exact (TRANS (@lem7039203 x2 y2) (@lem7039207 x2 y2)). Qed.
Lemma lem7039210 (R : type1605) (x1 : nat) (y1 : nat) : (term486 R x1 y1) = (term487 R x1 y1).
Proof. exact (MK_COMB (@lem7039175 R) (@lem7039192 x1 y1)). Qed.
Lemma lem7039211 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term28 R x1 y1 x2 y2) = (term488 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7039210 R x1 y1) (@lem7039209 x2 y2)). Qed.
Lemma lem7039213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039214 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7039213 nat (nat -> Prop) f x). Qed.
Lemma lem7039215 (R : type1605) (x1 : nat) (y1 : nat) : (term487 R x1 y1) = (term489 R x1 y1).
Proof. exact (@lem7039214 R (term485 x1 y1)). Qed.
Lemma lem7039216 (x2 : nat) (y2 : nat) : (term485 x2 y2) = (term485 x2 y2).
Proof. exact (eq_refl (term485 x2 y2)). Qed.
Lemma lem7039217 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term488 R x1 y1 x2 y2) = (term490 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7039215 R x1 y1) (@lem7039216 x2 y2)). Qed.
Lemma lem7039219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039220 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7039219 nat Prop f x). Qed.
Lemma lem7039221 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term490 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (@lem7039220 (term489 R x1 y1) (term485 x2 y2)). Qed.
Lemma lem7039222 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term488 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7039217 R x1 y1 x2 y2) (@lem7039221 R x1 y1 x2 y2)). Qed.
Lemma lem7039223 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term28 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7039211 R x1 y1 x2 y2) (@lem7039222 R x1 y1 x2 y2)). Qed.
Lemma lem7039224 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term575 R x1 y1 x2 y2) = (term576 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7039174) (@lem7039223 R x1 y1 x2 y2)). Qed.
Lemma lem7039231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039232 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7039231 nat (nat -> Prop) f x). Qed.
Lemma lem7039233 (R : type1605) (y1 : nat) : (R y1) = (@I (nat -> nat -> Prop) R y1).
Proof. exact (@lem7039232 R y1). Qed.
Lemma lem7039234 (y2 : nat) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7039235 (R : type1605) (y1 : nat) (y2 : nat) : (R y1 y2) = (@I (nat -> nat -> Prop) R y1 y2).
Proof. exact (MK_COMB (@lem7039233 R y1) (@lem7039234 y2)). Qed.
Lemma lem7039237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039238 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7039237 nat Prop f x). Qed.
Lemma lem7039239 (R : type1605) (y1 : nat) (y2 : nat) : (@I (nat -> nat -> Prop) R y1 y2) = (term492 R y1 y2).
Proof. exact (@lem7039238 (@I (nat -> nat -> Prop) R y1) y2). Qed.
Lemma lem7039241 (R : type1605) (y1 : nat) (y2 : nat) : (R y1 y2) = (term492 R y1 y2).
Proof. exact (TRANS (@lem7039235 R y1 y2) (@lem7039239 R y1 y2)). Qed.
Lemma lem7039248 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039249 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7039248 nat (nat -> Prop) f x). Qed.
Lemma lem7039250 (R : type1605) (x1 : nat) : (R x1) = (@I (nat -> nat -> Prop) R x1).
Proof. exact (@lem7039249 R x1). Qed.
Lemma lem7039251 (x2 : nat) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem7039252 (R : type1605) (x1 : nat) (x2 : nat) : (R x1 x2) = (@I (nat -> nat -> Prop) R x1 x2).
Proof. exact (MK_COMB (@lem7039250 R x1) (@lem7039251 x2)). Qed.
Lemma lem7039254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7039255 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7039254 nat Prop f x). Qed.
Lemma lem7039256 (R : type1605) (x1 : nat) (x2 : nat) : (@I (nat -> nat -> Prop) R x1 x2) = (term492 R x1 x2).
Proof. exact (@lem7039255 (@I (nat -> nat -> Prop) R x1) x2). Qed.
Lemma lem7039258 (R : type1605) (x1 : nat) (x2 : nat) : (R x1 x2) = (term492 R x1 x2).
Proof. exact (TRANS (@lem7039252 R x1 x2) (@lem7039256 R x1 x2)). Qed.
Lemma lem7039259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7039260 (R : type1605) (x1 : nat) (x2 : nat) : (term577 R x1 x2) = (term578 R x1 x2).
Proof. exact (MK_COMB (@lem7039259) (@lem7039258 R x1 x2)). Qed.
Lemma lem7039261 (x1 : nat) (x2 : nat) (R : type1605) (y1 : nat) (y2 : nat) : (term206 x1 x2 R y1 y2) = (term579 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7039260 R x1 x2) (@lem7039241 R y1 y2)). Qed.
Lemma lem7039262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7039263 (x1 : nat) (x2 : nat) (R : type1605) (y1 : nat) (y2 : nat) : (term580 x1 x2 R y1 y2) = (term581 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7039262) (@lem7039261 x1 x2 R y1 y2)). Qed.
Lemma lem7039264 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term205 R x1 y1 x2 y2) = (term582 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7039263 x1 x2 R y1 y2) (@lem7039224 R x1 y1 x2 y2)). Qed.
Lemma lem7039265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7039266 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term454 R x1 y1 x2 y2) = (term583 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7039265) (@lem7039264 R x1 y1 x2 y2)). Qed.
Lemma lem7039267 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) : (term470 A x1 y1 x2 y2 x R) = (term584 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7039266 R x1 y1 x2 y2) (@lem7039173 A x R)). Qed.
Lemma lem7039268 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term470 A x1 y1 x2 y2 x R) : term584 A x1 y1 x2 y2 x R.
Proof. exact (EQ_MP (@lem7039267 A x1 y1 x2 y2 x R) (@lem7038732 A x1 y1 x2 y2 x R h1)). Qed.
Lemma lem7039269 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term582 R x1 y1 x2 y2.
Proof. exact (h1). Qed.
Lemma lem7039270 {A : Type'} (x : type695 A) (R : type1605) (h1 : term574 A x R) : term574 A x R.
Proof. exact (h1). Qed.
Lemma lem7039272 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term579 x1 x2 R y1 y2.
Proof. exact (proj1 (@lem7039269 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039276 {A : Type'} (P : Prop) (Q : A -> Prop) : (term585 A P Q) = (term586 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7039277 (P : Prop) (Q : nat -> Prop) : (term587 P Q) = (term588 P Q).
Proof. exact (@lem7039276 nat P Q). Qed.
Lemma lem7039278 (R : type1605) (m : nat) (n : nat) : (term589 R m n) = (term590 R m n).
Proof. exact (@lem7039277 (term494 R m n) (term499 R m n)). Qed.
Lemma lem7039279 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term591 R m n m') = (term498 R m m' n).
Proof. exact (eq_refl (term591 R m n m')). Qed.
Lemma lem7039280 (R : type1605) (m : nat) (n : nat) : (term592 R m n) = (term499 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7039279 R m m' n)). Qed.
Lemma lem7039281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039282 (R : type1605) (m : nat) (n : nat) : (term593 R m n) = (term500 R m n).
Proof. exact (MK_COMB (@lem7039281) (@lem7039280 R m n)). Qed.
Lemma lem7039283 (R : type1605) (m : nat) (n : nat) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7039284 (R : type1605) (m : nat) (n : nat) : (term589 R m n) = (term501 R m n).
Proof. exact (MK_COMB (@lem7039283 R m n) (@lem7039282 R m n)). Qed.
Lemma lem7039285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7039286 (R : type1605) (m : nat) (n : nat) : (term594 R m n) = (term595 R m n).
Proof. exact (MK_COMB (@lem7039285) (@lem7039284 R m n)). Qed.
Lemma lem7039287 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term591 R m n m') = (term498 R m m' n).
Proof. exact (eq_refl (term591 R m n m')). Qed.
Lemma lem7039288 (R : type1605) (m : nat) (n : nat) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7039289 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term596 R m n m') = (term597 R m m' n).
Proof. exact (MK_COMB (@lem7039288 R m n) (@lem7039287 R m m' n)). Qed.
Lemma lem7039290 (R : type1605) (m : nat) (n : nat) : (term598 R m n) = (term599 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7039289 R m m' n)). Qed.
Lemma lem7039291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039292 (R : type1605) (m : nat) (n : nat) : (term590 R m n) = (term600 R m n).
Proof. exact (MK_COMB (@lem7039291) (@lem7039290 R m n)). Qed.
Lemma lem7039293 (R : type1605) (m : nat) (n : nat) : ((term589 R m n) = (term590 R m n)) = ((term501 R m n) = (term600 R m n)).
Proof. exact (MK_COMB (@lem7039286 R m n) (@lem7039292 R m n)). Qed.
Lemma lem7039294 (R : type1605) (m : nat) (n : nat) : (term501 R m n) = (term600 R m n).
Proof. exact (EQ_MP (@lem7039293 R m n) (@lem7039278 R m n)). Qed.
Lemma lem7039296 {A : Type'} (P : Prop) (Q : A -> Prop) : (term585 A P Q) = (term586 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7039297 (P : Prop) (Q : nat -> Prop) : (term587 P Q) = (term588 P Q).
Proof. exact (@lem7039296 nat P Q). Qed.
Lemma lem7039298 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term601 R m m' n) = (term602 R m m' n).
Proof. exact (@lem7039297 (term494 R m n) (term497 R m m' n)). Qed.
Lemma lem7039299 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term603 R m m' n n') = (term496 R m m' n n').
Proof. exact (eq_refl (term603 R m m' n n')). Qed.
Lemma lem7039300 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term604 R m m' n) = (term497 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7039299 R m m' n n')). Qed.
Lemma lem7039301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039302 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term605 R m m' n) = (term498 R m m' n).
Proof. exact (MK_COMB (@lem7039301) (@lem7039300 R m m' n)). Qed.
Lemma lem7039303 (R : type1605) (m : nat) (n : nat) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7039304 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term601 R m m' n) = (term597 R m m' n).
Proof. exact (MK_COMB (@lem7039303 R m n) (@lem7039302 R m m' n)). Qed.
Lemma lem7039305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7039306 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term606 R m m' n) = (term607 R m m' n).
Proof. exact (MK_COMB (@lem7039305) (@lem7039304 R m m' n)). Qed.
Lemma lem7039307 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term603 R m m' n n') = (term496 R m m' n n').
Proof. exact (eq_refl (term603 R m m' n n')). Qed.
Lemma lem7039308 (R : type1605) (m : nat) (n : nat) : (term495 R m n) = (term495 R m n).
Proof. exact (eq_refl (term495 R m n)). Qed.
Lemma lem7039309 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term608 R m m' n n') = (term609 R m m' n n').
Proof. exact (MK_COMB (@lem7039308 R m n) (@lem7039307 R m m' n n')). Qed.
Lemma lem7039310 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term610 R m m' n) = (term611 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7039309 R m m' n n')). Qed.
Lemma lem7039311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039312 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term602 R m m' n) = (term612 R m m' n).
Proof. exact (MK_COMB (@lem7039311) (@lem7039310 R m m' n)). Qed.
Lemma lem7039313 (R : type1605) (m : nat) (m' : nat) (n : nat) : ((term601 R m m' n) = (term602 R m m' n)) = ((term597 R m m' n) = (term612 R m m' n)).
Proof. exact (MK_COMB (@lem7039306 R m m' n) (@lem7039312 R m m' n)). Qed.
Lemma lem7039314 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term597 R m m' n) = (term612 R m m' n).
Proof. exact (EQ_MP (@lem7039313 R m m' n) (@lem7039298 R m m' n)). Qed.
Lemma lem7039315 (R : type1605) (m : nat) (n : nat) : (term599 R m n) = (term613 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7039314 R m m' n)). Qed.
Lemma lem7039316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039317 (R : type1605) (m : nat) (n : nat) : (term600 R m n) = (term614 R m n).
Proof. exact (MK_COMB (@lem7039316) (@lem7039315 R m n)). Qed.
Lemma lem7039318 (R : type1605) (m : nat) (n : nat) : (term501 R m n) = (term614 R m n).
Proof. exact (TRANS (@lem7039294 R m n) (@lem7039317 R m n)). Qed.
Lemma lem7039319 (R : type1605) (m : nat) : (term502 R m) = (term615 R m).
Proof. exact (fun_ext (fun n : nat => @lem7039318 R m n)). Qed.
Lemma lem7039320 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039321 (R : type1605) (m : nat) : (term503 R m) = (term616 R m).
Proof. exact (MK_COMB (@lem7039320) (@lem7039319 R m)). Qed.
Lemma lem7039322 (R : type1605) : (term504 R) = (term617 R).
Proof. exact (fun_ext (fun m : nat => @lem7039321 R m)). Qed.
Lemma lem7039323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039324 (R : type1605) : (term505 R) = (term618 R).
Proof. exact (MK_COMB (@lem7039323) (@lem7039322 R)). Qed.
Lemma lem7039337 (R : type1605) (m : nat) (m' : nat) (n : nat) (n' : nat) : (term609 R m m' n n') = (term609 R m m' n n').
Proof. exact (eq_refl (term609 R m m' n n')). Qed.
Lemma lem7039338 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term611 R m m' n) = (term611 R m m' n).
Proof. exact (fun_ext (fun n' : nat => @lem7039337 R m m' n n')). Qed.
Lemma lem7039339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039340 (R : type1605) (m : nat) (m' : nat) (n : nat) : (term612 R m m' n) = (term612 R m m' n).
Proof. exact (MK_COMB (@lem7039339) (@lem7039338 R m m' n)). Qed.
Lemma lem7039341 (R : type1605) (m : nat) (n : nat) : (term613 R m n) = (term613 R m n).
Proof. exact (fun_ext (fun m' : nat => @lem7039340 R m m' n)). Qed.
Lemma lem7039342 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039343 (R : type1605) (m : nat) (n : nat) : (term614 R m n) = (term614 R m n).
Proof. exact (MK_COMB (@lem7039342) (@lem7039341 R m n)). Qed.
Lemma lem7039344 (R : type1605) (m : nat) : (term615 R m) = (term615 R m).
Proof. exact (fun_ext (fun n : nat => @lem7039343 R m n)). Qed.
Lemma lem7039345 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039346 (R : type1605) (m : nat) : (term616 R m) = (term616 R m).
Proof. exact (MK_COMB (@lem7039345) (@lem7039344 R m)). Qed.
Lemma lem7039347 (R : type1605) : (term617 R) = (term617 R).
Proof. exact (fun_ext (fun m : nat => @lem7039346 R m)). Qed.
Lemma lem7039348 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7039349 (R : type1605) : (term618 R) = (term618 R).
Proof. exact (MK_COMB (@lem7039348) (@lem7039347 R)). Qed.
Lemma lem7039350 (R : type1605) : (term505 R) = (term618 R).
Proof. exact (TRANS (@lem7039324 R) (@lem7039349 R)). Qed.
Lemma lem7039351 (R : type1605) (h1 : term71 R) : term618 R.
Proof. exact (EQ_MP (@lem7039350 R) (@lem7038838 R h1)). Qed.
Lemma lem7039473 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7039481 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (x : A) : (term517 A s R f g x) = (term517 A s R f g x).
Proof. exact (eq_refl (term517 A s R f g x)). Qed.
Lemma lem7039482 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term518 A s R f g) = (term518 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7039481 A s R f g x)). Qed.
Lemma lem7039483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7039485 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) : (term519 A s R f g) = (term519 A s R f g).
Proof. exact (MK_COMB (@lem7039483 A) (@lem7039482 A s R f g)). Qed.
Lemma lem7039486 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term519 A s R f g.
Proof. exact (EQ_MP (@lem7039485 A s R f g) (@lem7038911 A s R f g h1)). Qed.
Lemma lem7039492 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term525 A R f s g) = (term525 A R f s g).
Proof. exact (eq_refl (term525 A R f s g)). Qed.
Lemma lem7039509 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term557 A R x f g s) = (term619 A R x f g s).
Proof. exact (@lem19490 (term551 A x f g s) (s = (@EMPTY A)) (term544 A R x f g s)). Qed.
Lemma lem7039512 {A : Type'} (s : A -> Prop) : (term559 A s) = (term559 A s).
Proof. exact (eq_refl (term559 A s)). Qed.
Lemma lem7039513 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term561 A R x f g s) = (term620 A R x f g s).
Proof. exact (MK_COMB (@lem7039512 A s) (@lem7039509 A R x f g s)). Qed.
Lemma lem7039520 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term620 A R x f g s) = (term621 A R x f g s).
Proof. exact (@lem19490 (term622 A x f g s) (term558 A s) (term623 A R x f g s)). Qed.
Lemma lem7039521 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term561 A R x f g s) = (term621 A R x f g s).
Proof. exact (TRANS (@lem7039513 A R x f g s) (@lem7039520 A R x f g s)). Qed.
Lemma lem7039522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7039523 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term563 A R x f g s) = (term624 A R x f g s).
Proof. exact (MK_COMB (@lem7039522) (@lem7039521 A R x f g s)). Qed.
Lemma lem7039524 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term565 A x R f s g) = (term625 A x R f s g).
Proof. exact (MK_COMB (@lem7039523 A R x f g s) (@lem7039492 A R f s g)). Qed.
Lemma lem7039531 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term625 A x R f s g) = (term626 A x R f s g).
Proof. exact (@lem19699 (term627 A x f g s) (term628 A R x f g s) (term525 A R f s g)). Qed.
Lemma lem7039532 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term565 A x R f s g) = (term626 A x R f s g).
Proof. exact (TRANS (@lem7039524 A x R f s g) (@lem7039531 A x R f s g)). Qed.
Lemma lem7039533 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term567 A x R f g) = (term629 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7039532 A x R f s g)). Qed.
Lemma lem7039534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7039535 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (g : A -> nat) : (term569 A x R f g) = (term630 A x R f g).
Proof. exact (MK_COMB (@lem7039534 A) (@lem7039533 A x R f g)). Qed.
Lemma lem7039536 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term571 A x R f) = (term631 A x R f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7039535 A x R f g)). Qed.
Lemma lem7039537 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7039538 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) : (term572 A x R f) = (term632 A x R f).
Proof. exact (MK_COMB (@lem7039537 A) (@lem7039536 A x R f)). Qed.
Lemma lem7039539 {A : Type'} (x : type695 A) (R : type1605) : (term573 A x R) = (term633 A x R).
Proof. exact (fun_ext (fun f : A -> nat => @lem7039538 A x R f)). Qed.
Lemma lem7039540 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7039542 {A : Type'} (x : type695 A) (R : type1605) : (term574 A x R) = (term634 A x R).
Proof. exact (MK_COMB (@lem7039540 A) (@lem7039539 A x R)). Qed.
Lemma lem7039543 {A : Type'} (x : type695 A) (R : type1605) (h1 : term574 A x R) : term634 A x R.
Proof. exact (EQ_MP (@lem7039542 A x R) (@lem7039270 A x R h1)). Qed.
Lemma lem7039544 (_93908 : nat) (R : type1605) (h1 : term71 R) : term635 R _93908.
Proof. exact (@lem7039351 R h1 _93908). Qed.
Lemma lem7039545 (R : type1605) (_93908 : nat) : (term635 R _93908) = (term616 R _93908).
Proof. exact (eq_refl (term635 R _93908)). Qed.
Lemma lem7039546 (_93908 : nat) (R : type1605) (h1 : term71 R) : term616 R _93908.
Proof. exact (EQ_MP (@lem7039545 R _93908) (@lem7039544 _93908 R h1)). Qed.
Lemma lem7039547 (_93908 : nat) (_93909 : nat) (R : type1605) (h1 : term71 R) : term636 R _93908 _93909.
Proof. exact (@lem7039546 _93908 R h1 _93909). Qed.
Lemma lem7039548 (R : type1605) (_93908 : nat) (_93909 : nat) : (term636 R _93908 _93909) = (term614 R _93908 _93909).
Proof. exact (eq_refl (term636 R _93908 _93909)). Qed.
Lemma lem7039549 (_93908 : nat) (_93909 : nat) (R : type1605) (h1 : term71 R) : term614 R _93908 _93909.
Proof. exact (EQ_MP (@lem7039548 R _93908 _93909) (@lem7039547 _93908 _93909 R h1)). Qed.
Lemma lem7039550 (_93908 : nat) (_93909 : nat) (_93910 : nat) (R : type1605) (h1 : term71 R) : term637 R _93908 _93909 _93910.
Proof. exact (@lem7039549 _93908 _93909 R h1 _93910). Qed.
Lemma lem7039551 (R : type1605) (_93908 : nat) (_93910 : nat) (_93909 : nat) : (term637 R _93908 _93909 _93910) = (term612 R _93908 _93910 _93909).
Proof. exact (eq_refl (term637 R _93908 _93909 _93910)). Qed.
Lemma lem7039552 (_93908 : nat) (_93910 : nat) (_93909 : nat) (R : type1605) (h1 : term71 R) : term612 R _93908 _93910 _93909.
Proof. exact (EQ_MP (@lem7039551 R _93908 _93910 _93909) (@lem7039550 _93908 _93909 _93910 R h1)). Qed.
Lemma lem7039553 (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) (R : type1605) (h1 : term71 R) : term638 R _93908 _93910 _93909 _93911.
Proof. exact (@lem7039552 _93908 _93910 _93909 R h1 _93911). Qed.
Lemma lem7039554 (R : type1605) (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) : (term638 R _93908 _93910 _93909 _93911) = (term609 R _93908 _93910 _93909 _93911).
Proof. exact (eq_refl (term638 R _93908 _93910 _93909 _93911)). Qed.
Lemma lem7039571 {A : Type'} (_93917 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term639 A s R f g _93917.
Proof. exact (@lem7039486 A s R f g h1 _93917). Qed.
Lemma lem7039572 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) : (term639 A s R f g _93917) = (term517 A s R f g _93917).
Proof. exact (eq_refl (term639 A s R f g _93917)). Qed.
Lemma lem7039574 {A : Type'} (_93918 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term640 A x R _93918.
Proof. exact (@lem7039543 A x R h1 _93918). Qed.
Lemma lem7039575 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) : (term640 A x R _93918) = (term632 A x R _93918).
Proof. exact (eq_refl (term640 A x R _93918)). Qed.
Lemma lem7039576 {A : Type'} (_93918 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term632 A x R _93918.
Proof. exact (EQ_MP (@lem7039575 A x R _93918) (@lem7039574 A _93918 x R h1)). Qed.
Lemma lem7039577 {A : Type'} (_93918 : A -> nat) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term641 A x R _93918 _93919.
Proof. exact (@lem7039576 A _93918 x R h1 _93919). Qed.
Lemma lem7039578 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) : (term641 A x R _93918 _93919) = (term630 A x R _93918 _93919).
Proof. exact (eq_refl (term641 A x R _93918 _93919)). Qed.
Lemma lem7039579 {A : Type'} (_93918 : A -> nat) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term630 A x R _93918 _93919.
Proof. exact (EQ_MP (@lem7039578 A x R _93918 _93919) (@lem7039577 A _93918 _93919 x R h1)). Qed.
Lemma lem7039580 {A : Type'} (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term642 A x R _93918 _93919 _93920.
Proof. exact (@lem7039579 A _93918 _93919 x R h1 _93920). Qed.
Lemma lem7039581 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term642 A x R _93918 _93919 _93920) = (term626 A x R _93918 _93920 _93919).
Proof. exact (eq_refl (term642 A x R _93918 _93919 _93920)). Qed.
Lemma lem7039582 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term626 A x R _93918 _93920 _93919.
Proof. exact (EQ_MP (@lem7039581 A x R _93918 _93920 _93919) (@lem7039580 A _93918 _93919 _93920 x R h1)). Qed.
Lemma lem7039583 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term643 A x R _93918 _93920 _93919.
Proof. exact (proj2 (@lem7039582 A _93918 _93920 _93919 x R h1)). Qed.
Lemma lem7039584 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term644 A x R _93918 _93920 _93919.
Proof. exact (proj1 (@lem7039582 A _93918 _93920 _93919 x R h1)). Qed.
Lemma lem7039594 (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) (R : type1605) (h1 : term71 R) : term609 R _93908 _93910 _93909 _93911.
Proof. exact (EQ_MP (@lem7039554 R _93908 _93910 _93909 _93911) (@lem7039553 _93908 _93910 _93909 _93911 R h1)). Qed.
Lemma lem7039608 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term576 R x1 y1 x2 y2.
Proof. exact (proj2 (@lem7039269 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039626 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7039632 {A : Type'} (_93917 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term517 A s R f g _93917.
Proof. exact (EQ_MP (@lem7039572 A s R f g _93917) (@lem7039571 A _93917 s R f g h1)). Qed.
Lemma lem7039634 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term191 A R f s g) : term526 A R f s g.
Proof. exact (EQ_MP (@lem7038962 A R f s g) (@lem7038727 A R f s g h1)). Qed.
Lemma lem7039638 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term644 A x R _93918 _93920 _93919) = (term645 A x R _93918 _93920 _93919).
Proof. exact (@lem7036612 (term558 A _93920) (term622 A x _93918 _93919 _93920) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7039645 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term646 A x R _93918 _93920 _93919) = (term647 A x R _93918 _93920 _93919).
Proof. exact (@lem7036612 (_93920 = (@EMPTY A)) (term551 A x _93918 _93919 _93920) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7039646 {A : Type'} (_93920 : A -> Prop) : (term559 A _93920) = (term559 A _93920).
Proof. exact (eq_refl (term559 A _93920)). Qed.
Lemma lem7039649 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term645 A x R _93918 _93920 _93919) = (term648 A x R _93918 _93920 _93919).
Proof. exact (MK_COMB (@lem7039646 A _93920) (@lem7039645 A x R _93918 _93920 _93919)). Qed.
Lemma lem7039651 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term644 A x R _93918 _93920 _93919) = (term648 A x R _93918 _93920 _93919).
Proof. exact (TRANS (@lem7039638 A x R _93918 _93920 _93919) (@lem7039649 A x R _93918 _93920 _93919)). Qed.
Lemma lem7039652 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term648 A x R _93918 _93920 _93919.
Proof. exact (EQ_MP (@lem7039651 A x R _93918 _93920 _93919) (@lem7039584 A _93918 _93920 _93919 x R h1)). Qed.
Lemma lem7039656 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term643 A x R _93918 _93920 _93919) = (term649 A x R _93918 _93920 _93919).
Proof. exact (@lem7036612 (term558 A _93920) (term623 A R x _93918 _93919 _93920) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7039663 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term650 A x R _93918 _93920 _93919) = (term651 A x R _93918 _93920 _93919).
Proof. exact (@lem7036612 (_93920 = (@EMPTY A)) (term544 A R x _93918 _93919 _93920) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7039664 {A : Type'} (_93920 : A -> Prop) : (term559 A _93920) = (term559 A _93920).
Proof. exact (eq_refl (term559 A _93920)). Qed.
Lemma lem7039667 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term649 A x R _93918 _93920 _93919) = (term652 A x R _93918 _93920 _93919).
Proof. exact (MK_COMB (@lem7039664 A _93920) (@lem7039663 A x R _93918 _93920 _93919)). Qed.
Lemma lem7039669 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term643 A x R _93918 _93920 _93919) = (term652 A x R _93918 _93920 _93919).
Proof. exact (TRANS (@lem7039656 A x R _93918 _93920 _93919) (@lem7039667 A x R _93918 _93920 _93919)). Qed.
Lemma lem7039670 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term652 A x R _93918 _93920 _93919.
Proof. exact (EQ_MP (@lem7039669 A x R _93918 _93920 _93919) (@lem7039583 A _93918 _93920 _93919 x R h1)). Qed.
Lemma lem7039839 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term492 R x1 x2.
Proof. exact (proj1 (@lem7039272 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039840 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term653 R x1 x2.
Proof. exact (fun h0 : term494 R x1 x2 => @lem7039839 R x1 y1 x2 y2 h1). Qed.
Lemma lem7039842 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7039843 (R : type1605) (x1 : nat) (x2 : nat) : (term653 R x1 x2) = (term492 R x1 x2).
Proof. exact (@lem7039842 (term492 R x1 x2)). Qed.
Lemma lem7039844 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term492 R x1 x2.
Proof. exact (EQ_MP (@lem7039843 R x1 x2) (@lem7039840 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039846 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term492 R y1 y2.
Proof. exact (proj2 (@lem7039272 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039847 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term653 R y1 y2.
Proof. exact (fun h0 : term494 R y1 y2 => @lem7039846 R x1 y1 x2 y2 h1). Qed.
Lemma lem7039849 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7039850 (R : type1605) (y1 : nat) (y2 : nat) : (term653 R y1 y2) = (term492 R y1 y2).
Proof. exact (@lem7039849 (term492 R y1 y2)). Qed.
Lemma lem7039851 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term492 R y1 y2.
Proof. exact (EQ_MP (@lem7039850 R y1 y2) (@lem7039847 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039867 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7039868 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term496 R _93908 _93910 _93909 _93911) = (term655 _93908 _93909 R _93910 _93911).
Proof. exact (@lem7039867 (term491 R _93908 _93910 _93909 _93911) (term494 R _93910 _93911)). Qed.
Lemma lem7039874 (R : type1605) (_93908 : nat) (_93909 : nat) : (term495 R _93908 _93909) = (term495 R _93908 _93909).
Proof. exact (eq_refl (term495 R _93908 _93909)). Qed.
Lemma lem7039875 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term609 R _93908 _93910 _93909 _93911) = (term656 _93908 _93909 R _93910 _93911).
Proof. exact (MK_COMB (@lem7039874 R _93908 _93909) (@lem7039868 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039879 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7039880 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term656 _93908 _93909 R _93910 _93911) = (term657 _93908 _93909 R _93910 _93911).
Proof. exact (@lem7039879 (term491 R _93908 _93910 _93909 _93911) (term494 R _93908 _93909) (term494 R _93910 _93911)). Qed.
Lemma lem7039896 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term609 R _93908 _93910 _93909 _93911) = (term657 _93908 _93909 R _93910 _93911).
Proof. exact (TRANS (@lem7039875 _93908 _93909 R _93910 _93911) (@lem7039880 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7039898 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term658 R _93908 _93910 _93909 _93911) = (term659 _93908 _93909 R _93910 _93911).
Proof. exact (MK_COMB (@lem7039897) (@lem7039896 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039914 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term657 _93908 _93909 R _93910 _93911) = (term657 _93908 _93909 R _93910 _93911).
Proof. exact (eq_refl (term657 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039915 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : ((term609 R _93908 _93910 _93909 _93911) = (term657 _93908 _93909 R _93910 _93911)) = ((term657 _93908 _93909 R _93910 _93911) = (term657 _93908 _93909 R _93910 _93911)).
Proof. exact (MK_COMB (@lem7039898 _93908 _93909 R _93910 _93911) (@lem7039914 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039917 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7039918 (x : Prop) : (x = x) = True.
Proof. exact (@lem7039917 Prop x). Qed.
Lemma lem7039919 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : ((term657 _93908 _93909 R _93910 _93911) = (term657 _93908 _93909 R _93910 _93911)) = True.
Proof. exact (@lem7039918 (term657 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039920 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : ((term609 R _93908 _93910 _93909 _93911) = (term657 _93908 _93909 R _93910 _93911)) = True.
Proof. exact (TRANS (@lem7039915 _93908 _93909 R _93910 _93911) (@lem7039919 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039921 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : True = ((term609 R _93908 _93910 _93909 _93911) = (term657 _93908 _93909 R _93910 _93911)).
Proof. exact (SYM (@lem7039920 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039922 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term609 R _93908 _93910 _93909 _93911) = (term657 _93908 _93909 R _93910 _93911).
Proof. exact (EQ_MP (@lem7039921 _93908 _93909 R _93910 _93911) (@lem0)). Qed.
Lemma lem7039923 (_93908 : nat) (_93909 : nat) (_93910 : nat) (_93911 : nat) (R : type1605) (h1 : term71 R) : term657 _93908 _93909 R _93910 _93911.
Proof. exact (EQ_MP (@lem7039922 _93908 _93909 R _93910 _93911) (@lem7039594 _93908 _93910 _93909 _93911 R h1)). Qed.
Lemma lem7039925 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7039926 (R : type1605) (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) : (term657 _93908 _93909 R _93910 _93911) = (term661 R _93908 _93910 _93909 _93911).
Proof. exact (@lem7039925 (term662 _93908 _93909 R _93910 _93911) (term491 R _93908 _93910 _93909 _93911)). Qed.
Lemma lem7039928 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7039929 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term665 _93908 _93909 R _93910 _93911) = (term666 _93908 _93909 R _93910 _93911).
Proof. exact (@lem7039928 (term494 R _93908 _93909) (term494 R _93910 _93911)). Qed.
Lemma lem7039931 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7039932 (R : type1605) (_93908 : nat) (_93909 : nat) : (term667 R _93908 _93909) = (term492 R _93908 _93909).
Proof. exact (@lem7039931 (term492 R _93908 _93909)). Qed.
Lemma lem7039933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7039934 (R : type1605) (_93908 : nat) (_93909 : nat) : (term668 R _93908 _93909) = (term578 R _93908 _93909).
Proof. exact (MK_COMB (@lem7039933) (@lem7039932 R _93908 _93909)). Qed.
Lemma lem7039936 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7039937 (R : type1605) (_93910 : nat) (_93911 : nat) : (term667 R _93910 _93911) = (term492 R _93910 _93911).
Proof. exact (@lem7039936 (term492 R _93910 _93911)). Qed.
Lemma lem7039938 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term666 _93908 _93909 R _93910 _93911) = (term579 _93908 _93909 R _93910 _93911).
Proof. exact (MK_COMB (@lem7039934 R _93908 _93909) (@lem7039937 R _93910 _93911)). Qed.
Lemma lem7039939 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term665 _93908 _93909 R _93910 _93911) = (term579 _93908 _93909 R _93910 _93911).
Proof. exact (TRANS (@lem7039929 _93908 _93909 R _93910 _93911) (@lem7039938 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039940 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7039941 (_93908 : nat) (_93909 : nat) (R : type1605) (_93910 : nat) (_93911 : nat) : (term669 _93908 _93909 R _93910 _93911) = (term670 _93908 _93909 R _93910 _93911).
Proof. exact (MK_COMB (@lem7039940) (@lem7039939 _93908 _93909 R _93910 _93911)). Qed.
Lemma lem7039942 (R : type1605) (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) : (term491 R _93908 _93910 _93909 _93911) = (term491 R _93908 _93910 _93909 _93911).
Proof. exact (eq_refl (term491 R _93908 _93910 _93909 _93911)). Qed.
Lemma lem7039943 (R : type1605) (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) : (term661 R _93908 _93910 _93909 _93911) = (term671 R _93908 _93910 _93909 _93911).
Proof. exact (MK_COMB (@lem7039941 _93908 _93909 R _93910 _93911) (@lem7039942 R _93908 _93910 _93909 _93911)). Qed.
Lemma lem7039944 (R : type1605) (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) : (term657 _93908 _93909 R _93910 _93911) = (term671 R _93908 _93910 _93909 _93911).
Proof. exact (TRANS (@lem7039926 R _93908 _93910 _93909 _93911) (@lem7039943 R _93908 _93910 _93909 _93911)). Qed.
Lemma lem7039946 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term579 x1 x2 R y1 y2.
Proof. exact (conj (@lem7039844 R x1 y1 x2 y2 h1) (@lem7039851 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039948 (_93908 : nat) (_93910 : nat) (_93909 : nat) (_93911 : nat) (R : type1605) (h1 : term71 R) : term671 R _93908 _93910 _93909 _93911.
Proof. exact (EQ_MP (@lem7039944 R _93908 _93910 _93909 _93911) (@lem7039923 _93908 _93909 _93910 _93911 R h1)). Qed.
Lemma lem7039949 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) (h1 : term71 R) : term671 R x1 y1 x2 y2.
Proof. exact (@lem7039948 x1 y1 x2 y2 R h1). Qed.
Lemma lem7039952 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term491 R x1 y1 x2 y2.
Proof. exact (@lem7039949 x1 y1 x2 y2 R h1 (@lem7039946 R x1 y1 x2 y2 h2)). Qed.
Lemma lem7039953 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term672 R x1 y1 x2 y2.
Proof. exact (fun h0 : term576 R x1 y1 x2 y2 => @lem7039952 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7039955 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7039956 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term672 R x1 y1 x2 y2) = (term491 R x1 y1 x2 y2).
Proof. exact (@lem7039955 (term491 R x1 y1 x2 y2)). Qed.
Lemma lem7039957 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term491 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7039956 R x1 y1 x2 y2) (@lem7039953 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7039960 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7039962 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term576 R x1 y1 x2 y2) = (term673 R x1 y1 x2 y2).
Proof. exact (@lem7039960 (term491 R x1 y1 x2 y2)). Qed.
Lemma lem7039965 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term582 R x1 y1 x2 y2) : term673 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7039962 R x1 y1 x2 y2) (@lem7039608 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7039968 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : False.
Proof. exact (@lem7039965 R x1 y1 x2 y2 h2 (@lem7039957 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7039969 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : term674.
Proof. exact (fun h0 : ~ False => @lem7039968 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7039971 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7039972 : term674 = False.
Proof. exact (@lem7039971 False). Qed.
Lemma lem7039973 (R : type1605) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : term71 R) (h2 : term582 R x1 y1 x2 y2) : False.
Proof. exact (EQ_MP (@lem7039972) (@lem7039969 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7040193 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7038846 A s) (@lem7038652 A s h1)). Qed.
Lemma lem7040194 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term675 A s.
Proof. exact (fun h0 : term558 A s => @lem7040193 A s h1). Qed.
Lemma lem7040196 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7040197 {A : Type'} (s : A -> Prop) : (term675 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7040196 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7040198 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7040197 A s) (@lem7040194 A s h1)). Qed.
Lemma lem7040200 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7040201 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term676 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem7040200 A s h1). Qed.
Lemma lem7040203 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7040204 {A : Type'} (s : A -> Prop) : (term676 A s) = (term79 A s).
Proof. exact (@lem7040203 (s = (@EMPTY A))). Qed.
Lemma lem7040205 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (EQ_MP (@lem7040204 A s) (@lem7040201 A s h1)). Qed.
Lemma lem7040207 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7038846 A s) (@lem7038652 A s h1)). Qed.
Lemma lem7040208 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term675 A s.
Proof. exact (fun h0 : term558 A s => @lem7040207 A s h1). Qed.
Lemma lem7040210 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7040211 {A : Type'} (s : A -> Prop) : (term675 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7040210 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7040212 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7040211 A s) (@lem7040208 A s h1)). Qed.
Lemma lem7040214 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (h1). Qed.
Lemma lem7040215 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term676 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem7040214 A s h1). Qed.
Lemma lem7040217 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7040218 {A : Type'} (s : A -> Prop) : (term676 A s) = (term79 A s).
Proof. exact (@lem7040217 (s = (@EMPTY A))). Qed.
Lemma lem7040219 {A : Type'} (s : A -> Prop) (h1 : term79 A s) : term79 A s.
Proof. exact (EQ_MP (@lem7040218 A s) (@lem7040215 A s h1)). Qed.
Lemma lem7040222 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term526 A R f s g) : term526 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7040223 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term526 A R f s g) : term678 A R f s g.
Proof. exact (fun h0 : term525 A R f s g => @lem7040222 A R f s g h1). Qed.
Lemma lem7040225 (p : Prop) : (term677 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7040226 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term678 A R f s g) = (term526 A R f s g).
Proof. exact (@lem7040225 (term525 A R f s g)). Qed.
Lemma lem7040227 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term526 A R f s g) : term526 A R f s g.
Proof. exact (EQ_MP (@lem7040226 A R f s g) (@lem7040223 A R f s g h1)). Qed.
Lemma lem7040233 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040234 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term648 A x R _93918 _93920 _93919) = (term679 A x R _93918 _93920 _93919).
Proof. exact (@lem7040233 (_93920 = (@EMPTY A)) (term558 A _93920) (term680 A x R _93918 _93920 _93919)). Qed.
Lemma lem7040250 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040251 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term681 A x R _93918 _93920 _93919) = (term682 A x R _93918 _93920 _93919).
Proof. exact (@lem7040250 (term551 A x _93918 _93919 _93920) (term558 A _93920) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7040265 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7040266 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term683 A R _93918 _93920 _93919) = (term684 A R _93918 _93919 _93920).
Proof. exact (@lem7040265 (term525 A R _93918 _93920 _93919) (term558 A _93920)). Qed.
Lemma lem7040272 {A : Type'} (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term685 A x _93918 _93919 _93920) = (term685 A x _93918 _93919 _93920).
Proof. exact (eq_refl (term685 A x _93918 _93919 _93920)). Qed.
Lemma lem7040273 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term682 A x R _93918 _93920 _93919) = (term686 A x R _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040272 A x _93918 _93919 _93920) (@lem7040266 A R _93918 _93919 _93920)). Qed.
Lemma lem7040284 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term681 A x R _93918 _93920 _93919) = (term686 A x R _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040251 A x R _93918 _93920 _93919) (@lem7040273 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040285 {A : Type'} (_93920 : A -> Prop) : (term251 A _93920) = (term251 A _93920).
Proof. exact (eq_refl (term251 A _93920)). Qed.
Lemma lem7040286 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term679 A x R _93918 _93920 _93919) = (term687 A x R _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040285 A _93920) (@lem7040284 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040297 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term648 A x R _93918 _93920 _93919) = (term687 A x R _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040234 A x R _93918 _93920 _93919) (@lem7040286 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7040299 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term688 A x R _93918 _93920 _93919) = (term689 A x R _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040298) (@lem7040297 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040313 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040314 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term690 A R _93918 _93920 _93919) = (term691 A R _93918 _93920 _93919).
Proof. exact (@lem7040313 (_93920 = (@EMPTY A)) (term558 A _93920) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7040330 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7040331 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term683 A R _93918 _93920 _93919) = (term684 A R _93918 _93919 _93920).
Proof. exact (@lem7040330 (term525 A R _93918 _93920 _93919) (term558 A _93920)). Qed.
Lemma lem7040337 {A : Type'} (_93920 : A -> Prop) : (term251 A _93920) = (term251 A _93920).
Proof. exact (eq_refl (term251 A _93920)). Qed.
Lemma lem7040338 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term691 A R _93918 _93920 _93919) = (term692 A R _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040337 A _93920) (@lem7040331 A R _93918 _93919 _93920)). Qed.
Lemma lem7040349 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term690 A R _93918 _93920 _93919) = (term692 A R _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040314 A R _93918 _93920 _93919) (@lem7040338 A R _93918 _93919 _93920)). Qed.
Lemma lem7040350 {A : Type'} (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term685 A x _93918 _93919 _93920) = (term685 A x _93918 _93919 _93920).
Proof. exact (eq_refl (term685 A x _93918 _93919 _93920)). Qed.
Lemma lem7040351 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term693 A x R _93918 _93920 _93919) = (term694 A x R _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040350 A x _93918 _93919 _93920) (@lem7040349 A R _93918 _93919 _93920)). Qed.
Lemma lem7040355 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040356 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term694 A x R _93918 _93919 _93920) = (term687 A x R _93918 _93919 _93920).
Proof. exact (@lem7040355 (_93920 = (@EMPTY A)) (term551 A x _93918 _93919 _93920) (term684 A R _93918 _93919 _93920)). Qed.
Lemma lem7040384 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term693 A x R _93918 _93920 _93919) = (term687 A x R _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040351 A x R _93918 _93919 _93920) (@lem7040356 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040385 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : ((term648 A x R _93918 _93920 _93919) = (term693 A x R _93918 _93920 _93919)) = ((term687 A x R _93918 _93919 _93920) = (term687 A x R _93918 _93919 _93920)).
Proof. exact (MK_COMB (@lem7040299 A x R _93918 _93919 _93920) (@lem7040384 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040387 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7040388 (x : Prop) : (x = x) = True.
Proof. exact (@lem7040387 Prop x). Qed.
Lemma lem7040389 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : ((term687 A x R _93918 _93919 _93920) = (term687 A x R _93918 _93919 _93920)) = True.
Proof. exact (@lem7040388 (term687 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040390 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : ((term648 A x R _93918 _93920 _93919) = (term693 A x R _93918 _93920 _93919)) = True.
Proof. exact (TRANS (@lem7040385 A x R _93918 _93919 _93920) (@lem7040389 A x R _93918 _93919 _93920)). Qed.
Lemma lem7040391 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : True = ((term648 A x R _93918 _93920 _93919) = (term693 A x R _93918 _93920 _93919)).
Proof. exact (SYM (@lem7040390 A x R _93918 _93920 _93919)). Qed.
Lemma lem7040392 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term648 A x R _93918 _93920 _93919) = (term693 A x R _93918 _93920 _93919).
Proof. exact (EQ_MP (@lem7040391 A x R _93918 _93920 _93919) (@lem0)). Qed.
Lemma lem7040393 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term693 A x R _93918 _93920 _93919.
Proof. exact (EQ_MP (@lem7040392 A x R _93918 _93920 _93919) (@lem7039652 A _93918 _93920 _93919 x R h1)). Qed.
Lemma lem7040395 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7040396 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term693 A x R _93918 _93920 _93919) = (term695 A R x _93918 _93919 _93920).
Proof. exact (@lem7040395 (term690 A R _93918 _93920 _93919) (term551 A x _93918 _93919 _93920)). Qed.
Lemma lem7040398 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7040399 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term696 A R _93918 _93920 _93919) = (term697 A R _93918 _93920 _93919).
Proof. exact (@lem7040398 (term558 A _93920) (term698 A R _93918 _93920 _93919)). Qed.
Lemma lem7040401 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7040402 {A : Type'} (_93920 : A -> Prop) : (term699 A _93920) = (@I ((A -> Prop) -> Prop) (@FINITE A) _93920).
Proof. exact (@lem7040401 (@I ((A -> Prop) -> Prop) (@FINITE A) _93920)). Qed.
Lemma lem7040403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7040404 {A : Type'} (_93920 : A -> Prop) : (term700 A _93920) = (term701 A _93920).
Proof. exact (MK_COMB (@lem7040403) (@lem7040402 A _93920)). Qed.
Lemma lem7040406 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7040407 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term702 A R _93918 _93920 _93919) = (term703 A R _93918 _93920 _93919).
Proof. exact (@lem7040406 (_93920 = (@EMPTY A)) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7040408 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term697 A R _93918 _93920 _93919) = (term704 A R _93918 _93920 _93919).
Proof. exact (MK_COMB (@lem7040404 A _93920) (@lem7040407 A R _93918 _93920 _93919)). Qed.
Lemma lem7040409 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term696 A R _93918 _93920 _93919) = (term704 A R _93918 _93920 _93919).
Proof. exact (TRANS (@lem7040399 A R _93918 _93920 _93919) (@lem7040408 A R _93918 _93920 _93919)). Qed.
Lemma lem7040410 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7040411 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term705 A R _93918 _93920 _93919) = (term706 A R _93918 _93920 _93919).
Proof. exact (MK_COMB (@lem7040410) (@lem7040409 A R _93918 _93920 _93919)). Qed.
Lemma lem7040412 {A : Type'} (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term551 A x _93918 _93919 _93920) = (term551 A x _93918 _93919 _93920).
Proof. exact (eq_refl (term551 A x _93918 _93919 _93920)). Qed.
Lemma lem7040413 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term695 A R x _93918 _93919 _93920) = (term707 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040411 A R _93918 _93920 _93919) (@lem7040412 A x _93918 _93919 _93920)). Qed.
Lemma lem7040414 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term693 A x R _93918 _93920 _93919) = (term707 A R x _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040396 A R x _93918 _93919 _93920) (@lem7040413 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040416 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term79 A s) (h2 : term526 A R f s g) : term703 A R f s g.
Proof. exact (conj (@lem7040219 A s h1) (@lem7040227 A R f s g h2)). Qed.
Lemma lem7040417 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : @FINITE A s) (h2 : term79 A s) (h3 : term526 A R f s g) : term704 A R f s g.
Proof. exact (conj (@lem7040212 A s h1) (@lem7040416 A R f s g h2 h3)). Qed.
Lemma lem7040419 {A : Type'} (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term707 A R x _93918 _93919 _93920.
Proof. exact (EQ_MP (@lem7040414 A R x _93918 _93919 _93920) (@lem7040393 A _93918 _93920 _93919 x R h1)). Qed.
Lemma lem7040420 {A : Type'} (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term707 A R x _93918 _93919 _93920.
Proof. exact (@lem7040419 A _93918 _93919 _93920 x R h1). Qed.
Lemma lem7040421 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term707 A R x f g s.
Proof. exact (@lem7040420 A f g s x R h1). Qed.
Lemma lem7040424 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term574 A x R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term526 A R f s g) : term551 A x f g s.
Proof. exact (@lem7040421 A f g s x R h1 (@lem7040417 A R f s g h2 h3 h4)). Qed.
Lemma lem7040425 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term574 A x R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term526 A R f s g) : term708 A x f g s.
Proof. exact (fun h0 : term709 A x f g s => @lem7040424 A x R f s g h1 h2 h3 h4). Qed.
Lemma lem7040427 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7040428 {A : Type'} (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term708 A x f g s) = (term551 A x f g s).
Proof. exact (@lem7040427 (term551 A x f g s)). Qed.
Lemma lem7040429 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term574 A x R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term526 A R f s g) : term551 A x f g s.
Proof. exact (EQ_MP (@lem7040428 A x f g s) (@lem7040425 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7040435 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7040436 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : (term517 A s R f g _93917) = (term710 A R f g _93917 s).
Proof. exact (@lem7040435 (term511 A R f g _93917) (term514 A _93917 s)). Qed.
Lemma lem7040442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7040443 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : (term711 A s R f g _93917) = (term712 A R f g _93917 s).
Proof. exact (MK_COMB (@lem7040442) (@lem7040436 A R f g _93917 s)). Qed.
Lemma lem7040449 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : (term710 A R f g _93917 s) = (term710 A R f g _93917 s).
Proof. exact (eq_refl (term710 A R f g _93917 s)). Qed.
Lemma lem7040450 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : ((term517 A s R f g _93917) = (term710 A R f g _93917 s)) = ((term710 A R f g _93917 s) = (term710 A R f g _93917 s)).
Proof. exact (MK_COMB (@lem7040443 A R f g _93917 s) (@lem7040449 A R f g _93917 s)). Qed.
Lemma lem7040452 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7040453 (x : Prop) : (x = x) = True.
Proof. exact (@lem7040452 Prop x). Qed.
Lemma lem7040454 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : ((term710 A R f g _93917 s) = (term710 A R f g _93917 s)) = True.
Proof. exact (@lem7040453 (term710 A R f g _93917 s)). Qed.
Lemma lem7040455 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : ((term517 A s R f g _93917) = (term710 A R f g _93917 s)) = True.
Proof. exact (TRANS (@lem7040450 A R f g _93917 s) (@lem7040454 A R f g _93917 s)). Qed.
Lemma lem7040456 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : True = ((term517 A s R f g _93917) = (term710 A R f g _93917 s)).
Proof. exact (SYM (@lem7040455 A R f g _93917 s)). Qed.
Lemma lem7040457 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) (s : A -> Prop) : (term517 A s R f g _93917) = (term710 A R f g _93917 s).
Proof. exact (EQ_MP (@lem7040456 A R f g _93917 s) (@lem0)). Qed.
Lemma lem7040458 {A : Type'} (_93917 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term710 A R f g _93917 s.
Proof. exact (EQ_MP (@lem7040457 A R f g _93917 s) (@lem7039632 A _93917 s R f g h1)). Qed.
Lemma lem7040460 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7040461 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) : (term710 A R f g _93917 s) = (term713 A s R f g _93917).
Proof. exact (@lem7040460 (term514 A _93917 s) (term511 A R f g _93917)). Qed.
Lemma lem7040463 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7040464 {A : Type'} (_93917 : A) (s : A -> Prop) : (term714 A _93917 s) = (term512 A _93917 s).
Proof. exact (@lem7040463 (term512 A _93917 s)). Qed.
Lemma lem7040465 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7040466 {A : Type'} (_93917 : A) (s : A -> Prop) : (term715 A _93917 s) = (term716 A _93917 s).
Proof. exact (MK_COMB (@lem7040465) (@lem7040464 A _93917 s)). Qed.
Lemma lem7040467 {A : Type'} (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) : (term511 A R f g _93917) = (term511 A R f g _93917).
Proof. exact (eq_refl (term511 A R f g _93917)). Qed.
Lemma lem7040468 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) : (term713 A s R f g _93917) = (term717 A s R f g _93917).
Proof. exact (MK_COMB (@lem7040466 A _93917 s) (@lem7040467 A R f g _93917)). Qed.
Lemma lem7040469 {A : Type'} (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (_93917 : A) : (term710 A R f g _93917 s) = (term717 A s R f g _93917).
Proof. exact (TRANS (@lem7040461 A s R f g _93917) (@lem7040468 A s R f g _93917)). Qed.
Lemma lem7040472 {A : Type'} (_93917 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term717 A s R f g _93917.
Proof. exact (EQ_MP (@lem7040469 A s R f g _93917) (@lem7040458 A _93917 s R f g h1)). Qed.
Lemma lem7040473 {A : Type'} (_93917 : A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term717 A s R f g _93917.
Proof. exact (@lem7040472 A _93917 s R f g h1). Qed.
Lemma lem7040474 {A : Type'} (x : type695 A) (s : A -> Prop) (R : type1605) (f : A -> nat) (g : A -> nat) (h1 : term80 A s R f g) : term718 A R x f g s.
Proof. exact (@lem7040473 A (term529 A x f g s) s R f g h1). Qed.
Lemma lem7040477 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term542 A R x f g s.
Proof. exact (@lem7040474 A x s R f g h1 (@lem7040429 A x R f s g h2 h3 h4 h5)). Qed.
Lemma lem7040478 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term719 A R x f g s.
Proof. exact (fun h0 : term544 A R x f g s => @lem7040477 A x R f s g h1 h2 h3 h4 h5). Qed.
Lemma lem7040480 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7040481 {A : Type'} (R : type1605) (x : type695 A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term719 A R x f g s) = (term542 A R x f g s).
Proof. exact (@lem7040480 (term542 A R x f g s)). Qed.
Lemma lem7040482 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term542 A R x f g s.
Proof. exact (EQ_MP (@lem7040481 A R x f g s) (@lem7040478 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7040488 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040489 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term652 A x R _93918 _93920 _93919) = (term720 A x R _93918 _93920 _93919).
Proof. exact (@lem7040488 (_93920 = (@EMPTY A)) (term558 A _93920) (term721 A x R _93918 _93920 _93919)). Qed.
Lemma lem7040515 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7040516 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term721 A x R _93918 _93920 _93919) = (term722 A R x _93918 _93919 _93920).
Proof. exact (@lem7040515 (term525 A R _93918 _93920 _93919) (term544 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040522 {A : Type'} (_93920 : A -> Prop) : (term559 A _93920) = (term559 A _93920).
Proof. exact (eq_refl (term559 A _93920)). Qed.
Lemma lem7040523 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term723 A x R _93918 _93920 _93919) = (term724 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040522 A _93920) (@lem7040516 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040527 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040528 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term724 A R x _93918 _93919 _93920) = (term725 A R x _93918 _93919 _93920).
Proof. exact (@lem7040527 (term525 A R _93918 _93920 _93919) (term558 A _93920) (term544 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040544 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term723 A x R _93918 _93920 _93919) = (term725 A R x _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040523 A R x _93918 _93919 _93920) (@lem7040528 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040545 {A : Type'} (_93920 : A -> Prop) : (term251 A _93920) = (term251 A _93920).
Proof. exact (eq_refl (term251 A _93920)). Qed.
Lemma lem7040546 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term720 A x R _93918 _93920 _93919) = (term726 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040545 A _93920) (@lem7040544 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040557 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term652 A x R _93918 _93920 _93919) = (term726 A R x _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040489 A x R _93918 _93920 _93919) (@lem7040546 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7040559 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term727 A x R _93918 _93920 _93919) = (term728 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040558) (@lem7040557 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040573 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040574 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term628 A R x _93918 _93919 _93920) = (term729 A R x _93918 _93919 _93920).
Proof. exact (@lem7040573 (_93920 = (@EMPTY A)) (term558 A _93920) (term544 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040592 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term730 A R _93918 _93920 _93919) = (term730 A R _93918 _93920 _93919).
Proof. exact (eq_refl (term730 A R _93918 _93920 _93919)). Qed.
Lemma lem7040593 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term731 A R x _93918 _93919 _93920) = (term732 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040592 A R _93918 _93920 _93919) (@lem7040574 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040597 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7040598 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term732 A R x _93918 _93919 _93920) = (term726 A R x _93918 _93919 _93920).
Proof. exact (@lem7040597 (_93920 = (@EMPTY A)) (term525 A R _93918 _93920 _93919) (term733 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040626 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term731 A R x _93918 _93919 _93920) = (term726 A R x _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040593 A R x _93918 _93919 _93920) (@lem7040598 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040627 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : ((term652 A x R _93918 _93920 _93919) = (term731 A R x _93918 _93919 _93920)) = ((term726 A R x _93918 _93919 _93920) = (term726 A R x _93918 _93919 _93920)).
Proof. exact (MK_COMB (@lem7040559 A R x _93918 _93919 _93920) (@lem7040626 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040629 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7040630 (x : Prop) : (x = x) = True.
Proof. exact (@lem7040629 Prop x). Qed.
Lemma lem7040631 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : ((term726 A R x _93918 _93919 _93920) = (term726 A R x _93918 _93919 _93920)) = True.
Proof. exact (@lem7040630 (term726 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040632 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : ((term652 A x R _93918 _93920 _93919) = (term731 A R x _93918 _93919 _93920)) = True.
Proof. exact (TRANS (@lem7040627 A R x _93918 _93919 _93920) (@lem7040631 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040633 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : True = ((term652 A x R _93918 _93920 _93919) = (term731 A R x _93918 _93919 _93920)).
Proof. exact (SYM (@lem7040632 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040634 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term652 A x R _93918 _93920 _93919) = (term731 A R x _93918 _93919 _93920).
Proof. exact (EQ_MP (@lem7040633 A R x _93918 _93919 _93920) (@lem0)). Qed.
Lemma lem7040635 {A : Type'} (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term731 A R x _93918 _93919 _93920.
Proof. exact (EQ_MP (@lem7040634 A R x _93918 _93919 _93920) (@lem7039670 A _93918 _93920 _93919 x R h1)). Qed.
Lemma lem7040637 (b : Prop) (a : Prop) : (a \/ b) = (term660 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7040638 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term731 A R x _93918 _93919 _93920) = (term734 A x R _93918 _93920 _93919).
Proof. exact (@lem7040637 (term628 A R x _93918 _93919 _93920) (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7040640 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7040641 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term735 A R x _93918 _93919 _93920) = (term736 A R x _93918 _93919 _93920).
Proof. exact (@lem7040640 (term558 A _93920) (term623 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040643 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7040644 {A : Type'} (_93920 : A -> Prop) : (term699 A _93920) = (@I ((A -> Prop) -> Prop) (@FINITE A) _93920).
Proof. exact (@lem7040643 (@I ((A -> Prop) -> Prop) (@FINITE A) _93920)). Qed.
Lemma lem7040645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7040646 {A : Type'} (_93920 : A -> Prop) : (term700 A _93920) = (term701 A _93920).
Proof. exact (MK_COMB (@lem7040645) (@lem7040644 A _93920)). Qed.
Lemma lem7040648 (a : Prop) (b : Prop) : (term663 a b) = (term664 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7040649 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term737 A R x _93918 _93919 _93920) = (term738 A R x _93918 _93919 _93920).
Proof. exact (@lem7040648 (_93920 = (@EMPTY A)) (term544 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040651 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7040652 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term739 A R x _93918 _93919 _93920) = (term542 A R x _93918 _93919 _93920).
Proof. exact (@lem7040651 (term542 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040653 {A : Type'} (_93920 : A -> Prop) : (term182 A _93920) = (term182 A _93920).
Proof. exact (eq_refl (term182 A _93920)). Qed.
Lemma lem7040654 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term738 A R x _93918 _93919 _93920) = (term740 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040653 A _93920) (@lem7040652 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040655 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term737 A R x _93918 _93919 _93920) = (term740 A R x _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040649 A R x _93918 _93919 _93920) (@lem7040654 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040656 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term736 A R x _93918 _93919 _93920) = (term741 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040646 A _93920) (@lem7040655 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040657 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term735 A R x _93918 _93919 _93920) = (term741 A R x _93918 _93919 _93920).
Proof. exact (TRANS (@lem7040641 A R x _93918 _93919 _93920) (@lem7040656 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7040659 {A : Type'} (R : type1605) (x : type695 A) (_93918 : A -> nat) (_93919 : A -> nat) (_93920 : A -> Prop) : (term742 A R x _93918 _93919 _93920) = (term743 A R x _93918 _93919 _93920).
Proof. exact (MK_COMB (@lem7040658) (@lem7040657 A R x _93918 _93919 _93920)). Qed.
Lemma lem7040660 {A : Type'} (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term525 A R _93918 _93920 _93919) = (term525 A R _93918 _93920 _93919).
Proof. exact (eq_refl (term525 A R _93918 _93920 _93919)). Qed.
Lemma lem7040661 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term734 A x R _93918 _93920 _93919) = (term744 A x R _93918 _93920 _93919).
Proof. exact (MK_COMB (@lem7040659 A R x _93918 _93919 _93920) (@lem7040660 A R _93918 _93920 _93919)). Qed.
Lemma lem7040662 {A : Type'} (x : type695 A) (R : type1605) (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) : (term731 A R x _93918 _93919 _93920) = (term744 A x R _93918 _93920 _93919).
Proof. exact (TRANS (@lem7040638 A x R _93918 _93920 _93919) (@lem7040661 A x R _93918 _93920 _93919)). Qed.
Lemma lem7040664 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term740 A R x f g s.
Proof. exact (conj (@lem7040205 A s h4) (@lem7040482 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7040665 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term741 A R x f g s.
Proof. exact (conj (@lem7040198 A s h3) (@lem7040664 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7040667 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term744 A x R _93918 _93920 _93919.
Proof. exact (EQ_MP (@lem7040662 A x R _93918 _93920 _93919) (@lem7040635 A _93918 _93919 _93920 x R h1)). Qed.
Lemma lem7040668 {A : Type'} (_93918 : A -> nat) (_93920 : A -> Prop) (_93919 : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term744 A x R _93918 _93920 _93919.
Proof. exact (@lem7040667 A _93918 _93920 _93919 x R h1). Qed.
Lemma lem7040669 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : type695 A) (R : type1605) (h1 : term574 A x R) : term744 A x R f s g.
Proof. exact (@lem7040668 A f s g x R h1). Qed.
Lemma lem7040672 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term526 A R f s g) : term525 A R f s g.
Proof. exact (@lem7040669 A f s g x R h2 (@lem7040665 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7040673 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type695 A) (R : type1605) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) : term745 A R f s g.
Proof. exact (fun h0 : term526 A R f s g => @lem7040672 A x R f s g h1 h2 h3 h4 h0). Qed.
Lemma lem7040675 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7040676 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term745 A R f s g) = (term525 A R f s g).
Proof. exact (@lem7040675 (term525 A R f s g)). Qed.
Lemma lem7040677 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type695 A) (R : type1605) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) : term525 A R f s g.
Proof. exact (EQ_MP (@lem7040676 A R f s g) (@lem7040673 A f g x R s h1 h2 h3 h4)). Qed.
Lemma lem7040680 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7040682 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term526 A R f s g) = (term746 A R f s g).
Proof. exact (@lem7040680 (term525 A R f s g)). Qed.
Lemma lem7040685 {A : Type'} (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term191 A R f s g) : term746 A R f s g.
Proof. exact (EQ_MP (@lem7040682 A R f s g) (@lem7039634 A R f s g h1)). Qed.
Lemma lem7040688 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (@lem7040685 A R f s g h5 (@lem7040677 A f g x R s h1 h2 h3 h4)). Qed.
Lemma lem7040689 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : term674.
Proof. exact (fun h0 : ~ False => @lem7040688 A x R f s g h1 h2 h3 h4 h5). Qed.
Lemma lem7040691 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7040692 : term674 = False.
Proof. exact (@lem7040691 False). Qed.
Lemma lem7040693 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7040692) (@lem7040689 A x R f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7040694 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : (term79 A s) = False.
Proof. exact (prop_ext (fun h6 : term79 A s => @lem7040693 A x R f s g h1 h2 h3 h4 h5) (fun h6 : False => @lem7039626 A s h4)). Qed.
Lemma lem7040695 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7040694 A x R f s g h1 h2 h3 h4 h5) (@lem7039626 A s h4)). Qed.
Lemma lem7040696 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : (term79 A s) = False.
Proof. exact (prop_ext (fun h6 : term79 A s => @lem7040695 A x R f s g h1 h2 h3 h4 h5) (fun h6 : False => @lem7039473 A s h4)). Qed.
Lemma lem7040697 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7040696 A x R f s g h1 h2 h3 h4 h5) (@lem7039473 A s h4)). Qed.
Lemma lem7040698 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : (term79 A s) = False.
Proof. exact (prop_ext (fun h6 : term79 A s => @lem7040697 A x R f s g h1 h2 h3 h4 h5) (fun h6 : False => @lem7039473 A s h4)). Qed.
Lemma lem7040699 {A : Type'} (x : type695 A) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term574 A x R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) : False.
Proof. exact (EQ_MP (@lem7040698 A x R f s g h1 h2 h3 h4 h5) (@lem7039473 A s h4)). Qed.
Lemma lem7040700 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term470 A x1 y1 x2 y2 x R) : False.
Proof. exact (or_elim (@lem7039268 A x1 y1 x2 y2 x R h6) (fun h0 : term582 R x1 y1 x2 y2 => @lem7039973 R x1 y1 x2 y2 h2 h0) (fun h0 : term574 A x R => @lem7040699 A x R f s g h1 h0 h3 h4 h5)). Qed.
Lemma lem7040701 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term470 A x1 y1 x2 y2 x R) : (term79 A s) = False.
Proof. exact (prop_ext (fun h7 : term79 A s => @lem7040700 A f s g x1 y1 x2 y2 x R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7038855 A s h4)). Qed.
Lemma lem7040702 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (x : type695 A) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term470 A x1 y1 x2 y2 x R) : False.
Proof. exact (EQ_MP (@lem7040701 A f s g x1 y1 x2 y2 x R h1 h2 h3 h4 h5 h6) (@lem7038855 A s h4)). Qed.
Lemma lem7040703 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term473 A x1 y1 x2 y2 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7038731 A x1 y1 x2 y2 R h3) (fun x : type695 A => fun h0 : term472 A x1 y1 x2 y2 R x => @lem7040702 A f s g x1 y1 x2 y2 x R h1 h2 h4 h5 h6 h0)). Qed.
Lemma lem7040704 {A : Type'} (x1 : nat) (y1 : nat) (x2 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term475 A x1 y1 x2 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7038730 A x1 y1 x2 R h3) (fun y2 : nat => fun h0 : term474 A x1 y1 x2 R y2 => @lem7040703 A x1 y1 x2 y2 R f s g h1 h2 h0 h4 h5 h6)). Qed.
Lemma lem7040705 {A : Type'} (x1 : nat) (y1 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term477 A x1 y1 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7038729 A x1 y1 R h3) (fun x2 : nat => fun h0 : term476 A x1 y1 R x2 => @lem7040704 A x1 y1 x2 R f s g h1 h2 h0 h4 h5 h6)). Qed.
Lemma lem7040706 {A : Type'} (x1 : nat) (R : type1605) (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : term479 A x1 R) (h4 : @FINITE A s) (h5 : term79 A s) (h6 : term191 A R f s g) : False.
Proof. exact (ex_elim (@lem7038728 A x1 R h3) (fun y1 : nat => fun h0 : term478 A x1 R y1 => @lem7040705 A x1 y1 R f s g h1 h2 h0 h4 h5 h6)). Qed.
Lemma lem7040707 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (ex_elim (@lem7038646 A R h6) (fun x1 : nat => fun h0 : term480 A R x1 => @lem7040706 A x1 R f s g h1 h2 h0 h3 h4 h5)). Qed.
Lemma lem7040708 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (term191 A R f s g) = False.
Proof. exact (prop_ext (fun h7 : term191 A R f s g => @lem7040707 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7038727 A R f s g h5)). Qed.
Lemma lem7040709 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7040708 A f s g R h1 h2 h3 h4 h5 h6) (@lem7038727 A R f s g h5)). Qed.
Lemma lem7040710 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (term79 A s) = False.
Proof. exact (prop_ext (fun h7 : term79 A s => @lem7040709 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7038658 A s h4)). Qed.
Lemma lem7040711 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7040710 A f s g R h1 h2 h3 h4 h5 h6) (@lem7038658 A s h4)). Qed.
Lemma lem7040712 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE A s => @lem7040711 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7038652 A s h3)). Qed.
Lemma lem7040713 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7040712 A f s g R h1 h2 h3 h4 h5 h6) (@lem7038652 A s h3)). Qed.
Lemma lem7040714 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : (term191 A R f s g) = False.
Proof. exact (prop_ext (fun h7 : term191 A R f s g => @lem7040713 A f s g R h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7037925 A R f s g h5)). Qed.
Lemma lem7040715 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term191 A R f s g) (h6 : term158 A R) : False.
Proof. exact (EQ_MP (@lem7040714 A f s g R h1 h2 h3 h4 h5 h6) (@lem7037925 A R f s g h5)). Qed.
Lemma lem7040716 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term158 A R) : term190 A R f s g.
Proof. exact (fun h0 : term191 A R f s g => @lem7040715 A f s g R h1 h2 h3 h4 h0 h5). Qed.
Lemma lem7040717 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (R : type1605) (h1 : term80 A s R f g) (h2 : term71 R) (h3 : @FINITE A s) (h4 : term79 A s) (h5 : term158 A R) : term25 A R f s g.
Proof. exact (EQ_MP (@lem7037924 A R f s g) (@lem7040716 A f g s R h1 h2 h3 h4 h5)). Qed.
Lemma lem7040718 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (R : type1605) (h1 : term71 R) (h2 : @FINITE A s) (h3 : term79 A s) (h4 : term158 A R) : term180 A R f s g.
Proof. exact (fun h0 : term80 A s R f g => @lem7040717 A f g s R h0 h1 h2 h3 h4). Qed.
Lemma lem7040719 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (R : type1605) (h1 : term71 R) (h2 : @FINITE A s) (h3 : term158 A R) : term78 A R f s g.
Proof. exact (fun h0 : term79 A s => @lem7040718 A f g s R h1 h2 h0 h3). Qed.
Lemma lem7040720 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (R : type1605) (h1 : term71 R) (h2 : term158 A R) : term82 A R f s g.
Proof. exact (fun h0 : @FINITE A s => @lem7040719 A f g s R h1 h0 h2). Qed.
Lemma lem7040725 {A : Type'} (f : A -> nat) (g : A -> nat) (R : type1605) (h1 : term71 R) (h2 : term158 A R) : term100 A R f g.
Proof. exact (fun s : A -> Prop => @lem7040720 A f s g R h1 h2). Qed.
Lemma lem7040730 {A : Type'} (f : A -> nat) (R : type1605) (h1 : term71 R) (h2 : term158 A R) : term118 A R f.
Proof. exact (fun g : A -> nat => @lem7040725 A f g R h1 h2). Qed.
Lemma lem7040735 {A : Type'} (R : type1605) (h1 : term71 R) (h2 : term158 A R) : term134 A R.
Proof. exact (fun f : A -> nat => @lem7040730 A f R h1 h2). Qed.
Lemma lem7040736 {A : Type'} (R : type1605) (h1 : term71 R) : term162 A R.
Proof. exact (fun h0 : term158 A R => @lem7040735 A R h1 h0). Qed.
Lemma lem7040737 {A : Type'} (R : type1605) : term172 A R.
Proof. exact (fun h0 : term71 R => @lem7040736 A R h0). Qed.
Lemma lem7040742 {A : Type'} : term176 A.
Proof. exact (fun R : type1605 => @lem7040737 A R). Qed.
Lemma lem7040743 {A : Type'} : term175 A.
Proof. exact (EQ_MP (@lem7037915 A) (@lem7040742 A)). Qed.
Lemma lem7040744 {A : Type'} (R : type1605) : term747 A R.
Proof. exact (@lem7040743 A R). Qed.
Lemma lem7040745 {A : Type'} (R : type1605) : (term747 A R) = (term166 A R).
Proof. exact (eq_refl (term747 A R)). Qed.
Lemma lem7040746 {A : Type'} (R : type1605) : term166 A R.
Proof. exact (EQ_MP (@lem7040745 A R) (@lem7040744 A R)). Qed.
Lemma lem7040748 {A : Type'} (R : type1605) : term166 A R.
Proof. exact (@lem7037543 A R (@lem7040746 A R)). Qed.
Lemma lem7040749 {A : Type'} (R : type1605) (h1 : term71 R) : term164 A R.
Proof. exact (@lem7040748 A R (@lem7037385 R h1)). Qed.
Lemma lem7040750 {A : Type'} (R : type1605) (h1 : term71 R) (h2 : term165 A R) : False.
Proof. exact (@lem7040749 A R h1 (@lem7037527 A R h2)). Qed.
Lemma lem7040751 {A : Type'} (R : type1605) (h1 : term71 R) (h2 : term165 A R) : (term165 A R) = False.
Proof. exact (prop_ext (fun h3 : term165 A R => @lem7040750 A R h1 h2) (fun h3 : False => @lem7037527 A R h2)). Qed.
Lemma lem7040752 {A : Type'} (R : type1605) (h1 : term71 R) (h2 : term165 A R) : False.
Proof. exact (EQ_MP (@lem7040751 A R h1 h2) (@lem7037527 A R h2)). Qed.
Lemma lem7040753 {A : Type'} (R : type1605) (h1 : term71 R) : term164 A R.
Proof. exact (fun h0 : term165 A R => @lem7040752 A R h1 h0). Qed.
Lemma lem7040754 {A : Type'} (R : type1605) (h1 : term71 R) : term162 A R.
Proof. exact (EQ_MP (@lem7037526 A R) (@lem7040753 A R h1)). Qed.
Lemma lem7040755 {A : Type'} (R : type1605) (h1 : term71 R) : term161 A R.
Proof. exact (EQ_MP (@lem7037522 A R) (@lem7040754 A R h1)). Qed.
Lemma lem7040756 {A : Type'} (R : type1605) (h1 : term71 R) : term134 A R.
Proof. exact (@lem7040755 A R h1 (@lem7036629 A R)). Qed.
Lemma lem7040757 {A : Type'} (R : type1605) : term135 A R.
Proof. exact (fun h0 : term71 R => @lem7040756 A R h0). Qed.
Lemma lem7040762 {A : Type'} : term139 A.
Proof. exact (fun R : type1605 => @lem7040757 A R). Qed.
Lemma lem7040763 {A : Type'} : term138 A.
Proof. exact (EQ_MP (@lem7037384 A) (@lem7040762 A)). Qed.
