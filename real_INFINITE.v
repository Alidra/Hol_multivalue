Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_INFINITE_term_abbrevs.
Require Import FINITE_REAL_INTERVAL_spec.
Require Import FINITE_SUBSET_spec.
Require Import INFINITE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUBSET_UNIV_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem4713563 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3220196 A s). Qed.
Lemma lem4713564 {A : Type'} (s : A -> Prop) : (term0 A s) = (@SUBSET A s (@UNIV A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4713565 {A : Type'} (s : A -> Prop) : @SUBSET A s (@UNIV A).
Proof. exact (EQ_MP (@lem4713564 A s) (@lem4713563 A s)). Qed.
Lemma lem4713566 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = ((@SUBSET A s (@UNIV A)) = True).
Proof. exact (@lem7 (@SUBSET A s (@UNIV A))). Qed.
Lemma lem4713568 : term1.
Proof. exact (proj2 (@lem4713562)). Qed.
Lemma lem4713614 : term2.
Proof. exact (proj1 (@lem4713568)). Qed.
Lemma lem4713615 (a : real) : term3 a.
Proof. exact (@lem4713614 a). Qed.
Lemma lem4713616 (a : real) : (term3 a) = (term4 a).
Proof. exact (eq_refl (term3 a)). Qed.
Lemma lem4713617 (a : real) : term4 a.
Proof. exact (EQ_MP (@lem4713616 a) (@lem4713615 a)). Qed.
Lemma lem4713618 (a : real) : term5 a.
Proof. exact (@lem82 (term6 a)). Qed.
Lemma lem4713635 (p : Prop) (q : Prop) (r : Prop) : (term7 p q r) = (term8 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4713636 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term9 A t s) = (term10 A t s).
Proof. exact (@lem4713635 (@FINITE A t) (@SUBSET A s t) (@FINITE A s)). Qed.
Lemma lem4713641 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4713636 A t s)). Qed.
Lemma lem4713642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4713643 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (MK_COMB (@lem4713642 A) (@lem4713641 A s)). Qed.
Lemma lem4713648 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4713643 A s)). Qed.
Lemma lem4713649 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4713650 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem4713649 A) (@lem4713648 A)). Qed.
Lemma lem4713655 {A : Type'} : term18 A.
Proof. exact (EQ_MP (@lem4713650 A) (@lem3599924 A)). Qed.
Lemma lem4713656 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem4713657 {A : Type'} (s : A -> Prop) (h1 : term18 A) : term19 A s.
Proof. exact (@lem4713656 A h1 s). Qed.
Lemma lem4713658 {A : Type'} (s : A -> Prop) : (term19 A s) = (term14 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem4713659 {A : Type'} (s : A -> Prop) (h1 : term18 A) : term14 A s.
Proof. exact (EQ_MP (@lem4713658 A s) (@lem4713657 A s h1)). Qed.
Lemma lem4713660 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term18 A) : term20 A s t.
Proof. exact (@lem4713659 A s h1 t). Qed.
Lemma lem4713661 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term20 A s t) = (term10 A t s).
Proof. exact (eq_refl (term20 A s t)). Qed.
Lemma lem4713662 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term18 A) : term10 A t s.
Proof. exact (EQ_MP (@lem4713661 A t s) (@lem4713660 A s t h1)). Qed.
Lemma lem4713663 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem4713664 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term18 A) (h2 : @FINITE A t) : term21 A t s.
Proof. exact (@lem4713662 A t s h1 (@lem4713663 A t h2)). Qed.
Lemma lem4713665 {A : Type'} (t : A -> Prop) (h1 : term18 A) (h2 : @FINITE A t) : term22 A t.
Proof. exact (fun s : A -> Prop => @lem4713664 A s t h1 h2). Qed.
Lemma lem4713666 {A : Type'} (t : A -> Prop) (h1 : term18 A) : term23 A t.
Proof. exact (fun h0 : @FINITE A t => @lem4713665 A t h1 h0). Qed.
Lemma lem4713667 {A : Type'} (h1 : term18 A) : term24 A.
Proof. exact (fun t : A -> Prop => @lem4713666 A t h1). Qed.
Lemma lem4713668 {A : Type'} : term25 A.
Proof. exact (fun h0 : term18 A => @lem4713667 A h0). Qed.
Lemma lem4713669 {A : Type'} : term24 A.
Proof. exact (@lem4713668 A (@lem4713655 A)). Qed.
Lemma lem4713670 {A : Type'} (t : A -> Prop) : term26 A t.
Proof. exact (@lem4713669 A t). Qed.
Lemma lem4713671 {A : Type'} (t : A -> Prop) : (term26 A t) = (term23 A t).
Proof. exact (eq_refl (term26 A t)). Qed.
Lemma lem4713673 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem4713674 {A : Type'} (s : A -> Prop) : (term27 A s) = ((@INFINITE A s) = (term28 A s)).
Proof. exact (eq_refl (term27 A s)). Qed.
Lemma lem4713677 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term28 A s).
Proof. exact (EQ_MP (@lem4713674 A s) (@lem4713673 A s)). Qed.
Lemma lem4713678 (s : real -> Prop) : (@INFINITE real s) = (term29 s).
Proof. exact (@lem4713677 real s). Qed.
Lemma lem4713679 : (@INFINITE real (@UNIV real)) = term30.
Proof. exact (@lem4713678 (@UNIV real)). Qed.
Lemma lem4713680 : term30 = (@INFINITE real (@UNIV real)).
Proof. exact (SYM (@lem4713679)). Qed.
Lemma lem4713681 (h1 : @FINITE real (@UNIV real)) : @FINITE real (@UNIV real).
Proof. exact (h1). Qed.
Lemma lem4713683 {A : Type'} (t : A -> Prop) : term23 A t.
Proof. exact (EQ_MP (@lem4713671 A t) (@lem4713670 A t)). Qed.
Lemma lem4713684 (t : real -> Prop) : term31 t.
Proof. exact (@lem4713683 real t). Qed.
Lemma lem4713685 : term32.
Proof. exact (@lem4713684 (@UNIV real)). Qed.
Lemma lem4713686 (h1 : @FINITE real (@UNIV real)) : term33.
Proof. exact (@lem4713685 (@lem4713681 h1)). Qed.
Lemma lem4713687 (h1 : @FINITE real (@UNIV real)) : term34.
Proof. exact (@lem4713686 h1 term35). Qed.
Lemma lem4713688 : term34 = term36.
Proof. exact (eq_refl term34). Qed.
Lemma lem4713689 (h1 : @FINITE real (@UNIV real)) : term36.
Proof. exact (EQ_MP (@lem4713688) (@lem4713687 h1)). Qed.
Lemma lem4713691 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4713692 : term37 = term38.
Proof. exact (@lem4713691 term36). Qed.
Lemma lem4713696 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4713566 A s) (@lem4713565 A s)). Qed.
Lemma lem4713697 (s : real -> Prop) : (@SUBSET real s (@UNIV real)) = True.
Proof. exact (@lem4713696 real s). Qed.
Lemma lem4713698 : term39 = True.
Proof. exact (@lem4713697 term35). Qed.
Lemma lem4713699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4713700 : term40 = (imp True).
Proof. exact (MK_COMB (@lem4713699) (@lem4713698)). Qed.
Lemma lem4713704 (a : real) : (term6 a) = False.
Proof. exact (@lem4713618 a (@lem4713617 a)). Qed.
Lemma lem4713705 : term41 = False.
Proof. exact (@lem4713704 term42). Qed.
Lemma lem4713706 : term36 = (True -> False).
Proof. exact (MK_COMB (@lem4713700) (@lem4713705)). Qed.
Lemma lem4713708 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4713709 : (True -> False) = False.
Proof. exact (@lem4713708 False). Qed.
Lemma lem4713710 : term36 = False.
Proof. exact (TRANS (@lem4713706) (@lem4713709)). Qed.
Lemma lem4713711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4713712 : term38 = (~ False).
Proof. exact (MK_COMB (@lem4713711) (@lem4713710)). Qed.
Lemma lem4713714 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4713715 : term38 = True.
Proof. exact (TRANS (@lem4713712) (@lem4713714)). Qed.
Lemma lem4713716 : term37 = True.
Proof. exact (TRANS (@lem4713692) (@lem4713715)). Qed.
Lemma lem4713717 : True = term37.
Proof. exact (SYM (@lem4713716)). Qed.
Lemma lem4713718 : term37.
Proof. exact (EQ_MP (@lem4713717) (@lem0)). Qed.
Lemma lem4713719 (h1 : @FINITE real (@UNIV real)) : False.
Proof. exact (@lem4713718 (@lem4713689 h1)). Qed.
Lemma lem4713720 : term43.
Proof. exact (fun h0 : @FINITE real (@UNIV real) => @lem4713719 h0). Qed.
Lemma lem4713721 : term43 = term30.
Proof. exact (@lem69 (@FINITE real (@UNIV real))). Qed.
Lemma lem4713722 : term30.
Proof. exact (EQ_MP (@lem4713721) (@lem4713720)). Qed.
Lemma lem4713723 : @INFINITE real (@UNIV real).
Proof. exact (EQ_MP (@lem4713680) (@lem4713722)). Qed.
