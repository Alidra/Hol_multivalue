Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1396750_term_abbrevs.
Require Import REAL_MUL_RZERO_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem1396687 (x : real) : term0 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1396688 (x : real) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1396695 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term3 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1396696 (p : Prop) (q : Prop) (p' : Prop) : term4 p q p'.
Proof. exact (fun q' : Prop => @lem1396695 p q p' q'). Qed.
Lemma lem1396697 (p : Prop) (q : Prop) : term5 p q.
Proof. exact (fun p' : Prop => @lem1396696 p q p'). Qed.
Lemma lem1396698 (y : real) : term6 y.
Proof. exact (@lem1396697 (y = term2) (term7 y)). Qed.
Lemma lem1396699 (y : real) (p' : Prop) : term8 y p'.
Proof. exact (@lem1396698 y p'). Qed.
Lemma lem1396700 (y : real) (p' : Prop) : (term8 y p') = (term9 y p').
Proof. exact (eq_refl (term8 y p')). Qed.
Lemma lem1396701 (y : real) (p' : Prop) : term9 y p'.
Proof. exact (EQ_MP (@lem1396700 y p') (@lem1396699 y p')). Qed.
Lemma lem1396702 (y : real) (p' : Prop) (q' : Prop) : term10 y p' q'.
Proof. exact (@lem1396701 y p' q'). Qed.
Lemma lem1396703 (y : real) (p' : Prop) (q' : Prop) : (term10 y p' q') = (term11 y p' q').
Proof. exact (eq_refl (term10 y p' q')). Qed.
Lemma lem1396704 (y : real) (p' : Prop) (q' : Prop) : term11 y p' q'.
Proof. exact (EQ_MP (@lem1396703 y p' q') (@lem1396702 y p' q')). Qed.
Lemma lem1396707 (y : real) : (y = term2) = (y = term2).
Proof. exact (eq_refl (y = term2)). Qed.
Lemma lem1396708 (y : real) (q' : Prop) : term12 y q'.
Proof. exact (@lem1396704 y (y = term2) q'). Qed.
Lemma lem1396709 (y : real) (q' : Prop) : term13 y q'.
Proof. exact (@lem1396708 y q' (@lem1396707 y)). Qed.
Lemma lem1396718 (y : real) (h1 : y = term2) : y = term2.
Proof. exact (h1). Qed.
Lemma lem1396719 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1396720 (x : real) (y : real) (h1 : y = term2) : (real_mul x y) = (term1 x).
Proof. exact (MK_COMB (@lem1396719 x) (@lem1396718 y h1)). Qed.
Lemma lem1396722 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1396688 x) (@lem1396687 x)). Qed.
Lemma lem1396723 (x : real) (y : real) (h1 : y = term2) : (real_mul x y) = term2.
Proof. exact (TRANS (@lem1396720 x y h1) (@lem1396722 x)). Qed.
Lemma lem1396724 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1396725 (x : real) (y : real) (h1 : y = term2) : (term14 x y) = term15.
Proof. exact (MK_COMB (@lem1396724) (@lem1396723 x y h1)). Qed.
Lemma lem1396726 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1396727 (x : real) (y : real) (h1 : y = term2) : ((real_mul x y) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1396725 x y h1) (@lem1396726)). Qed.
Lemma lem1396729 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1396730 (x : real) : (x = x) = True.
Proof. exact (@lem1396729 real x). Qed.
Lemma lem1396731 : (term2 = term2) = True.
Proof. exact (@lem1396730 term2). Qed.
Lemma lem1396732 (x : real) (y : real) (h1 : y = term2) : ((real_mul x y) = term2) = True.
Proof. exact (TRANS (@lem1396727 x y h1) (@lem1396731)). Qed.
Lemma lem1396733 (y : real) (h1 : y = term2) : (term16 y) = term17.
Proof. exact (fun_ext (fun x : real => @lem1396732 x y h1)). Qed.
Lemma lem1396734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396735 (y : real) (h1 : y = term2) : (term7 y) = term18.
Proof. exact (MK_COMB (@lem1396734) (@lem1396733 y h1)). Qed.
Lemma lem1396737 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1396738 (t : Prop) : (term20 t) = t.
Proof. exact (@lem1396737 real t). Qed.
Lemma lem1396739 : term18 = True.
Proof. exact (@lem1396738 True). Qed.
Lemma lem1396740 (y : real) (h1 : y = term2) : (term7 y) = True.
Proof. exact (TRANS (@lem1396735 y h1) (@lem1396739)). Qed.
Lemma lem1396741 (y : real) : term21 y.
Proof. exact (fun h0 : y = term2 => @lem1396740 y h0). Qed.
Lemma lem1396742 (y : real) : term22 y.
Proof. exact (@lem1396709 y True). Qed.
Lemma lem1396743 (y : real) : (term23 y) = (term24 y).
Proof. exact (@lem1396742 y (@lem1396741 y)). Qed.
Lemma lem1396747 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1396748 (y : real) : (term24 y) = True.
Proof. exact (@lem1396747 (y = term2)). Qed.
Lemma lem1396749 (y : real) : (term23 y) = True.
Proof. exact (TRANS (@lem1396743 y) (@lem1396748 y)). Qed.
Lemma lem1396750 (y : real) : True = (term23 y).
Proof. exact (SYM (@lem1396749 y)). Qed.
