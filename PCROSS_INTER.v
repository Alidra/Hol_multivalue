Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_INTER_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import IN_INTER_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8036725 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8036726 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8036727 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8036726 _141927 _141928 _141929 s) (@lem8036725 _141927 _141928 _141929 s)). Qed.
Lemma lem8036728 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8036727 _141927 _141928 _141929 s t). Qed.
Lemma lem8036729 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8036730 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8036729 _141927 _141928 _141929 s t) (@lem8036728 _141927 _141928 _141929 s t)). Qed.
Lemma lem8036731 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8036730 _141927 _141928 _141929 s t x). Qed.
Lemma lem8036732 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8036733 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8036732 _141927 _141928 _141929 x s t) (@lem8036731 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8036734 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8036733 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8036735 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8036737 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem8036738 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem8036739 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem8036738 A s) (@lem8036737 A s)). Qed.
Lemma lem8036740 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem8036739 A s t). Qed.
Lemma lem8036741 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem8036742 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem8036741 A s t) (@lem8036740 A s t)). Qed.
Lemma lem8036743 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem8036742 A s t x). Qed.
Lemma lem8036744 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem8036746 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8036747 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem8036748 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem8036747 A s) (@lem8036746 A s)). Qed.
Lemma lem8036749 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem8036748 A s t). Qed.
Lemma lem8036750 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem8036775 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem8036750 A s t) (@lem8036749 A s t)). Qed.
Lemma lem8036776 {_142469 _142470 _142471 : Type'} (s : type16 _142469 _142470 _142471) (t : type16 _142469 _142470 _142471) : (s = t) = (term20 _142469 _142470 _142471 s t).
Proof. exact (@lem8036775 (type2 _142469 _142470 _142471) s t). Qed.
Lemma lem8036777 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : ((term21 _142469 _142470 _142471 s t u) = (term22 _142469 _142470 _142471 t s u)) = (term23 _142469 _142470 _142471 t s u).
Proof. exact (@lem8036776 _142469 _142470 _142471 (term21 _142469 _142470 _142471 s t u) (term22 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036783 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term24 _140454 _140455 _140456 P) = (term25 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8036784 {_142469 _142470 _142471 : Type'} (P : type16 _142469 _142470 _142471) : (term24 _142469 _142470 _142471 P) = (term25 _142469 _142470 _142471 P).
Proof. exact (@lem8036783 _142469 _142470 _142471 P). Qed.
Lemma lem8036785 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term26 _142469 _142470 _142471 t s u) = (term27 _142469 _142470 _142471 t s u).
Proof. exact (@lem8036784 _142469 _142470 _142471 (term28 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036786 {_142469 _142470 _142471 : Type'} (x : type2 _142469 _142470 _142471) (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term29 _142469 _142470 _142471 t s u x) = ((term30 _142469 _142470 _142471 x s t u) = (term31 _142469 _142470 _142471 x t s u)).
Proof. exact (eq_refl (term29 _142469 _142470 _142471 t s u x)). Qed.
Lemma lem8036787 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term32 _142469 _142470 _142471 t s u) = (term28 _142469 _142470 _142471 t s u).
Proof. exact (fun_ext (fun x : type2 _142469 _142470 _142471 => @lem8036786 _142469 _142470 _142471 x t s u)). Qed.
Lemma lem8036788 {_142469 _142470 _142471 : Type'} : (@all (cart _142469 (finite_sum _142470 _142471))) = (@all (cart _142469 (finite_sum _142470 _142471))).
Proof. exact (eq_refl (@all (cart _142469 (finite_sum _142470 _142471)))). Qed.
Lemma lem8036789 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term26 _142469 _142470 _142471 t s u) = (term23 _142469 _142470 _142471 t s u).
Proof. exact (MK_COMB (@lem8036788 _142469 _142470 _142471) (@lem8036787 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036791 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term33 _142469 _142470 _142471 t s u) = (term34 _142469 _142470 _142471 t s u).
Proof. exact (MK_COMB (@lem8036790) (@lem8036789 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036792 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (y : cart _142469 _142471) (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term35 _142469 _142470 _142471 t s u x y) = ((term36 _142469 _142470 _142471 x y s t u) = (term37 _142469 _142470 _142471 x y t s u)).
Proof. exact (eq_refl (term35 _142469 _142470 _142471 t s u x y)). Qed.
Lemma lem8036793 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term38 _142469 _142470 _142471 t s u x) = (term39 _142469 _142470 _142471 x t s u).
Proof. exact (fun_ext (fun y : cart _142469 _142471 => @lem8036792 _142469 _142470 _142471 x y t s u)). Qed.
Lemma lem8036794 {_142469 _142471 : Type'} : (@all (cart _142469 _142471)) = (@all (cart _142469 _142471)).
Proof. exact (eq_refl (@all (cart _142469 _142471))). Qed.
Lemma lem8036795 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term40 _142469 _142470 _142471 t s u x) = (term41 _142469 _142470 _142471 x t s u).
Proof. exact (MK_COMB (@lem8036794 _142469 _142471) (@lem8036793 _142469 _142470 _142471 x t s u)). Qed.
Lemma lem8036796 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term42 _142469 _142470 _142471 t s u) = (term43 _142469 _142470 _142471 t s u).
Proof. exact (fun_ext (fun x : cart _142469 _142470 => @lem8036795 _142469 _142470 _142471 x t s u)). Qed.
Lemma lem8036797 {_142469 _142470 : Type'} : (@all (cart _142469 _142470)) = (@all (cart _142469 _142470)).
Proof. exact (eq_refl (@all (cart _142469 _142470))). Qed.
Lemma lem8036798 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term27 _142469 _142470 _142471 t s u) = (term44 _142469 _142470 _142471 t s u).
Proof. exact (MK_COMB (@lem8036797 _142469 _142470) (@lem8036796 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036799 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : ((term26 _142469 _142470 _142471 t s u) = (term27 _142469 _142470 _142471 t s u)) = ((term23 _142469 _142470 _142471 t s u) = (term44 _142469 _142470 _142471 t s u)).
Proof. exact (MK_COMB (@lem8036791 _142469 _142470 _142471 t s u) (@lem8036798 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036800 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term23 _142469 _142470 _142471 t s u) = (term44 _142469 _142470 _142471 t s u).
Proof. exact (EQ_MP (@lem8036799 _142469 _142470 _142471 t s u) (@lem8036785 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036807 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : ((term21 _142469 _142470 _142471 s t u) = (term22 _142469 _142470 _142471 t s u)) = (term44 _142469 _142470 _142471 t s u).
Proof. exact (TRANS (@lem8036777 _142469 _142470 _142471 t s u) (@lem8036800 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036819 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8036735 _141927 _141928 _141929 x s y t) (@lem8036734 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8036820 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term7 _142469 _142470 _142471 x y s t) = (term8 _142469 _142470 _142471 x s y t).
Proof. exact (@lem8036819 _142469 _142470 _142471 x s y t). Qed.
Lemma lem8036821 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (t : type24 _142469 _142471) (u : type24 _142469 _142471) : (term36 _142469 _142470 _142471 x y s t u) = (term45 _142469 _142470 _142471 x s y t u).
Proof. exact (@lem8036820 _142469 _142470 _142471 x s y (@INTER (cart _142469 _142471) t u)). Qed.
Lemma lem8036825 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8036744 A s x t) (@lem8036743 A s t x)). Qed.
Lemma lem8036826 {_142469 _142471 : Type'} (s : type24 _142469 _142471) (x : cart _142469 _142471) (t : type24 _142469 _142471) : (term46 _142469 _142471 x s t) = (term47 _142469 _142471 s x t).
Proof. exact (@lem8036825 (cart _142469 _142471) s x t). Qed.
Lemma lem8036827 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term46 _142469 _142471 y t u) = (term47 _142469 _142471 t y u).
Proof. exact (@lem8036826 _142469 _142471 t y u). Qed.
Lemma lem8036830 {_142469 _142470 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) : (term48 _142469 _142470 x s) = (term48 _142469 _142470 x s).
Proof. exact (eq_refl (term48 _142469 _142470 x s)). Qed.
Lemma lem8036831 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term45 _142469 _142470 _142471 x s y t u) = (term49 _142469 _142470 _142471 x s t y u).
Proof. exact (MK_COMB (@lem8036830 _142469 _142470 x s) (@lem8036827 _142469 _142471 t y u)). Qed.
Lemma lem8036834 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term36 _142469 _142470 _142471 x y s t u) = (term49 _142469 _142470 _142471 x s t y u).
Proof. exact (TRANS (@lem8036821 _142469 _142470 _142471 x s y t u) (@lem8036831 _142469 _142470 _142471 x s t y u)). Qed.
Lemma lem8036835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036836 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term50 _142469 _142470 _142471 x y s t u) = (term51 _142469 _142470 _142471 x s t y u).
Proof. exact (MK_COMB (@lem8036835) (@lem8036834 _142469 _142470 _142471 x s t y u)). Qed.
Lemma lem8036838 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8036744 A s x t) (@lem8036743 A s t x)). Qed.
Lemma lem8036839 {_142469 _142470 _142471 : Type'} (s : type16 _142469 _142470 _142471) (x : type2 _142469 _142470 _142471) (t : type16 _142469 _142470 _142471) : (term52 _142469 _142470 _142471 x s t) = (term53 _142469 _142470 _142471 s x t).
Proof. exact (@lem8036838 (type2 _142469 _142470 _142471) s x t). Qed.
Lemma lem8036840 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (y : cart _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term37 _142469 _142470 _142471 x y t s u) = (term54 _142469 _142470 _142471 t x y s u).
Proof. exact (@lem8036839 _142469 _142470 _142471 (@PCROSS _142469 _142470 _142471 s t) (@pastecart _142469 _142470 _142471 x y) (@PCROSS _142469 _142470 _142471 s u)). Qed.
Lemma lem8036844 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8036735 _141927 _141928 _141929 x s y t) (@lem8036734 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8036845 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term7 _142469 _142470 _142471 x y s t) = (term8 _142469 _142470 _142471 x s y t).
Proof. exact (@lem8036844 _142469 _142470 _142471 x s y t). Qed.
Lemma lem8036848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036849 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term55 _142469 _142470 _142471 x y s t) = (term56 _142469 _142470 _142471 x s y t).
Proof. exact (MK_COMB (@lem8036848) (@lem8036845 _142469 _142470 _142471 x s y t)). Qed.
Lemma lem8036851 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8036735 _141927 _141928 _141929 x s y t) (@lem8036734 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8036852 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term7 _142469 _142470 _142471 x y s t) = (term8 _142469 _142470 _142471 x s y t).
Proof. exact (@lem8036851 _142469 _142470 _142471 x s y t). Qed.
Lemma lem8036853 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term7 _142469 _142470 _142471 x y s u) = (term8 _142469 _142470 _142471 x s y u).
Proof. exact (@lem8036852 _142469 _142470 _142471 x s y u). Qed.
Lemma lem8036856 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term54 _142469 _142470 _142471 t x y s u) = (term57 _142469 _142470 _142471 t x s y u).
Proof. exact (MK_COMB (@lem8036849 _142469 _142470 _142471 x s y t) (@lem8036853 _142469 _142470 _142471 x s y u)). Qed.
Lemma lem8036859 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term37 _142469 _142470 _142471 x y t s u) = (term57 _142469 _142470 _142471 t x s y u).
Proof. exact (TRANS (@lem8036840 _142469 _142470 _142471 t x y s u) (@lem8036856 _142469 _142470 _142471 t x s y u)). Qed.
Lemma lem8036860 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term36 _142469 _142470 _142471 x y s t u) = (term37 _142469 _142470 _142471 x y t s u)) = ((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)).
Proof. exact (MK_COMB (@lem8036836 _142469 _142470 _142471 x s t y u) (@lem8036859 _142469 _142470 _142471 t x s y u)). Qed.
Lemma lem8036865 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term39 _142469 _142470 _142471 x t s u) = (term58 _142469 _142470 _142471 t x s u).
Proof. exact (fun_ext (fun y : cart _142469 _142471 => @lem8036860 _142469 _142470 _142471 t x s y u)). Qed.
Lemma lem8036866 {_142469 _142471 : Type'} : (@all (cart _142469 _142471)) = (@all (cart _142469 _142471)).
Proof. exact (eq_refl (@all (cart _142469 _142471))). Qed.
Lemma lem8036867 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term41 _142469 _142470 _142471 x t s u) = (term59 _142469 _142470 _142471 t x s u).
Proof. exact (MK_COMB (@lem8036866 _142469 _142471) (@lem8036865 _142469 _142470 _142471 t x s u)). Qed.
Lemma lem8036874 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term43 _142469 _142470 _142471 t s u) = (term60 _142469 _142470 _142471 t s u).
Proof. exact (fun_ext (fun x : cart _142469 _142470 => @lem8036867 _142469 _142470 _142471 t x s u)). Qed.
Lemma lem8036875 {_142469 _142470 : Type'} : (@all (cart _142469 _142470)) = (@all (cart _142469 _142470)).
Proof. exact (eq_refl (@all (cart _142469 _142470))). Qed.
Lemma lem8036876 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : (term44 _142469 _142470 _142471 t s u) = (term61 _142469 _142470 _142471 t s u).
Proof. exact (MK_COMB (@lem8036875 _142469 _142470) (@lem8036874 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036883 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : ((term21 _142469 _142470 _142471 s t u) = (term22 _142469 _142470 _142471 t s u)) = (term61 _142469 _142470 _142471 t s u).
Proof. exact (TRANS (@lem8036807 _142469 _142470 _142471 t s u) (@lem8036876 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036884 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) : (term62 _142469 _142470 _142471 t s) = (term63 _142469 _142470 _142471 t s).
Proof. exact (fun_ext (fun u : type24 _142469 _142471 => @lem8036883 _142469 _142470 _142471 t s u)). Qed.
Lemma lem8036885 {_142469 _142471 : Type'} : (@all ((cart _142469 _142471) -> Prop)) = (@all ((cart _142469 _142471) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142469 _142471) -> Prop))). Qed.
Lemma lem8036886 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) : (term64 _142469 _142470 _142471 t s) = (term65 _142469 _142470 _142471 t s).
Proof. exact (MK_COMB (@lem8036885 _142469 _142471) (@lem8036884 _142469 _142470 _142471 t s)). Qed.
Lemma lem8036893 {_142469 _142470 _142471 : Type'} (s : type24 _142469 _142470) : (term66 _142469 _142470 _142471 s) = (term67 _142469 _142470 _142471 s).
Proof. exact (fun_ext (fun t : type24 _142469 _142471 => @lem8036886 _142469 _142470 _142471 t s)). Qed.
Lemma lem8036894 {_142469 _142471 : Type'} : (@all ((cart _142469 _142471) -> Prop)) = (@all ((cart _142469 _142471) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142469 _142471) -> Prop))). Qed.
Lemma lem8036895 {_142469 _142470 _142471 : Type'} (s : type24 _142469 _142470) : (term68 _142469 _142470 _142471 s) = (term69 _142469 _142470 _142471 s).
Proof. exact (MK_COMB (@lem8036894 _142469 _142471) (@lem8036893 _142469 _142470 _142471 s)). Qed.
Lemma lem8036902 {_142469 _142470 _142471 : Type'} : (term70 _142469 _142470 _142471) = (term71 _142469 _142470 _142471).
Proof. exact (fun_ext (fun s : type24 _142469 _142470 => @lem8036895 _142469 _142470 _142471 s)). Qed.
Lemma lem8036903 {_142469 _142470 : Type'} : (@all ((cart _142469 _142470) -> Prop)) = (@all ((cart _142469 _142470) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142469 _142470) -> Prop))). Qed.
Lemma lem8036904 {_142469 _142470 _142471 : Type'} : (term72 _142469 _142470 _142471) = (term73 _142469 _142470 _142471).
Proof. exact (MK_COMB (@lem8036903 _142469 _142470) (@lem8036902 _142469 _142470 _142471)). Qed.
Lemma lem8036911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036912 {_142469 _142470 _142471 : Type'} : (term74 _142469 _142470 _142471) = (term75 _142469 _142470 _142471).
Proof. exact (MK_COMB (@lem8036911) (@lem8036904 _142469 _142470 _142471)). Qed.
Lemma lem8036934 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem8036750 A s t) (@lem8036749 A s t)). Qed.
Lemma lem8036935 {_142505 _142506 _142507 : Type'} (s : type16 _142505 _142506 _142507) (t : type16 _142505 _142506 _142507) : (s = t) = (term20 _142505 _142506 _142507 s t).
Proof. exact (@lem8036934 (type2 _142505 _142506 _142507) s t). Qed.
Lemma lem8036936 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : ((term76 _142505 _142506 _142507 s t u) = (term77 _142505 _142506 _142507 s t u)) = (term78 _142505 _142506 _142507 s t u).
Proof. exact (@lem8036935 _142505 _142506 _142507 (term76 _142505 _142506 _142507 s t u) (term77 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036942 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term24 _140454 _140455 _140456 P) = (term25 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8036943 {_142505 _142506 _142507 : Type'} (P : type16 _142505 _142506 _142507) : (term24 _142505 _142506 _142507 P) = (term25 _142505 _142506 _142507 P).
Proof. exact (@lem8036942 _142505 _142506 _142507 P). Qed.
Lemma lem8036944 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term79 _142505 _142506 _142507 s t u) = (term80 _142505 _142506 _142507 s t u).
Proof. exact (@lem8036943 _142505 _142506 _142507 (term81 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036945 {_142505 _142506 _142507 : Type'} (x : type2 _142505 _142506 _142507) (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term82 _142505 _142506 _142507 s t u x) = ((term83 _142505 _142506 _142507 x s t u) = (term84 _142505 _142506 _142507 x s t u)).
Proof. exact (eq_refl (term82 _142505 _142506 _142507 s t u x)). Qed.
Lemma lem8036946 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term85 _142505 _142506 _142507 s t u) = (term81 _142505 _142506 _142507 s t u).
Proof. exact (fun_ext (fun x : type2 _142505 _142506 _142507 => @lem8036945 _142505 _142506 _142507 x s t u)). Qed.
Lemma lem8036947 {_142505 _142506 _142507 : Type'} : (@all (cart _142505 (finite_sum _142506 _142507))) = (@all (cart _142505 (finite_sum _142506 _142507))).
Proof. exact (eq_refl (@all (cart _142505 (finite_sum _142506 _142507)))). Qed.
Lemma lem8036948 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term79 _142505 _142506 _142507 s t u) = (term78 _142505 _142506 _142507 s t u).
Proof. exact (MK_COMB (@lem8036947 _142505 _142506 _142507) (@lem8036946 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036950 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term86 _142505 _142506 _142507 s t u) = (term87 _142505 _142506 _142507 s t u).
Proof. exact (MK_COMB (@lem8036949) (@lem8036948 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036951 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (y : cart _142505 _142507) (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term88 _142505 _142506 _142507 s t u x y) = ((term89 _142505 _142506 _142507 x y s t u) = (term90 _142505 _142506 _142507 x y s t u)).
Proof. exact (eq_refl (term88 _142505 _142506 _142507 s t u x y)). Qed.
Lemma lem8036952 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term91 _142505 _142506 _142507 s t u x) = (term92 _142505 _142506 _142507 x s t u).
Proof. exact (fun_ext (fun y : cart _142505 _142507 => @lem8036951 _142505 _142506 _142507 x y s t u)). Qed.
Lemma lem8036953 {_142505 _142507 : Type'} : (@all (cart _142505 _142507)) = (@all (cart _142505 _142507)).
Proof. exact (eq_refl (@all (cart _142505 _142507))). Qed.
Lemma lem8036954 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term93 _142505 _142506 _142507 s t u x) = (term94 _142505 _142506 _142507 x s t u).
Proof. exact (MK_COMB (@lem8036953 _142505 _142507) (@lem8036952 _142505 _142506 _142507 x s t u)). Qed.
Lemma lem8036955 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term95 _142505 _142506 _142507 s t u) = (term96 _142505 _142506 _142507 s t u).
Proof. exact (fun_ext (fun x : cart _142505 _142506 => @lem8036954 _142505 _142506 _142507 x s t u)). Qed.
Lemma lem8036956 {_142505 _142506 : Type'} : (@all (cart _142505 _142506)) = (@all (cart _142505 _142506)).
Proof. exact (eq_refl (@all (cart _142505 _142506))). Qed.
Lemma lem8036957 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term80 _142505 _142506 _142507 s t u) = (term97 _142505 _142506 _142507 s t u).
Proof. exact (MK_COMB (@lem8036956 _142505 _142506) (@lem8036955 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036958 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : ((term79 _142505 _142506 _142507 s t u) = (term80 _142505 _142506 _142507 s t u)) = ((term78 _142505 _142506 _142507 s t u) = (term97 _142505 _142506 _142507 s t u)).
Proof. exact (MK_COMB (@lem8036950 _142505 _142506 _142507 s t u) (@lem8036957 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036959 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term78 _142505 _142506 _142507 s t u) = (term97 _142505 _142506 _142507 s t u).
Proof. exact (EQ_MP (@lem8036958 _142505 _142506 _142507 s t u) (@lem8036944 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036966 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : ((term76 _142505 _142506 _142507 s t u) = (term77 _142505 _142506 _142507 s t u)) = (term97 _142505 _142506 _142507 s t u).
Proof. exact (TRANS (@lem8036936 _142505 _142506 _142507 s t u) (@lem8036959 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8036978 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8036735 _141927 _141928 _141929 x s y t) (@lem8036734 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8036979 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (y : cart _142505 _142507) (t : type24 _142505 _142507) : (term7 _142505 _142506 _142507 x y s t) = (term8 _142505 _142506 _142507 x s y t).
Proof. exact (@lem8036978 _142505 _142506 _142507 x s y t). Qed.
Lemma lem8036980 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term89 _142505 _142506 _142507 x y s t u) = (term98 _142505 _142506 _142507 x s t y u).
Proof. exact (@lem8036979 _142505 _142506 _142507 x (@INTER (cart _142505 _142506) s t) y u). Qed.
Lemma lem8036984 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8036744 A s x t) (@lem8036743 A s t x)). Qed.
Lemma lem8036985 {_142505 _142506 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term46 _142505 _142506 x s t) = (term47 _142505 _142506 s x t).
Proof. exact (@lem8036984 (cart _142505 _142506) s x t). Qed.
Lemma lem8036988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036989 {_142505 _142506 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term99 _142505 _142506 x s t) = (term100 _142505 _142506 s x t).
Proof. exact (MK_COMB (@lem8036988) (@lem8036985 _142505 _142506 s x t)). Qed.
Lemma lem8036990 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (@IN (cart _142505 _142507) y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (eq_refl (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8036991 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term98 _142505 _142506 _142507 x s t y u) = (term101 _142505 _142506 _142507 s x t y u).
Proof. exact (MK_COMB (@lem8036989 _142505 _142506 s x t) (@lem8036990 _142505 _142507 y u)). Qed.
Lemma lem8036994 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term89 _142505 _142506 _142507 x y s t u) = (term101 _142505 _142506 _142507 s x t y u).
Proof. exact (TRANS (@lem8036980 _142505 _142506 _142507 x s t y u) (@lem8036991 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8036995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036996 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term102 _142505 _142506 _142507 x y s t u) = (term103 _142505 _142506 _142507 s x t y u).
Proof. exact (MK_COMB (@lem8036995) (@lem8036994 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8036998 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8036744 A s x t) (@lem8036743 A s t x)). Qed.
Lemma lem8036999 {_142505 _142506 _142507 : Type'} (s : type16 _142505 _142506 _142507) (x : type2 _142505 _142506 _142507) (t : type16 _142505 _142506 _142507) : (term52 _142505 _142506 _142507 x s t) = (term53 _142505 _142506 _142507 s x t).
Proof. exact (@lem8036998 (type2 _142505 _142506 _142507) s x t). Qed.
Lemma lem8037000 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (y : cart _142505 _142507) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term90 _142505 _142506 _142507 x y s t u) = (term104 _142505 _142506 _142507 s x y t u).
Proof. exact (@lem8036999 _142505 _142506 _142507 (@PCROSS _142505 _142506 _142507 s u) (@pastecart _142505 _142506 _142507 x y) (@PCROSS _142505 _142506 _142507 t u)). Qed.
Lemma lem8037004 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8036735 _141927 _141928 _141929 x s y t) (@lem8036734 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037005 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (y : cart _142505 _142507) (t : type24 _142505 _142507) : (term7 _142505 _142506 _142507 x y s t) = (term8 _142505 _142506 _142507 x s y t).
Proof. exact (@lem8037004 _142505 _142506 _142507 x s y t). Qed.
Lemma lem8037006 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term7 _142505 _142506 _142507 x y s u) = (term8 _142505 _142506 _142507 x s y u).
Proof. exact (@lem8037005 _142505 _142506 _142507 x s y u). Qed.
Lemma lem8037009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037010 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term55 _142505 _142506 _142507 x y s u) = (term56 _142505 _142506 _142507 x s y u).
Proof. exact (MK_COMB (@lem8037009) (@lem8037006 _142505 _142506 _142507 x s y u)). Qed.
Lemma lem8037012 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8036735 _141927 _141928 _141929 x s y t) (@lem8036734 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8037013 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (y : cart _142505 _142507) (t : type24 _142505 _142507) : (term7 _142505 _142506 _142507 x y s t) = (term8 _142505 _142506 _142507 x s y t).
Proof. exact (@lem8037012 _142505 _142506 _142507 x s y t). Qed.
Lemma lem8037014 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term7 _142505 _142506 _142507 x y t u) = (term8 _142505 _142506 _142507 x t y u).
Proof. exact (@lem8037013 _142505 _142506 _142507 x t y u). Qed.
Lemma lem8037017 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term104 _142505 _142506 _142507 s x y t u) = (term105 _142505 _142506 _142507 s x t y u).
Proof. exact (MK_COMB (@lem8037010 _142505 _142506 _142507 x s y u) (@lem8037014 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037020 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term90 _142505 _142506 _142507 x y s t u) = (term105 _142505 _142506 _142507 s x t y u).
Proof. exact (TRANS (@lem8037000 _142505 _142506 _142507 s x y t u) (@lem8037017 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8037021 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term89 _142505 _142506 _142507 x y s t u) = (term90 _142505 _142506 _142507 x y s t u)) = ((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)).
Proof. exact (MK_COMB (@lem8036996 _142505 _142506 _142507 s x t y u) (@lem8037020 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8037026 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term92 _142505 _142506 _142507 x s t u) = (term106 _142505 _142506 _142507 s x t u).
Proof. exact (fun_ext (fun y : cart _142505 _142507 => @lem8037021 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8037027 {_142505 _142507 : Type'} : (@all (cart _142505 _142507)) = (@all (cart _142505 _142507)).
Proof. exact (eq_refl (@all (cart _142505 _142507))). Qed.
Lemma lem8037028 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term94 _142505 _142506 _142507 x s t u) = (term107 _142505 _142506 _142507 s x t u).
Proof. exact (MK_COMB (@lem8037027 _142505 _142507) (@lem8037026 _142505 _142506 _142507 s x t u)). Qed.
Lemma lem8037035 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term96 _142505 _142506 _142507 s t u) = (term108 _142505 _142506 _142507 s t u).
Proof. exact (fun_ext (fun x : cart _142505 _142506 => @lem8037028 _142505 _142506 _142507 s x t u)). Qed.
Lemma lem8037036 {_142505 _142506 : Type'} : (@all (cart _142505 _142506)) = (@all (cart _142505 _142506)).
Proof. exact (eq_refl (@all (cart _142505 _142506))). Qed.
Lemma lem8037037 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : (term97 _142505 _142506 _142507 s t u) = (term109 _142505 _142506 _142507 s t u).
Proof. exact (MK_COMB (@lem8037036 _142505 _142506) (@lem8037035 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8037044 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : ((term76 _142505 _142506 _142507 s t u) = (term77 _142505 _142506 _142507 s t u)) = (term109 _142505 _142506 _142507 s t u).
Proof. exact (TRANS (@lem8036966 _142505 _142506 _142507 s t u) (@lem8037037 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8037045 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) : (term110 _142505 _142506 _142507 s t) = (term111 _142505 _142506 _142507 s t).
Proof. exact (fun_ext (fun u : type24 _142505 _142507 => @lem8037044 _142505 _142506 _142507 s t u)). Qed.
Lemma lem8037046 {_142505 _142507 : Type'} : (@all ((cart _142505 _142507) -> Prop)) = (@all ((cart _142505 _142507) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142505 _142507) -> Prop))). Qed.
Lemma lem8037047 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) : (term112 _142505 _142506 _142507 s t) = (term113 _142505 _142506 _142507 s t).
Proof. exact (MK_COMB (@lem8037046 _142505 _142507) (@lem8037045 _142505 _142506 _142507 s t)). Qed.
Lemma lem8037054 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) : (term114 _142505 _142506 _142507 s) = (term115 _142505 _142506 _142507 s).
Proof. exact (fun_ext (fun t : type24 _142505 _142506 => @lem8037047 _142505 _142506 _142507 s t)). Qed.
Lemma lem8037055 {_142505 _142506 : Type'} : (@all ((cart _142505 _142506) -> Prop)) = (@all ((cart _142505 _142506) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142505 _142506) -> Prop))). Qed.
Lemma lem8037056 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) : (term116 _142505 _142506 _142507 s) = (term117 _142505 _142506 _142507 s).
Proof. exact (MK_COMB (@lem8037055 _142505 _142506) (@lem8037054 _142505 _142506 _142507 s)). Qed.
Lemma lem8037063 {_142505 _142506 _142507 : Type'} : (term118 _142505 _142506 _142507) = (term119 _142505 _142506 _142507).
Proof. exact (fun_ext (fun s : type24 _142505 _142506 => @lem8037056 _142505 _142506 _142507 s)). Qed.
Lemma lem8037064 {_142505 _142506 : Type'} : (@all ((cart _142505 _142506) -> Prop)) = (@all ((cart _142505 _142506) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142505 _142506) -> Prop))). Qed.
Lemma lem8037065 {_142505 _142506 _142507 : Type'} : (term120 _142505 _142506 _142507) = (term121 _142505 _142506 _142507).
Proof. exact (MK_COMB (@lem8037064 _142505 _142506) (@lem8037063 _142505 _142506 _142507)). Qed.
Lemma lem8037072 {_142469 _142470 _142471 _142505 _142506 _142507 : Type'} : (term122 _142469 _142470 _142471 _142505 _142506 _142507) = (term123 _142469 _142470 _142471 _142505 _142506 _142507).
Proof. exact (MK_COMB (@lem8036912 _142469 _142470 _142471) (@lem8037065 _142505 _142506 _142507)). Qed.
Lemma lem8037075 {_142469 _142470 _142471 _142505 _142506 _142507 : Type'} : (term123 _142469 _142470 _142471 _142505 _142506 _142507) = (term122 _142469 _142470 _142471 _142505 _142506 _142507).
Proof. exact (SYM (@lem8037072 _142469 _142470 _142471 _142505 _142506 _142507)). Qed.
Lemma lem8037090 {_142469 _142470 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) : term124 _142469 _142470 x s.
Proof. exact (@lem9851 (@IN (cart _142469 _142470) x s)). Qed.
Lemma lem8037091 {_142469 _142470 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) : (term124 _142469 _142470 x s) = (term125 _142469 _142470 x s).
Proof. exact (eq_refl (term124 _142469 _142470 x s)). Qed.
Lemma lem8037092 {_142469 _142470 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) : term125 _142469 _142470 x s.
Proof. exact (EQ_MP (@lem8037091 _142469 _142470 x s) (@lem8037090 _142469 _142470 x s)). Qed.
Lemma lem8037093 {_142469 _142470 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = True) : (@IN (cart _142469 _142470) x s) = True.
Proof. exact (h1). Qed.
Lemma lem8037094 {_142469 _142470 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = False) : (@IN (cart _142469 _142470) x s) = False.
Proof. exact (h1). Qed.
Lemma lem8037109 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term126 _142469 _142471 t y u) = (term126 _142469 _142471 t y u).
Proof. exact (eq_refl (term126 _142469 _142471 t y u)). Qed.
Lemma lem8037110 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = True) : (term127 _142469 _142470 _142471 t y u x s) = (term128 _142469 _142471 t y u).
Proof. exact (MK_COMB (@lem8037109 _142469 _142471 t y u) (@lem8037093 _142469 _142470 x s h1)). Qed.
Lemma lem8037111 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term128 _142469 _142471 t y u) = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)).
Proof. exact (eq_refl (term128 _142469 _142471 t y u)). Qed.
Lemma lem8037112 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) : (term131 _142469 _142470 _142471 t y u x s) = (term131 _142469 _142470 _142471 t y u x s).
Proof. exact (eq_refl (term131 _142469 _142470 _142471 t y u x s)). Qed.
Lemma lem8037113 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term127 _142469 _142470 _142471 t y u x s) = (term128 _142469 _142471 t y u)) = ((term127 _142469 _142470 _142471 t y u x s) = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u))).
Proof. exact (MK_COMB (@lem8037112 _142469 _142470 _142471 t y u x s) (@lem8037111 _142469 _142471 t y u)). Qed.
Lemma lem8037114 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term127 _142469 _142470 _142471 t y u x s) = ((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)).
Proof. exact (eq_refl (term127 _142469 _142470 _142471 t y u x s)). Qed.
Lemma lem8037115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037116 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term131 _142469 _142470 _142471 t y u x s) = (term132 _142469 _142470 _142471 t x s y u).
Proof. exact (MK_COMB (@lem8037115) (@lem8037114 _142469 _142470 _142471 t x s y u)). Qed.
Lemma lem8037117 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)) = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)).
Proof. exact (eq_refl ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u))). Qed.
Lemma lem8037118 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term127 _142469 _142470 _142471 t y u x s) = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u))) = (((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)) = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u))).
Proof. exact (MK_COMB (@lem8037116 _142469 _142470 _142471 t x s y u) (@lem8037117 _142469 _142471 t y u)). Qed.
Lemma lem8037119 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term127 _142469 _142470 _142471 t y u x s) = (term128 _142469 _142471 t y u)) = (((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)) = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u))).
Proof. exact (TRANS (@lem8037113 _142469 _142470 _142471 x s t y u) (@lem8037118 _142469 _142470 _142471 x s t y u)). Qed.
Lemma lem8037120 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = True) : ((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)) = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)).
Proof. exact (EQ_MP (@lem8037119 _142469 _142470 _142471 x s t y u) (@lem8037110 _142469 _142470 _142471 t y u x s h1)). Qed.
Lemma lem8037121 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = True) : ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)) = ((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)).
Proof. exact (SYM (@lem8037120 _142469 _142470 _142471 t y u x s h1)). Qed.
Lemma lem8037122 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term126 _142469 _142471 t y u) = (term126 _142469 _142471 t y u).
Proof. exact (eq_refl (term126 _142469 _142471 t y u)). Qed.
Lemma lem8037123 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = False) : (term127 _142469 _142470 _142471 t y u x s) = (term133 _142469 _142471 t y u).
Proof. exact (MK_COMB (@lem8037122 _142469 _142471 t y u) (@lem8037094 _142469 _142470 x s h1)). Qed.
Lemma lem8037124 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term133 _142469 _142471 t y u) = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)).
Proof. exact (eq_refl (term133 _142469 _142471 t y u)). Qed.
Lemma lem8037125 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) : (term131 _142469 _142470 _142471 t y u x s) = (term131 _142469 _142470 _142471 t y u x s).
Proof. exact (eq_refl (term131 _142469 _142470 _142471 t y u x s)). Qed.
Lemma lem8037126 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term127 _142469 _142470 _142471 t y u x s) = (term133 _142469 _142471 t y u)) = ((term127 _142469 _142470 _142471 t y u x s) = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u))).
Proof. exact (MK_COMB (@lem8037125 _142469 _142470 _142471 t y u x s) (@lem8037124 _142469 _142471 t y u)). Qed.
Lemma lem8037127 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term127 _142469 _142470 _142471 t y u x s) = ((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)).
Proof. exact (eq_refl (term127 _142469 _142470 _142471 t y u x s)). Qed.
Lemma lem8037128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037129 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term131 _142469 _142470 _142471 t y u x s) = (term132 _142469 _142470 _142471 t x s y u).
Proof. exact (MK_COMB (@lem8037128) (@lem8037127 _142469 _142470 _142471 t x s y u)). Qed.
Lemma lem8037130 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)) = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)).
Proof. exact (eq_refl ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u))). Qed.
Lemma lem8037131 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term127 _142469 _142470 _142471 t y u x s) = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u))) = (((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)) = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u))).
Proof. exact (MK_COMB (@lem8037129 _142469 _142470 _142471 t x s y u) (@lem8037130 _142469 _142471 t y u)). Qed.
Lemma lem8037132 {_142469 _142470 _142471 : Type'} (x : cart _142469 _142470) (s : type24 _142469 _142470) (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term127 _142469 _142470 _142471 t y u x s) = (term133 _142469 _142471 t y u)) = (((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)) = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u))).
Proof. exact (TRANS (@lem8037126 _142469 _142470 _142471 x s t y u) (@lem8037131 _142469 _142470 _142471 x s t y u)). Qed.
Lemma lem8037133 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = False) : ((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)) = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)).
Proof. exact (EQ_MP (@lem8037132 _142469 _142470 _142471 x s t y u) (@lem8037123 _142469 _142470 _142471 t y u x s h1)). Qed.
Lemma lem8037134 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = False) : ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)) = ((term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u)).
Proof. exact (SYM (@lem8037133 _142469 _142470 _142471 t y u x s h1)). Qed.
Lemma lem8037138 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037139 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term129 _142469 _142471 t y u) = (term47 _142469 _142471 t y u).
Proof. exact (@lem8037138 (term47 _142469 _142471 t y u)). Qed.
Lemma lem8037142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037143 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term136 _142469 _142471 t y u) = (term137 _142469 _142471 t y u).
Proof. exact (MK_COMB (@lem8037142) (@lem8037139 _142469 _142471 t y u)). Qed.
Lemma lem8037147 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037148 {_142469 _142471 : Type'} (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term138 _142469 _142471 y t) = (@IN (cart _142469 _142471) y t).
Proof. exact (@lem8037147 (@IN (cart _142469 _142471) y t)). Qed.
Lemma lem8037149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037150 {_142469 _142471 : Type'} (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term139 _142469 _142471 y t) = (term48 _142469 _142471 y t).
Proof. exact (MK_COMB (@lem8037149) (@lem8037148 _142469 _142471 y t)). Qed.
Lemma lem8037152 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037153 {_142469 _142471 : Type'} (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term138 _142469 _142471 y u) = (@IN (cart _142469 _142471) y u).
Proof. exact (@lem8037152 (@IN (cart _142469 _142471) y u)). Qed.
Lemma lem8037154 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term130 _142469 _142471 t y u) = (term47 _142469 _142471 t y u).
Proof. exact (MK_COMB (@lem8037150 _142469 _142471 y t) (@lem8037153 _142469 _142471 y u)). Qed.
Lemma lem8037157 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)) = ((term47 _142469 _142471 t y u) = (term47 _142469 _142471 t y u)).
Proof. exact (MK_COMB (@lem8037143 _142469 _142471 t y u) (@lem8037154 _142469 _142471 t y u)). Qed.
Lemma lem8037159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8037160 (x : Prop) : (x = x) = True.
Proof. exact (@lem8037159 Prop x). Qed.
Lemma lem8037161 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term47 _142469 _142471 t y u) = (term47 _142469 _142471 t y u)) = True.
Proof. exact (@lem8037160 (term47 _142469 _142471 t y u)). Qed.
Lemma lem8037162 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)) = True.
Proof. exact (TRANS (@lem8037157 _142469 _142471 t y u) (@lem8037161 _142469 _142471 t y u)). Qed.
Lemma lem8037163 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : True = ((term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u)).
Proof. exact (SYM (@lem8037162 _142469 _142471 t y u)). Qed.
Lemma lem8037164 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term129 _142469 _142471 t y u) = (term130 _142469 _142471 t y u).
Proof. exact (EQ_MP (@lem8037163 _142469 _142471 t y u) (@lem0)). Qed.
Lemma lem8037168 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037169 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term134 _142469 _142471 t y u) = False.
Proof. exact (@lem8037168 (term47 _142469 _142471 t y u)). Qed.
Lemma lem8037170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037171 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term140 _142469 _142471 t y u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8037170) (@lem8037169 _142469 _142471 t y u)). Qed.
Lemma lem8037175 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037176 {_142469 _142471 : Type'} (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term141 _142469 _142471 y t) = False.
Proof. exact (@lem8037175 (@IN (cart _142469 _142471) y t)). Qed.
Lemma lem8037177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037178 {_142469 _142471 : Type'} (y : cart _142469 _142471) (t : type24 _142469 _142471) : (term142 _142469 _142471 y t) = (and False).
Proof. exact (MK_COMB (@lem8037177) (@lem8037176 _142469 _142471 y t)). Qed.
Lemma lem8037180 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037181 {_142469 _142471 : Type'} (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term141 _142469 _142471 y u) = False.
Proof. exact (@lem8037180 (@IN (cart _142469 _142471) y u)). Qed.
Lemma lem8037182 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term135 _142469 _142471 t y u) = (False /\ False).
Proof. exact (MK_COMB (@lem8037178 _142469 _142471 y t) (@lem8037181 _142469 _142471 y u)). Qed.
Lemma lem8037184 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037185 : (False /\ False) = False.
Proof. exact (@lem8037184 False). Qed.
Lemma lem8037186 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term135 _142469 _142471 t y u) = False.
Proof. exact (TRANS (@lem8037182 _142469 _142471 t y u) (@lem8037185)). Qed.
Lemma lem8037187 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)) = (False = False).
Proof. exact (MK_COMB (@lem8037171 _142469 _142471 t y u) (@lem8037186 _142469 _142471 t y u)). Qed.
Lemma lem8037189 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8037190 : (False = False) = (~ False).
Proof. exact (@lem8037189 False). Qed.
Lemma lem8037192 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8037193 : (False = False) = True.
Proof. exact (TRANS (@lem8037190) (@lem8037192)). Qed.
Lemma lem8037194 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)) = True.
Proof. exact (TRANS (@lem8037187 _142469 _142471 t y u) (@lem8037193)). Qed.
Lemma lem8037195 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : True = ((term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u)).
Proof. exact (SYM (@lem8037194 _142469 _142471 t y u)). Qed.
Lemma lem8037196 {_142469 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term134 _142469 _142471 t y u) = (term135 _142469 _142471 t y u).
Proof. exact (EQ_MP (@lem8037195 _142469 _142471 t y u) (@lem0)). Qed.
Lemma lem8037197 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = False) : (term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u).
Proof. exact (EQ_MP (@lem8037134 _142469 _142470 _142471 t y u x s h1) (@lem8037196 _142469 _142471 t y u)). Qed.
Lemma lem8037198 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (y : cart _142469 _142471) (u : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (h1 : (@IN (cart _142469 _142470) x s) = True) : (term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u).
Proof. exact (EQ_MP (@lem8037121 _142469 _142470 _142471 t y u x s h1) (@lem8037164 _142469 _142471 t y u)). Qed.
Lemma lem8037201 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (y : cart _142469 _142471) (u : type24 _142469 _142471) : (term49 _142469 _142470 _142471 x s t y u) = (term57 _142469 _142470 _142471 t x s y u).
Proof. exact (or_elim (@lem8037092 _142469 _142470 x s) (fun h0 : (@IN (cart _142469 _142470) x s) = True => @lem8037198 _142469 _142470 _142471 t y u x s h0) (fun h0 : (@IN (cart _142469 _142470) x s) = False => @lem8037197 _142469 _142470 _142471 t y u x s h0)). Qed.
Lemma lem8037216 {_142505 _142506 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) : term124 _142505 _142506 x s.
Proof. exact (@lem9851 (@IN (cart _142505 _142506) x s)). Qed.
Lemma lem8037217 {_142505 _142506 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) : (term124 _142505 _142506 x s) = (term125 _142505 _142506 x s).
Proof. exact (eq_refl (term124 _142505 _142506 x s)). Qed.
Lemma lem8037218 {_142505 _142506 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) : term125 _142505 _142506 x s.
Proof. exact (EQ_MP (@lem8037217 _142505 _142506 x s) (@lem8037216 _142505 _142506 x s)). Qed.
Lemma lem8037219 {_142505 _142506 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = True) : (@IN (cart _142505 _142506) x s) = True.
Proof. exact (h1). Qed.
Lemma lem8037220 {_142505 _142506 : Type'} (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = False) : (@IN (cart _142505 _142506) x s) = False.
Proof. exact (h1). Qed.
Lemma lem8037235 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term143 _142505 _142506 _142507 x t y u) = (term143 _142505 _142506 _142507 x t y u).
Proof. exact (eq_refl (term143 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037236 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = True) : (term144 _142505 _142506 _142507 t y u x s) = (term145 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037235 _142505 _142506 _142507 x t y u) (@lem8037219 _142505 _142506 x s h1)). Qed.
Lemma lem8037237 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term145 _142505 _142506 _142507 x t y u) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u)).
Proof. exact (eq_refl (term145 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037238 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) : (term148 _142505 _142506 _142507 t y u x s) = (term148 _142505 _142506 _142507 t y u x s).
Proof. exact (eq_refl (term148 _142505 _142506 _142507 t y u x s)). Qed.
Lemma lem8037239 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term144 _142505 _142506 _142507 t y u x s) = (term145 _142505 _142506 _142507 x t y u)) = ((term144 _142505 _142506 _142507 t y u x s) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u))).
Proof. exact (MK_COMB (@lem8037238 _142505 _142506 _142507 t y u x s) (@lem8037237 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037240 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term144 _142505 _142506 _142507 t y u x s) = ((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)).
Proof. exact (eq_refl (term144 _142505 _142506 _142507 t y u x s)). Qed.
Lemma lem8037241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037242 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term148 _142505 _142506 _142507 t y u x s) = (term149 _142505 _142506 _142507 s x t y u).
Proof. exact (MK_COMB (@lem8037241) (@lem8037240 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8037243 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u)) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u)).
Proof. exact (eq_refl ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u))). Qed.
Lemma lem8037244 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term144 _142505 _142506 _142507 t y u x s) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u))) = (((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u))).
Proof. exact (MK_COMB (@lem8037242 _142505 _142506 _142507 s x t y u) (@lem8037243 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037245 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term144 _142505 _142506 _142507 t y u x s) = (term145 _142505 _142506 _142507 x t y u)) = (((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u))).
Proof. exact (TRANS (@lem8037239 _142505 _142506 _142507 s x t y u) (@lem8037244 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8037246 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = True) : ((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u)).
Proof. exact (EQ_MP (@lem8037245 _142505 _142506 _142507 s x t y u) (@lem8037236 _142505 _142506 _142507 t y u x s h1)). Qed.
Lemma lem8037247 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = True) : ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u)) = ((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)).
Proof. exact (SYM (@lem8037246 _142505 _142506 _142507 t y u x s h1)). Qed.
Lemma lem8037248 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term143 _142505 _142506 _142507 x t y u) = (term143 _142505 _142506 _142507 x t y u).
Proof. exact (eq_refl (term143 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037249 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = False) : (term144 _142505 _142506 _142507 t y u x s) = (term150 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037248 _142505 _142506 _142507 x t y u) (@lem8037220 _142505 _142506 x s h1)). Qed.
Lemma lem8037250 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term150 _142505 _142506 _142507 x t y u) = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)).
Proof. exact (eq_refl (term150 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037251 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) : (term148 _142505 _142506 _142507 t y u x s) = (term148 _142505 _142506 _142507 t y u x s).
Proof. exact (eq_refl (term148 _142505 _142506 _142507 t y u x s)). Qed.
Lemma lem8037252 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term144 _142505 _142506 _142507 t y u x s) = (term150 _142505 _142506 _142507 x t y u)) = ((term144 _142505 _142506 _142507 t y u x s) = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u))).
Proof. exact (MK_COMB (@lem8037251 _142505 _142506 _142507 t y u x s) (@lem8037250 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037253 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term144 _142505 _142506 _142507 t y u x s) = ((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)).
Proof. exact (eq_refl (term144 _142505 _142506 _142507 t y u x s)). Qed.
Lemma lem8037254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037255 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term148 _142505 _142506 _142507 t y u x s) = (term149 _142505 _142506 _142507 s x t y u).
Proof. exact (MK_COMB (@lem8037254) (@lem8037253 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8037256 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)) = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)).
Proof. exact (eq_refl ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u))). Qed.
Lemma lem8037257 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term144 _142505 _142506 _142507 t y u x s) = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u))) = (((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)) = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u))).
Proof. exact (MK_COMB (@lem8037255 _142505 _142506 _142507 s x t y u) (@lem8037256 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037258 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term144 _142505 _142506 _142507 t y u x s) = (term150 _142505 _142506 _142507 x t y u)) = (((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)) = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u))).
Proof. exact (TRANS (@lem8037252 _142505 _142506 _142507 s x t y u) (@lem8037257 _142505 _142506 _142507 s x t y u)). Qed.
Lemma lem8037259 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = False) : ((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)) = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)).
Proof. exact (EQ_MP (@lem8037258 _142505 _142506 _142507 s x t y u) (@lem8037249 _142505 _142506 _142507 t y u x s h1)). Qed.
Lemma lem8037260 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = False) : ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)) = ((term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u)).
Proof. exact (SYM (@lem8037259 _142505 _142506 _142507 t y u x s h1)). Qed.
Lemma lem8037266 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037267 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term138 _142505 _142506 x t) = (@IN (cart _142505 _142506) x t).
Proof. exact (@lem8037266 (@IN (cart _142505 _142506) x t)). Qed.
Lemma lem8037268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037269 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term139 _142505 _142506 x t) = (term48 _142505 _142506 x t).
Proof. exact (MK_COMB (@lem8037268) (@lem8037267 _142505 _142506 x t)). Qed.
Lemma lem8037270 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (@IN (cart _142505 _142507) y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (eq_refl (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037271 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term146 _142505 _142506 _142507 x t y u) = (term8 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037269 _142505 _142506 x t) (@lem8037270 _142505 _142507 y u)). Qed.
Lemma lem8037274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037275 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term153 _142505 _142506 _142507 x t y u) = (term154 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037274) (@lem8037271 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037279 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037280 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term138 _142505 _142507 y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (@lem8037279 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037282 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term139 _142505 _142507 y u) = (term48 _142505 _142507 y u).
Proof. exact (MK_COMB (@lem8037281) (@lem8037280 _142505 _142507 y u)). Qed.
Lemma lem8037285 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term8 _142505 _142506 _142507 x t y u) = (term8 _142505 _142506 _142507 x t y u).
Proof. exact (eq_refl (term8 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037286 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term147 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037282 _142505 _142507 y u) (@lem8037285 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037289 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u)) = ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)).
Proof. exact (MK_COMB (@lem8037275 _142505 _142506 _142507 x t y u) (@lem8037286 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037292 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)) = ((term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u)).
Proof. exact (SYM (@lem8037289 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037293 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) : term124 _142505 _142506 x t.
Proof. exact (@lem9851 (@IN (cart _142505 _142506) x t)). Qed.
Lemma lem8037294 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term124 _142505 _142506 x t) = (term125 _142505 _142506 x t).
Proof. exact (eq_refl (term124 _142505 _142506 x t)). Qed.
Lemma lem8037295 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) : term125 _142505 _142506 x t.
Proof. exact (EQ_MP (@lem8037294 _142505 _142506 x t) (@lem8037293 _142505 _142506 x t)). Qed.
Lemma lem8037296 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = True) : (@IN (cart _142505 _142506) x t) = True.
Proof. exact (h1). Qed.
Lemma lem8037297 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = False) : (@IN (cart _142505 _142506) x t) = False.
Proof. exact (h1). Qed.
Lemma lem8037308 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term156 _142505 _142507 y u) = (term156 _142505 _142507 y u).
Proof. exact (eq_refl (term156 _142505 _142507 y u)). Qed.
Lemma lem8037309 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = True) : (term157 _142505 _142506 _142507 y u x t) = (term158 _142505 _142507 y u).
Proof. exact (MK_COMB (@lem8037308 _142505 _142507 y u) (@lem8037296 _142505 _142506 x t h1)). Qed.
Lemma lem8037310 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term158 _142505 _142507 y u) = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)).
Proof. exact (eq_refl (term158 _142505 _142507 y u)). Qed.
Lemma lem8037311 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term160 _142505 _142506 _142507 y u x t) = (term160 _142505 _142506 _142507 y u x t).
Proof. exact (eq_refl (term160 _142505 _142506 _142507 y u x t)). Qed.
Lemma lem8037312 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term157 _142505 _142506 _142507 y u x t) = (term158 _142505 _142507 y u)) = ((term157 _142505 _142506 _142507 y u x t) = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u))).
Proof. exact (MK_COMB (@lem8037311 _142505 _142506 _142507 y u x t) (@lem8037310 _142505 _142507 y u)). Qed.
Lemma lem8037313 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term157 _142505 _142506 _142507 y u x t) = ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)).
Proof. exact (eq_refl (term157 _142505 _142506 _142507 y u x t)). Qed.
Lemma lem8037314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037315 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term160 _142505 _142506 _142507 y u x t) = (term161 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037314) (@lem8037313 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037316 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)) = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)).
Proof. exact (eq_refl ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u))). Qed.
Lemma lem8037317 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term157 _142505 _142506 _142507 y u x t) = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u))) = (((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)) = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u))).
Proof. exact (MK_COMB (@lem8037315 _142505 _142506 _142507 x t y u) (@lem8037316 _142505 _142507 y u)). Qed.
Lemma lem8037318 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term157 _142505 _142506 _142507 y u x t) = (term158 _142505 _142507 y u)) = (((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)) = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u))).
Proof. exact (TRANS (@lem8037312 _142505 _142506 _142507 x t y u) (@lem8037317 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037319 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = True) : ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)) = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)).
Proof. exact (EQ_MP (@lem8037318 _142505 _142506 _142507 x t y u) (@lem8037309 _142505 _142506 _142507 y u x t h1)). Qed.
Lemma lem8037320 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = True) : ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)) = ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)).
Proof. exact (SYM (@lem8037319 _142505 _142506 _142507 y u x t h1)). Qed.
Lemma lem8037321 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term156 _142505 _142507 y u) = (term156 _142505 _142507 y u).
Proof. exact (eq_refl (term156 _142505 _142507 y u)). Qed.
Lemma lem8037322 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = False) : (term157 _142505 _142506 _142507 y u x t) = (term162 _142505 _142507 y u).
Proof. exact (MK_COMB (@lem8037321 _142505 _142507 y u) (@lem8037297 _142505 _142506 x t h1)). Qed.
Lemma lem8037323 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term162 _142505 _142507 y u) = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)).
Proof. exact (eq_refl (term162 _142505 _142507 y u)). Qed.
Lemma lem8037324 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term160 _142505 _142506 _142507 y u x t) = (term160 _142505 _142506 _142507 y u x t).
Proof. exact (eq_refl (term160 _142505 _142506 _142507 y u x t)). Qed.
Lemma lem8037325 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term157 _142505 _142506 _142507 y u x t) = (term162 _142505 _142507 y u)) = ((term157 _142505 _142506 _142507 y u x t) = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u))).
Proof. exact (MK_COMB (@lem8037324 _142505 _142506 _142507 y u x t) (@lem8037323 _142505 _142507 y u)). Qed.
Lemma lem8037326 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term157 _142505 _142506 _142507 y u x t) = ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)).
Proof. exact (eq_refl (term157 _142505 _142506 _142507 y u x t)). Qed.
Lemma lem8037327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037328 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term160 _142505 _142506 _142507 y u x t) = (term161 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037327) (@lem8037326 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037329 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)) = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)).
Proof. exact (eq_refl ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u))). Qed.
Lemma lem8037330 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term157 _142505 _142506 _142507 y u x t) = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u))) = (((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)) = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u))).
Proof. exact (MK_COMB (@lem8037328 _142505 _142506 _142507 x t y u) (@lem8037329 _142505 _142507 y u)). Qed.
Lemma lem8037331 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term157 _142505 _142506 _142507 y u x t) = (term162 _142505 _142507 y u)) = (((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)) = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u))).
Proof. exact (TRANS (@lem8037325 _142505 _142506 _142507 x t y u) (@lem8037330 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037332 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = False) : ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)) = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)).
Proof. exact (EQ_MP (@lem8037331 _142505 _142506 _142507 x t y u) (@lem8037322 _142505 _142506 _142507 y u x t h1)). Qed.
Lemma lem8037333 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = False) : ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)) = ((term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u)).
Proof. exact (SYM (@lem8037332 _142505 _142506 _142507 y u x t h1)). Qed.
Lemma lem8037337 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037338 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term138 _142505 _142507 y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (@lem8037337 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037340 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term164 _142505 _142507 y u) = (term165 _142505 _142507 y u).
Proof. exact (MK_COMB (@lem8037339) (@lem8037338 _142505 _142507 y u)). Qed.
Lemma lem8037344 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8037345 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term138 _142505 _142507 y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (@lem8037344 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037346 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term48 _142505 _142507 y u) = (term48 _142505 _142507 y u).
Proof. exact (eq_refl (term48 _142505 _142507 y u)). Qed.
Lemma lem8037347 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term159 _142505 _142507 y u) = (term166 _142505 _142507 y u).
Proof. exact (MK_COMB (@lem8037346 _142505 _142507 y u) (@lem8037345 _142505 _142507 y u)). Qed.
Lemma lem8037349 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem8037350 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term166 _142505 _142507 y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (@lem8037349 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037351 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term159 _142505 _142507 y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (TRANS (@lem8037347 _142505 _142507 y u) (@lem8037350 _142505 _142507 y u)). Qed.
Lemma lem8037352 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)) = ((@IN (cart _142505 _142507) y u) = (@IN (cart _142505 _142507) y u)).
Proof. exact (MK_COMB (@lem8037340 _142505 _142507 y u) (@lem8037351 _142505 _142507 y u)). Qed.
Lemma lem8037354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8037355 (x : Prop) : (x = x) = True.
Proof. exact (@lem8037354 Prop x). Qed.
Lemma lem8037356 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((@IN (cart _142505 _142507) y u) = (@IN (cart _142505 _142507) y u)) = True.
Proof. exact (@lem8037355 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037357 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)) = True.
Proof. exact (TRANS (@lem8037352 _142505 _142507 y u) (@lem8037356 _142505 _142507 y u)). Qed.
Lemma lem8037358 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : True = ((term138 _142505 _142507 y u) = (term159 _142505 _142507 y u)).
Proof. exact (SYM (@lem8037357 _142505 _142507 y u)). Qed.
Lemma lem8037359 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term138 _142505 _142507 y u) = (term159 _142505 _142507 y u).
Proof. exact (EQ_MP (@lem8037358 _142505 _142507 y u) (@lem0)). Qed.
Lemma lem8037363 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037364 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term141 _142505 _142507 y u) = False.
Proof. exact (@lem8037363 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037366 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term167 _142505 _142507 y u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8037365) (@lem8037364 _142505 _142507 y u)). Qed.
Lemma lem8037370 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037371 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term141 _142505 _142507 y u) = False.
Proof. exact (@lem8037370 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037372 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term48 _142505 _142507 y u) = (term48 _142505 _142507 y u).
Proof. exact (eq_refl (term48 _142505 _142507 y u)). Qed.
Lemma lem8037373 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term163 _142505 _142507 y u) = (term168 _142505 _142507 y u).
Proof. exact (MK_COMB (@lem8037372 _142505 _142507 y u) (@lem8037371 _142505 _142507 y u)). Qed.
Lemma lem8037375 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem8037376 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term168 _142505 _142507 y u) = False.
Proof. exact (@lem8037375 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037377 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term163 _142505 _142507 y u) = False.
Proof. exact (TRANS (@lem8037373 _142505 _142507 y u) (@lem8037376 _142505 _142507 y u)). Qed.
Lemma lem8037378 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)) = (False = False).
Proof. exact (MK_COMB (@lem8037366 _142505 _142507 y u) (@lem8037377 _142505 _142507 y u)). Qed.
Lemma lem8037380 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8037381 : (False = False) = (~ False).
Proof. exact (@lem8037380 False). Qed.
Lemma lem8037383 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8037384 : (False = False) = True.
Proof. exact (TRANS (@lem8037381) (@lem8037383)). Qed.
Lemma lem8037385 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)) = True.
Proof. exact (TRANS (@lem8037378 _142505 _142507 y u) (@lem8037384)). Qed.
Lemma lem8037386 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : True = ((term141 _142505 _142507 y u) = (term163 _142505 _142507 y u)).
Proof. exact (SYM (@lem8037385 _142505 _142507 y u)). Qed.
Lemma lem8037387 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term141 _142505 _142507 y u) = (term163 _142505 _142507 y u).
Proof. exact (EQ_MP (@lem8037386 _142505 _142507 y u) (@lem0)). Qed.
Lemma lem8037388 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = False) : (term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u).
Proof. exact (EQ_MP (@lem8037333 _142505 _142506 _142507 y u x t h1) (@lem8037387 _142505 _142507 y u)). Qed.
Lemma lem8037389 {_142505 _142506 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (t : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x t) = True) : (term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u).
Proof. exact (EQ_MP (@lem8037320 _142505 _142506 _142507 y u x t h1) (@lem8037359 _142505 _142507 y u)). Qed.
Lemma lem8037391 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term8 _142505 _142506 _142507 x t y u) = (term155 _142505 _142506 _142507 x t y u).
Proof. exact (or_elim (@lem8037295 _142505 _142506 x t) (fun h0 : (@IN (cart _142505 _142506) x t) = True => @lem8037389 _142505 _142506 _142507 y u x t h0) (fun h0 : (@IN (cart _142505 _142506) x t) = False => @lem8037388 _142505 _142506 _142507 y u x t h0)). Qed.
Lemma lem8037392 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term146 _142505 _142506 _142507 x t y u) = (term147 _142505 _142506 _142507 x t y u).
Proof. exact (EQ_MP (@lem8037292 _142505 _142506 _142507 x t y u) (@lem8037391 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037398 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037399 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term141 _142505 _142506 x t) = False.
Proof. exact (@lem8037398 (@IN (cart _142505 _142506) x t)). Qed.
Lemma lem8037400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037401 {_142505 _142506 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) : (term142 _142505 _142506 x t) = (and False).
Proof. exact (MK_COMB (@lem8037400) (@lem8037399 _142505 _142506 x t)). Qed.
Lemma lem8037402 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (@IN (cart _142505 _142507) y u) = (@IN (cart _142505 _142507) y u).
Proof. exact (eq_refl (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037403 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term151 _142505 _142506 _142507 x t y u) = (term141 _142505 _142507 y u).
Proof. exact (MK_COMB (@lem8037401 _142505 _142506 x t) (@lem8037402 _142505 _142507 y u)). Qed.
Lemma lem8037405 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037406 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term141 _142505 _142507 y u) = False.
Proof. exact (@lem8037405 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037407 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term151 _142505 _142506 _142507 x t y u) = False.
Proof. exact (TRANS (@lem8037403 _142505 _142506 _142507 x t y u) (@lem8037406 _142505 _142507 y u)). Qed.
Lemma lem8037408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8037409 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term169 _142505 _142506 _142507 x t y u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8037408) (@lem8037407 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037413 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037414 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term141 _142505 _142507 y u) = False.
Proof. exact (@lem8037413 (@IN (cart _142505 _142507) y u)). Qed.
Lemma lem8037415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8037416 {_142505 _142507 : Type'} (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term142 _142505 _142507 y u) = (and False).
Proof. exact (MK_COMB (@lem8037415) (@lem8037414 _142505 _142507 y u)). Qed.
Lemma lem8037419 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term8 _142505 _142506 _142507 x t y u) = (term8 _142505 _142506 _142507 x t y u).
Proof. exact (eq_refl (term8 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037420 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term152 _142505 _142506 _142507 x t y u) = (term170 _142505 _142506 _142507 x t y u).
Proof. exact (MK_COMB (@lem8037416 _142505 _142507 y u) (@lem8037419 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037422 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8037423 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term170 _142505 _142506 _142507 x t y u) = False.
Proof. exact (@lem8037422 (term8 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037424 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term152 _142505 _142506 _142507 x t y u) = False.
Proof. exact (TRANS (@lem8037420 _142505 _142506 _142507 x t y u) (@lem8037423 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037425 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)) = (False = False).
Proof. exact (MK_COMB (@lem8037409 _142505 _142506 _142507 x t y u) (@lem8037424 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037427 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8037428 : (False = False) = (~ False).
Proof. exact (@lem8037427 False). Qed.
Lemma lem8037430 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8037431 : (False = False) = True.
Proof. exact (TRANS (@lem8037428) (@lem8037430)). Qed.
Lemma lem8037432 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)) = True.
Proof. exact (TRANS (@lem8037425 _142505 _142506 _142507 x t y u) (@lem8037431)). Qed.
Lemma lem8037433 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : True = ((term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u)).
Proof. exact (SYM (@lem8037432 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037434 {_142505 _142506 _142507 : Type'} (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term151 _142505 _142506 _142507 x t y u) = (term152 _142505 _142506 _142507 x t y u).
Proof. exact (EQ_MP (@lem8037433 _142505 _142506 _142507 x t y u) (@lem0)). Qed.
Lemma lem8037435 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = False) : (term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u).
Proof. exact (EQ_MP (@lem8037260 _142505 _142506 _142507 t y u x s h1) (@lem8037434 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037436 {_142505 _142506 _142507 : Type'} (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) (x : cart _142505 _142506) (s : type24 _142505 _142506) (h1 : (@IN (cart _142505 _142506) x s) = True) : (term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u).
Proof. exact (EQ_MP (@lem8037247 _142505 _142506 _142507 t y u x s h1) (@lem8037392 _142505 _142506 _142507 x t y u)). Qed.
Lemma lem8037439 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (y : cart _142505 _142507) (u : type24 _142505 _142507) : (term101 _142505 _142506 _142507 s x t y u) = (term105 _142505 _142506 _142507 s x t y u).
Proof. exact (or_elim (@lem8037218 _142505 _142506 x s) (fun h0 : (@IN (cart _142505 _142506) x s) = True => @lem8037436 _142505 _142506 _142507 t y u x s h0) (fun h0 : (@IN (cart _142505 _142506) x s) = False => @lem8037435 _142505 _142506 _142507 t y u x s h0)). Qed.
Lemma lem8037444 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (x : cart _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : term107 _142505 _142506 _142507 s x t u.
Proof. exact (fun y : cart _142505 _142507 => @lem8037439 _142505 _142506 _142507 s x t y u). Qed.
Lemma lem8037449 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) (u : type24 _142505 _142507) : term109 _142505 _142506 _142507 s t u.
Proof. exact (fun x : cart _142505 _142506 => @lem8037444 _142505 _142506 _142507 s x t u). Qed.
Lemma lem8037454 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) (t : type24 _142505 _142506) : term113 _142505 _142506 _142507 s t.
Proof. exact (fun u : type24 _142505 _142507 => @lem8037449 _142505 _142506 _142507 s t u). Qed.
Lemma lem8037459 {_142505 _142506 _142507 : Type'} (s : type24 _142505 _142506) : term117 _142505 _142506 _142507 s.
Proof. exact (fun t : type24 _142505 _142506 => @lem8037454 _142505 _142506 _142507 s t). Qed.
Lemma lem8037464 {_142505 _142506 _142507 : Type'} : term121 _142505 _142506 _142507.
Proof. exact (fun s : type24 _142505 _142506 => @lem8037459 _142505 _142506 _142507 s). Qed.
Lemma lem8037469 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (x : cart _142469 _142470) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : term59 _142469 _142470 _142471 t x s u.
Proof. exact (fun y : cart _142469 _142471 => @lem8037201 _142469 _142470 _142471 t x s y u). Qed.
Lemma lem8037474 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) (u : type24 _142469 _142471) : term61 _142469 _142470 _142471 t s u.
Proof. exact (fun x : cart _142469 _142470 => @lem8037469 _142469 _142470 _142471 t x s u). Qed.
Lemma lem8037479 {_142469 _142470 _142471 : Type'} (t : type24 _142469 _142471) (s : type24 _142469 _142470) : term65 _142469 _142470 _142471 t s.
Proof. exact (fun u : type24 _142469 _142471 => @lem8037474 _142469 _142470 _142471 t s u). Qed.
Lemma lem8037484 {_142469 _142470 _142471 : Type'} (s : type24 _142469 _142470) : term69 _142469 _142470 _142471 s.
Proof. exact (fun t : type24 _142469 _142471 => @lem8037479 _142469 _142470 _142471 t s). Qed.
Lemma lem8037489 {_142469 _142470 _142471 : Type'} : term73 _142469 _142470 _142471.
Proof. exact (fun s : type24 _142469 _142470 => @lem8037484 _142469 _142470 _142471 s). Qed.
Lemma lem8037490 {_142469 _142470 _142471 _142505 _142506 _142507 : Type'} : term123 _142469 _142470 _142471 _142505 _142506 _142507.
Proof. exact (conj (@lem8037489 _142469 _142470 _142471) (@lem8037464 _142505 _142506 _142507)). Qed.
Lemma lem8037491 {_142469 _142470 _142471 _142505 _142506 _142507 : Type'} : term122 _142469 _142470 _142471 _142505 _142506 _142507.
Proof. exact (EQ_MP (@lem8037075 _142469 _142470 _142471 _142505 _142506 _142507) (@lem8037490 _142469 _142470 _142471 _142505 _142506 _142507)). Qed.
