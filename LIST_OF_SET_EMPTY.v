Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LIST_OF_SET_EMPTY_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_EMPTY_spec.
Require Import LENGTH_EQ_NIL_spec.
Require Import LENGTH_LIST_OF_SET_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem4790594 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4790596 {_110321 : Type'} (s : _110321 -> Prop) : term0 _110321 s.
Proof. exact (@lem4788175 _110321 s). Qed.
Lemma lem4790597 {_110321 : Type'} (s : _110321 -> Prop) : (term0 _110321 s) = (term1 _110321 s).
Proof. exact (eq_refl (term0 _110321 s)). Qed.
Lemma lem4790598 {_110321 : Type'} (s : _110321 -> Prop) : term1 _110321 s.
Proof. exact (EQ_MP (@lem4790597 _110321 s) (@lem4790596 _110321 s)). Qed.
Lemma lem4790599 {_110321 : Type'} (s : _110321 -> Prop) (h1 : @FINITE _110321 s) : @FINITE _110321 s.
Proof. exact (h1). Qed.
Lemma lem4790600 {_110321 : Type'} (s : _110321 -> Prop) (h1 : @FINITE _110321 s) : (term2 _110321 s) = (@CARD _110321 s).
Proof. exact (@lem4790598 _110321 s (@lem4790599 _110321 s h1)). Qed.
Lemma lem4790607 {A : Type'} (l : list A) (h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (h1). Qed.
Lemma lem4790608 {A : Type'} (l : list A) (h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (SYM (@lem4790607 A l h1)). Qed.
Lemma lem4790609 {A : Type'} (l : list A) (h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (h1). Qed.
Lemma lem4790610 {A : Type'} (l : list A) (h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (SYM (@lem4790609 A l h1)). Qed.
Lemma lem4790611 {A : Type'} (l : list A) : (((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) = ((l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))).
Proof. exact (prop_ext (fun h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)) => @lem4790608 A l h1) (fun h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)) => @lem4790610 A l h1)). Qed.
Lemma lem4790612 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (fun_ext (fun l : list A => @lem4790611 A l)). Qed.
Lemma lem4790613 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4790614 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem4790613 A) (@lem4790612 A)). Qed.
Lemma lem4790615 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem4790614 A) (@lem1117066 A)). Qed.
Lemma lem4790616 {A : Type'} (l : list A) : term7 A l.
Proof. exact (@lem4790615 A l). Qed.
Lemma lem4790617 {A : Type'} (l : list A) : (term7 A l) = ((l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))).
Proof. exact (eq_refl (term7 A l)). Qed.
Lemma lem4790620 {A : Type'} (l : list A) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem4790617 A l) (@lem4790616 A l)). Qed.
Lemma lem4790621 {_110458 : Type'} (l : list _110458) : (l = (@nil _110458)) = ((@List.length _110458 l) = (NUMERAL 0)).
Proof. exact (@lem4790620 _110458 l). Qed.
Lemma lem4790622 {_110458 : Type'} : ((@list_of_set _110458 (@EMPTY _110458)) = (@nil _110458)) = ((term8 _110458) = (NUMERAL 0)).
Proof. exact (@lem4790621 _110458 (@list_of_set _110458 (@EMPTY _110458))). Qed.
Lemma lem4790625 {_110458 : Type'} : ((term8 _110458) = (NUMERAL 0)) = ((@list_of_set _110458 (@EMPTY _110458)) = (@nil _110458)).
Proof. exact (SYM (@lem4790622 _110458)). Qed.
Lemma lem4790629 {_110321 : Type'} (s : _110321 -> Prop) : term1 _110321 s.
Proof. exact (fun h0 : @FINITE _110321 s => @lem4790600 _110321 s h0). Qed.
Lemma lem4790630 {_110458 : Type'} (s : _110458 -> Prop) : term1 _110458 s.
Proof. exact (@lem4790629 _110458 s). Qed.
Lemma lem4790631 {_110458 : Type'} : term9 _110458.
Proof. exact (@lem4790630 _110458 (@EMPTY _110458)). Qed.
Lemma lem4790633 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4790594 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4790634 {_110458 : Type'} : (@FINITE _110458 (@EMPTY _110458)) = True.
Proof. exact (@lem4790633 _110458). Qed.
Lemma lem4790635 {_110458 : Type'} : True = (@FINITE _110458 (@EMPTY _110458)).
Proof. exact (SYM (@lem4790634 _110458)). Qed.
Lemma lem4790636 {_110458 : Type'} : @FINITE _110458 (@EMPTY _110458).
Proof. exact (EQ_MP (@lem4790635 _110458) (@lem0)). Qed.
Lemma lem4790637 {_110458 : Type'} : (term8 _110458) = (@CARD _110458 (@EMPTY _110458)).
Proof. exact (@lem4790631 _110458 (@lem4790636 _110458)). Qed.
Lemma lem4790639 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4790640 {_110458 : Type'} : (@CARD _110458 (@EMPTY _110458)) = (NUMERAL 0).
Proof. exact (@lem4790639 _110458). Qed.
Lemma lem4790641 {_110458 : Type'} : (term8 _110458) = (NUMERAL 0).
Proof. exact (TRANS (@lem4790637 _110458) (@lem4790640 _110458)). Qed.
Lemma lem4790642 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4790643 {_110458 : Type'} : (term10 _110458) = term11.
Proof. exact (MK_COMB (@lem4790642) (@lem4790641 _110458)). Qed.
Lemma lem4790644 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem4790645 {_110458 : Type'} : ((term8 _110458) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem4790643 _110458) (@lem4790644)). Qed.
Lemma lem4790647 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4790648 (x : nat) : (x = x) = True.
Proof. exact (@lem4790647 nat x). Qed.
Lemma lem4790649 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem4790648 (NUMERAL 0)). Qed.
Lemma lem4790650 {_110458 : Type'} : ((term8 _110458) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem4790645 _110458) (@lem4790649)). Qed.
Lemma lem4790651 {_110458 : Type'} : True = ((term8 _110458) = (NUMERAL 0)).
Proof. exact (SYM (@lem4790650 _110458)). Qed.
Lemma lem4790652 {_110458 : Type'} : (term8 _110458) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem4790651 _110458) (@lem0)). Qed.
Lemma lem4790653 {_110458 : Type'} : (@list_of_set _110458 (@EMPTY _110458)) = (@nil _110458).
Proof. exact (EQ_MP (@lem4790625 _110458) (@lem4790652 _110458)). Qed.
