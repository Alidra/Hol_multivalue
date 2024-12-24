Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import list_INDUCT_term_abbrevs.
Require Import thm1070927_spec.
Require Import thm1070928_spec.
Require Import thm1070978_spec.
Require Import thm1070982_spec.
Require Import thm1071333_spec.
Require Import thm1071695_spec.
Lemma lem1071696 {A : Type'} (P : type1143 A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term1 A NIL' CONS' list' P.
Proof. exact (@lem1070928 A list' NIL' CONS' h1 (term2 A list' P)). Qed.
Lemma lem1071697 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (P : type1143 A) : (term1 A NIL' CONS' list' P) = (term3 A NIL' CONS' list' P).
Proof. exact (eq_refl (term1 A NIL' CONS' list' P)). Qed.
Lemma lem1071698 {A : Type'} (P : type1143 A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term3 A NIL' CONS' list' P.
Proof. exact (EQ_MP (@lem1071697 A NIL' CONS' list' P) (@lem1071696 A P list' NIL' CONS' h1)). Qed.
Lemma lem1071699 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term4 A list' CONS'.
Proof. exact (proj2 (@lem1070927 A list' NIL' CONS' h1)). Qed.
Lemma lem1071703 {A : Type'} (list' : type1338 A) (P : type1143 A) (NIL' : recspace A) : (term5 A list' P NIL') = (term6 A list' P NIL').
Proof. exact (eq_refl (term5 A list' P NIL')). Qed.
Lemma lem1071705 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : list' NIL'.
Proof. exact (proj1 (@lem1070927 A list' NIL' CONS' h1)). Qed.
Lemma lem1071707 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term7 A)) : (@_mk_list A NIL') = (@nil A).
Proof. exact (SYM (@lem1071333 A NIL' h1)). Qed.
Lemma lem1071708 {A : Type'} (P : type1143 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1071709 {A : Type'} (P : type1143 A) (NIL' : recspace A) (h1 : NIL' = (term7 A)) : (term8 A P NIL') = (P (@nil A)).
Proof. exact (MK_COMB (@lem1071708 A P) (@lem1071707 A NIL' h1)). Qed.
Lemma lem1071710 {A : Type'} (list' : type1338 A) (NIL' : recspace A) : (term9 A list' NIL') = (term9 A list' NIL').
Proof. exact (eq_refl (term9 A list' NIL')). Qed.
Lemma lem1071711 {A : Type'} (list' : type1338 A) (P : type1143 A) (NIL' : recspace A) (h1 : NIL' = (term7 A)) : (term6 A list' P NIL') = (term10 A list' NIL' P).
Proof. exact (MK_COMB (@lem1071710 A list' NIL') (@lem1071709 A P NIL' h1)). Qed.
Lemma lem1071712 {A : Type'} (list' : type1338 A) (P : type1143 A) (NIL' : recspace A) : (term11 A list' P NIL') = (term11 A list' P NIL').
Proof. exact (eq_refl (term11 A list' P NIL')). Qed.
Lemma lem1071713 {A : Type'} (list' : type1338 A) (P : type1143 A) (NIL' : recspace A) (h1 : NIL' = (term7 A)) : ((term5 A list' P NIL') = (term6 A list' P NIL')) = ((term5 A list' P NIL') = (term10 A list' NIL' P)).
Proof. exact (MK_COMB (@lem1071712 A list' P NIL') (@lem1071711 A list' P NIL' h1)). Qed.
Lemma lem1071714 {A : Type'} (list' : type1338 A) (P : type1143 A) (NIL' : recspace A) (h1 : NIL' = (term7 A)) : (term5 A list' P NIL') = (term10 A list' NIL' P).
Proof. exact (EQ_MP (@lem1071713 A list' P NIL' h1) (@lem1071703 A list' P NIL')). Qed.
Lemma lem1071715 {A : Type'} (P : type1143 A) (h1 : P (@nil A)) : P (@nil A).
Proof. exact (h1). Qed.
Lemma lem1071716 {A : Type'} (P : type1143 A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : P (@nil A)) (h2 : list' = (term0 A NIL' CONS')) : term10 A list' NIL' P.
Proof. exact (conj (@lem1071705 A list' NIL' CONS' h2) (@lem1071715 A P h1)). Qed.
Lemma lem1071717 {A : Type'} (list' : type1338 A) (P : type1143 A) (NIL' : recspace A) (h1 : NIL' = (term7 A)) : (term10 A list' NIL' P) = (term5 A list' P NIL').
Proof. exact (SYM (@lem1071714 A list' P NIL' h1)). Qed.
Lemma lem1071718 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : P (@nil A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : term5 A list' P NIL'.
Proof. exact (EQ_MP (@lem1071717 A list' P NIL' h3) (@lem1071716 A P list' NIL' CONS' h1 h2)). Qed.
Lemma lem1071719 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : list' = (term0 A NIL' CONS')) (h2 : NIL' = (term7 A)) : term12 A list' P NIL'.
Proof. exact (fun h0 : P (@nil A) => @lem1071718 A P list' CONS' NIL' h0 h1 h2). Qed.
Lemma lem1071720 {A : Type'} (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : term5 A list' P a1) : term5 A list' P a1.
Proof. exact (h1). Qed.
Lemma lem1071721 {A : Type'} (list' : type1338 A) (P : type1143 A) (a1 : recspace A) : (term5 A list' P a1) = (term6 A list' P a1).
Proof. exact (eq_refl (term5 A list' P a1)). Qed.
Lemma lem1071722 {A : Type'} (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : term5 A list' P a1) : term6 A list' P a1.
Proof. exact (EQ_MP (@lem1071721 A list' P a1) (@lem1071720 A list' P a1 h1)). Qed.
Lemma lem1071723 {A : Type'} (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : term5 A list' P a1) : term8 A P a1.
Proof. exact (proj2 (@lem1071722 A list' P a1 h1)). Qed.
Lemma lem1071724 {A : Type'} (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : term5 A list' P a1) : list' a1.
Proof. exact (proj1 (@lem1071722 A list' P a1 h1)). Qed.
Lemma lem1071725 {A : Type'} (a0 : A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term13 A list' CONS' a0.
Proof. exact (@lem1071699 A list' NIL' CONS' h1 a0). Qed.
Lemma lem1071726 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) : (term13 A list' CONS' a0) = (term14 A list' CONS' a0).
Proof. exact (eq_refl (term13 A list' CONS' a0)). Qed.
Lemma lem1071727 {A : Type'} (a0 : A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term14 A list' CONS' a0.
Proof. exact (EQ_MP (@lem1071726 A list' CONS' a0) (@lem1071725 A a0 list' NIL' CONS' h1)). Qed.
Lemma lem1071728 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term15 A list' CONS' a0 a1.
Proof. exact (@lem1071727 A a0 list' NIL' CONS' h1 a1). Qed.
Lemma lem1071729 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term15 A list' CONS' a0 a1) = (term16 A list' CONS' a0 a1).
Proof. exact (eq_refl (term15 A list' CONS' a0 a1)). Qed.
Lemma lem1071732 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term16 A list' CONS' a0 a1.
Proof. exact (EQ_MP (@lem1071729 A list' CONS' a0 a1) (@lem1071728 A a0 a1 list' NIL' CONS' h1)). Qed.
Lemma lem1071733 {A : Type'} (a0 : A) (a1 : recspace A) (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : term16 A list' CONS' a0 a1.
Proof. exact (@lem1071732 A a0 a1 list' NIL' CONS' h1). Qed.
Lemma lem1071734 {A : Type'} (a0 : A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : list' = (term0 A NIL' CONS')) (h2 : term5 A list' P a1) : term17 A list' CONS' a0 a1.
Proof. exact (@lem1071733 A a0 a1 list' NIL' CONS' h1 (@lem1071724 A list' P a1 h2)). Qed.
Lemma lem1071742 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (list' r) = ((term19 A r) = r).
Proof. exact (TRANS (@lem1070982 A r list' CONS' NIL' h1 h2 h3) (@lem1070978 A r)). Qed.
Lemma lem1071743 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (list' r) = ((term19 A r) = r).
Proof. exact (@lem1071742 A r list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071744 {A : Type'} (a1 : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (list' a1) = ((term19 A a1) = a1).
Proof. exact (@lem1071743 A a1 list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071745 {A : Type'} (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : (term19 A a1) = a1.
Proof. exact (EQ_MP (@lem1071744 A a1 list' CONS' NIL' h1 h2 h3) (@lem1071724 A list' P a1 h4)). Qed.
Lemma lem1071746 {A : Type'} (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : a1 = (term19 A a1).
Proof. exact (SYM (@lem1071745 A CONS' NIL' list' P a1 h1 h2 h3 h4)). Qed.
Lemma lem1071747 {A : Type'} (list' : type1338 A) (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term20 A list' P CONS' a0 a1) = (term21 A list' P CONS' a0 a1).
Proof. exact (eq_refl (term20 A list' P CONS' a0 a1)). Qed.
Lemma lem1071748 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) : (term22 A P CONS' a0) = (term22 A P CONS' a0).
Proof. exact (eq_refl (term22 A P CONS' a0)). Qed.
Lemma lem1071749 {A : Type'} (a0 : A) (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : (term23 A P CONS' a0 a1) = (term24 A P CONS' a0 a1).
Proof. exact (MK_COMB (@lem1071748 A P CONS' a0) (@lem1071746 A CONS' NIL' list' P a1 h1 h2 h3 h4)). Qed.
Lemma lem1071750 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term24 A P CONS' a0 a1) = (term25 A P CONS' a0 a1).
Proof. exact (eq_refl (term24 A P CONS' a0 a1)). Qed.
Lemma lem1071751 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term26 A P CONS' a0 a1) = (term26 A P CONS' a0 a1).
Proof. exact (eq_refl (term26 A P CONS' a0 a1)). Qed.
Lemma lem1071752 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : ((term23 A P CONS' a0 a1) = (term24 A P CONS' a0 a1)) = ((term23 A P CONS' a0 a1) = (term25 A P CONS' a0 a1)).
Proof. exact (MK_COMB (@lem1071751 A P CONS' a0 a1) (@lem1071750 A P CONS' a0 a1)). Qed.
Lemma lem1071753 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term23 A P CONS' a0 a1) = (term27 A P CONS' a0 a1).
Proof. exact (eq_refl (term23 A P CONS' a0 a1)). Qed.
Lemma lem1071754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1071755 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term26 A P CONS' a0 a1) = (term28 A P CONS' a0 a1).
Proof. exact (MK_COMB (@lem1071754) (@lem1071753 A P CONS' a0 a1)). Qed.
Lemma lem1071756 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term25 A P CONS' a0 a1) = (term25 A P CONS' a0 a1).
Proof. exact (eq_refl (term25 A P CONS' a0 a1)). Qed.
Lemma lem1071757 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : ((term23 A P CONS' a0 a1) = (term25 A P CONS' a0 a1)) = ((term27 A P CONS' a0 a1) = (term25 A P CONS' a0 a1)).
Proof. exact (MK_COMB (@lem1071755 A P CONS' a0 a1) (@lem1071756 A P CONS' a0 a1)). Qed.
Lemma lem1071758 {A : Type'} (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : ((term23 A P CONS' a0 a1) = (term24 A P CONS' a0 a1)) = ((term27 A P CONS' a0 a1) = (term25 A P CONS' a0 a1)).
Proof. exact (TRANS (@lem1071752 A P CONS' a0 a1) (@lem1071757 A P CONS' a0 a1)). Qed.
Lemma lem1071759 {A : Type'} (a0 : A) (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : (term27 A P CONS' a0 a1) = (term25 A P CONS' a0 a1).
Proof. exact (EQ_MP (@lem1071758 A P CONS' a0 a1) (@lem1071749 A a0 CONS' NIL' list' P a1 h1 h2 h3 h4)). Qed.
Lemma lem1071760 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term29 A list' CONS' a0 a1) = (term29 A list' CONS' a0 a1).
Proof. exact (eq_refl (term29 A list' CONS' a0 a1)). Qed.
Lemma lem1071761 {A : Type'} (a0 : A) (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : (term21 A list' P CONS' a0 a1) = (term30 A list' P CONS' a0 a1).
Proof. exact (MK_COMB (@lem1071760 A list' CONS' a0 a1) (@lem1071759 A a0 CONS' NIL' list' P a1 h1 h2 h3 h4)). Qed.
Lemma lem1071762 {A : Type'} (a0 : A) (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : (term20 A list' P CONS' a0 a1) = (term30 A list' P CONS' a0 a1).
Proof. exact (TRANS (@lem1071747 A list' P CONS' a0 a1) (@lem1071761 A a0 CONS' NIL' list' P a1 h1 h2 h3 h4)). Qed.
Lemma lem1071764 {A : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : (term31 A CONS' a0 a1) = (@cons A a0 a1).
Proof. exact (SYM (@lem1071695 A a0 a1 CONS' h1)). Qed.
Lemma lem1071765 {A : Type'} (a0 : A) (a1 : list A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : (term31 A CONS' a0 a1) = (@cons A a0 a1).
Proof. exact (@lem1071764 A a0 a1 CONS' h1). Qed.
Lemma lem1071766 {A : Type'} (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : (term32 A CONS' a0 a1) = (term33 A a0 a1).
Proof. exact (@lem1071765 A a0 (@_mk_list A a1) CONS' h1). Qed.
Lemma lem1071767 {A : Type'} (P : type1143 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1071768 {A : Type'} (P : type1143 A) (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : (term25 A P CONS' a0 a1) = (term34 A P a0 a1).
Proof. exact (MK_COMB (@lem1071767 A P) (@lem1071766 A a0 a1 CONS' h1)). Qed.
Lemma lem1071769 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term29 A list' CONS' a0 a1) = (term29 A list' CONS' a0 a1).
Proof. exact (eq_refl (term29 A list' CONS' a0 a1)). Qed.
Lemma lem1071770 {A : Type'} (list' : type1338 A) (P : type1143 A) (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : (term30 A list' P CONS' a0 a1) = (term35 A list' CONS' P a0 a1).
Proof. exact (MK_COMB (@lem1071769 A list' CONS' a0 a1) (@lem1071768 A P a0 a1 CONS' h1)). Qed.
Lemma lem1071771 {A : Type'} (list' : type1338 A) (P : type1143 A) (CONS' : type1399 A) (a0 : A) (a1 : recspace A) : (term36 A list' P CONS' a0 a1) = (term36 A list' P CONS' a0 a1).
Proof. exact (eq_refl (term36 A list' P CONS' a0 a1)). Qed.
Lemma lem1071772 {A : Type'} (list' : type1338 A) (P : type1143 A) (a0 : A) (a1 : recspace A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : ((term20 A list' P CONS' a0 a1) = (term30 A list' P CONS' a0 a1)) = ((term20 A list' P CONS' a0 a1) = (term35 A list' CONS' P a0 a1)).
Proof. exact (MK_COMB (@lem1071771 A list' P CONS' a0 a1) (@lem1071770 A list' P a0 a1 CONS' h1)). Qed.
Lemma lem1071773 {A : Type'} (a0 : A) (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : (term20 A list' P CONS' a0 a1) = (term35 A list' CONS' P a0 a1).
Proof. exact (EQ_MP (@lem1071772 A list' P a0 a1 CONS' h1) (@lem1071762 A a0 CONS' NIL' list' P a1 h1 h2 h3 h4)). Qed.
Lemma lem1071774 {A : Type'} (P : type1143 A) (h1 : term37 A P) : term37 A P.
Proof. exact (h1). Qed.
Lemma lem1071775 {A : Type'} (a0 : A) (P : type1143 A) (h1 : term37 A P) : term38 A P a0.
Proof. exact (@lem1071774 A P h1 a0). Qed.
Lemma lem1071776 {A : Type'} (P : type1143 A) (a0 : A) : (term38 A P a0) = (term39 A P a0).
Proof. exact (eq_refl (term38 A P a0)). Qed.
Lemma lem1071777 {A : Type'} (a0 : A) (P : type1143 A) (h1 : term37 A P) : term39 A P a0.
Proof. exact (EQ_MP (@lem1071776 A P a0) (@lem1071775 A a0 P h1)). Qed.
Lemma lem1071778 {A : Type'} (a0 : A) (a1 : list A) (P : type1143 A) (h1 : term37 A P) : term40 A P a0 a1.
Proof. exact (@lem1071777 A a0 P h1 a1). Qed.
Lemma lem1071779 {A : Type'} (P : type1143 A) (a0 : A) (a1 : list A) : (term40 A P a0 a1) = (term41 A P a0 a1).
Proof. exact (eq_refl (term40 A P a0 a1)). Qed.
Lemma lem1071780 {A : Type'} (a0 : A) (a1 : list A) (P : type1143 A) (h1 : term37 A P) : term41 A P a0 a1.
Proof. exact (EQ_MP (@lem1071779 A P a0 a1) (@lem1071778 A a0 a1 P h1)). Qed.
Lemma lem1071781 {A : Type'} (a0 : A) (a1 : recspace A) (P : type1143 A) (h1 : term37 A P) : term42 A P a0 a1.
Proof. exact (@lem1071780 A a0 (@_mk_list A a1) P h1). Qed.
Lemma lem1071782 {A : Type'} (a0 : A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : term37 A P) (h2 : term5 A list' P a1) : term34 A P a0 a1.
Proof. exact (@lem1071781 A a0 a1 P h1 (@lem1071723 A list' P a1 h2)). Qed.
Lemma lem1071783 {A : Type'} (a0 : A) (NIL' : recspace A) (CONS' : type1399 A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : term37 A P) (h2 : list' = (term0 A NIL' CONS')) (h3 : term5 A list' P a1) : term35 A list' CONS' P a0 a1.
Proof. exact (conj (@lem1071734 A a0 NIL' CONS' list' P a1 h2 h3) (@lem1071782 A a0 list' P a1 h1 h3)). Qed.
Lemma lem1071784 {A : Type'} (a0 : A) (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) (h4 : term5 A list' P a1) : (term35 A list' CONS' P a0 a1) = (term20 A list' P CONS' a0 a1).
Proof. exact (SYM (@lem1071773 A a0 CONS' NIL' list' P a1 h1 h2 h3 h4)). Qed.
Lemma lem1071785 {A : Type'} (a0 : A) (CONS' : type1399 A) (NIL' : recspace A) (list' : type1338 A) (P : type1143 A) (a1 : recspace A) (h1 : term37 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) (h5 : term5 A list' P a1) : term20 A list' P CONS' a0 a1.
Proof. exact (EQ_MP (@lem1071784 A a0 CONS' NIL' list' P a1 h2 h3 h4 h5) (@lem1071783 A a0 NIL' CONS' list' P a1 h1 h3 h5)). Qed.
Lemma lem1071786 {A : Type'} (a0 : A) (a1 : recspace A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term37 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term43 A list' P CONS' a0 a1.
Proof. exact (fun h0 : term5 A list' P a1 => @lem1071785 A a0 CONS' NIL' list' P a1 h1 h2 h3 h4 h0). Qed.
Lemma lem1071787 {A : Type'} (a0 : A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term37 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term44 A list' P CONS' a0.
Proof. exact (fun a1 : recspace A => @lem1071786 A a0 a1 P list' CONS' NIL' h1 h2 h3 h4). Qed.
Lemma lem1071788 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term37 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term45 A list' P CONS'.
Proof. exact (fun a0 : A => @lem1071787 A a0 P list' CONS' NIL' h1 h2 h3 h4). Qed.
Lemma lem1071789 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : term46 A list' P CONS'.
Proof. exact (fun h0 : term37 A P => @lem1071788 A P list' CONS' NIL' h0 h1 h2 h3). Qed.
Lemma lem1071790 {A : Type'} (P : type1143 A) (h1 : term47 A P) : term47 A P.
Proof. exact (h1). Qed.
Lemma lem1071791 {A : Type'} (P : type1143 A) (h1 : term47 A P) : term37 A P.
Proof. exact (proj2 (@lem1071790 A P h1)). Qed.
Lemma lem1071792 {A : Type'} (P : type1143 A) (h1 : term47 A P) : P (@nil A).
Proof. exact (proj1 (@lem1071790 A P h1)). Qed.
Lemma lem1071793 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : term5 A list' P NIL'.
Proof. exact (@lem1071719 A P list' CONS' NIL' h2 h3 (@lem1071792 A P h1)). Qed.
Lemma lem1071794 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term45 A list' P CONS'.
Proof. exact (@lem1071789 A P list' CONS' NIL' h2 h3 h4 (@lem1071791 A P h1)). Qed.
Lemma lem1071795 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term48 A NIL' list' P CONS'.
Proof. exact (conj (@lem1071793 A P list' CONS' NIL' h1 h3 h4) (@lem1071794 A P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071796 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term49 A list' P.
Proof. exact (@lem1071698 A P list' NIL' CONS' h3 (@lem1071795 A P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071797 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term50 A list' P x.
Proof. exact (@lem1071796 A P list' CONS' NIL' h1 h2 h3 h4 (@_dest_list A x)). Qed.
Lemma lem1071798 {A : Type'} (list' : type1338 A) (P : type1143 A) (x : list A) : (term50 A list' P x) = (term51 A list' P x).
Proof. exact (eq_refl (term50 A list' P x)). Qed.
Lemma lem1071799 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term51 A list' P x.
Proof. exact (EQ_MP (@lem1071798 A list' P x) (@lem1071797 A x P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071801 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (list' r) = ((term19 A r) = r).
Proof. exact (TRANS (@lem1070982 A r list' CONS' NIL' h1 h2 h3) (@lem1070978 A r)). Qed.
Lemma lem1071802 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (list' r) = ((term19 A r) = r).
Proof. exact (@lem1071801 A r list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071803 {A : Type'} (x : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (term52 A list' x) = ((term53 A x) = (@_dest_list A x)).
Proof. exact (@lem1071802 A (@_dest_list A x) list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1071805 {A : Type'} (x : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (term54 A list' x) = (term55 A x).
Proof. exact (MK_COMB (@lem1071804) (@lem1071803 A x list' CONS' NIL' h1 h2 h3)). Qed.
Lemma lem1071806 {A : Type'} (list' : type1338 A) (P : type1143 A) (x : list A) : (term56 A list' P x) = (term56 A list' P x).
Proof. exact (eq_refl (term56 A list' P x)). Qed.
Lemma lem1071807 {A : Type'} (P : type1143 A) (x : list A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : (term51 A list' P x) = (term57 A list' P x).
Proof. exact (MK_COMB (@lem1071805 A x list' CONS' NIL' h1 h2 h3) (@lem1071806 A list' P x)). Qed.
Lemma lem1071808 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term57 A list' P x.
Proof. exact (EQ_MP (@lem1071807 A P x list' CONS' NIL' h2 h3 h4) (@lem1071799 A x P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071810 {A : Type'} (a : list A) : (term58 A a) = a.
Proof. exact (@axiom_15 A a). Qed.
Lemma lem1071811 {A : Type'} (a : list A) : (term58 A a) = a.
Proof. exact (@lem1071810 A a). Qed.
Lemma lem1071812 {A : Type'} (x : list A) : (term58 A x) = x.
Proof. exact (@lem1071811 A x). Qed.
Lemma lem1071813 {A : Type'} : (@_dest_list A) = (@_dest_list A).
Proof. exact (eq_refl (@_dest_list A)). Qed.
Lemma lem1071814 {A : Type'} (x : list A) : (term53 A x) = (@_dest_list A x).
Proof. exact (MK_COMB (@lem1071813 A) (@lem1071812 A x)). Qed.
Lemma lem1071815 {A : Type'} : (@eq (recspace A)) = (@eq (recspace A)).
Proof. exact (eq_refl (@eq (recspace A))). Qed.
Lemma lem1071816 {A : Type'} (x : list A) : (term59 A x) = (term60 A x).
Proof. exact (MK_COMB (@lem1071815 A) (@lem1071814 A x)). Qed.
Lemma lem1071817 {A : Type'} (x : list A) : (@_dest_list A x) = (@_dest_list A x).
Proof. exact (eq_refl (@_dest_list A x)). Qed.
Lemma lem1071818 {A : Type'} (x : list A) : ((term53 A x) = (@_dest_list A x)) = ((@_dest_list A x) = (@_dest_list A x)).
Proof. exact (MK_COMB (@lem1071816 A x) (@lem1071817 A x)). Qed.
Lemma lem1071819 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1071820 {A : Type'} (x : list A) : (term55 A x) = (term61 A x).
Proof. exact (MK_COMB (@lem1071819) (@lem1071818 A x)). Qed.
Lemma lem1071821 {A : Type'} (list' : type1338 A) (P : type1143 A) (x : list A) : (term56 A list' P x) = (term56 A list' P x).
Proof. exact (eq_refl (term56 A list' P x)). Qed.
Lemma lem1071822 {A : Type'} (list' : type1338 A) (P : type1143 A) (x : list A) : (term57 A list' P x) = (term62 A list' P x).
Proof. exact (MK_COMB (@lem1071820 A x) (@lem1071821 A list' P x)). Qed.
Lemma lem1071823 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term62 A list' P x.
Proof. exact (EQ_MP (@lem1071822 A list' P x) (@lem1071808 A x P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071824 {A : Type'} (x : list A) : (@_dest_list A x) = (@_dest_list A x).
Proof. exact (eq_refl (@_dest_list A x)). Qed.
Lemma lem1071825 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term56 A list' P x.
Proof. exact (@lem1071823 A x P list' CONS' NIL' h1 h2 h3 h4 (@lem1071824 A x)). Qed.
Lemma lem1071826 {A : Type'} (list' : type1338 A) (P : type1143 A) (x : list A) : (term56 A list' P x) = (term63 A list' P x).
Proof. exact (eq_refl (term56 A list' P x)). Qed.
Lemma lem1071827 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term63 A list' P x.
Proof. exact (EQ_MP (@lem1071826 A list' P x) (@lem1071825 A x P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071828 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term64 A P x.
Proof. exact (proj2 (@lem1071827 A x P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071830 {A : Type'} (a : list A) : (term58 A a) = a.
Proof. exact (@axiom_15 A a). Qed.
Lemma lem1071831 {A : Type'} (a : list A) : (term58 A a) = a.
Proof. exact (@lem1071830 A a). Qed.
Lemma lem1071832 {A : Type'} (x : list A) : (term58 A x) = x.
Proof. exact (@lem1071831 A x). Qed.
Lemma lem1071833 {A : Type'} (P : type1143 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1071834 {A : Type'} (P : type1143 A) (x : list A) : (term64 A P x) = (P x).
Proof. exact (MK_COMB (@lem1071833 A P) (@lem1071832 A x)). Qed.
Lemma lem1071835 {A : Type'} (x : list A) (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : P x.
Proof. exact (EQ_MP (@lem1071834 A P x) (@lem1071828 A x P list' CONS' NIL' h1 h2 h3 h4)). Qed.
Lemma lem1071836 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : term47 A P) (h2 : CONS' = (term18 A)) (h3 : list' = (term0 A NIL' CONS')) (h4 : NIL' = (term7 A)) : term65 A P.
Proof. exact (fun x : list A => @lem1071835 A x P list' CONS' NIL' h1 h2 h3 h4). Qed.
Lemma lem1071837 {A : Type'} (P : type1143 A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : term66 A P.
Proof. exact (fun h0 : term47 A P => @lem1071836 A P list' CONS' NIL' h0 h1 h2 h3). Qed.
Lemma lem1071838 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term7 A)) : term67 A.
Proof. exact (fun P : type1143 A => @lem1071837 A P list' CONS' NIL' h1 h2 h3). Qed.
Lemma lem1071839 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term18 A)) (h2 : NIL' = (term7 A)) : term68 A list' NIL' CONS'.
Proof. exact (fun h0 : list' = (term0 A NIL' CONS') => @lem1071838 A list' CONS' NIL' h1 h0 h2). Qed.
Lemma lem1071840 {A : Type'} : (term7 A) = (term7 A).
Proof. exact (eq_refl (term7 A)). Qed.
Lemma lem1071841 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : term69 A list' NIL' CONS'.
Proof. exact (fun h0 : NIL' = (term7 A) => @lem1071839 A list' CONS' NIL' h1 h0). Qed.
Lemma lem1071842 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : term70 A list' CONS'.
Proof. exact (@lem1071841 A list' (term7 A) CONS' h1). Qed.
Lemma lem1071843 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (h1 : CONS' = (term18 A)) : term71 A list' CONS'.
Proof. exact (@lem1071842 A list' CONS' h1 (@lem1071840 A)). Qed.
Lemma lem1071844 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (eq_refl (term18 A)). Qed.
Lemma lem1071845 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) : term72 A list' CONS'.
Proof. exact (fun h0 : CONS' = (term18 A) => @lem1071843 A list' CONS' h0). Qed.
Lemma lem1071846 {A : Type'} (list' : type1338 A) : term73 A list'.
Proof. exact (@lem1071845 A list' (term18 A)). Qed.
Lemma lem1071847 {A : Type'} (list' : type1338 A) : term74 A list'.
Proof. exact (@lem1071846 A list' (@lem1071844 A)). Qed.
Lemma lem1071848 {A : Type'} (list' : type1338 A) (h1 : list' = (term75 A)) : list' = (term75 A).
Proof. exact (h1). Qed.
Lemma lem1071849 {A : Type'} (list' : type1338 A) (h1 : list' = (term75 A)) : term67 A.
Proof. exact (@lem1071847 A list' (@lem1071848 A list' h1)). Qed.
Lemma lem1071850 {A : Type'} : (term75 A) = (term75 A).
Proof. exact (eq_refl (term75 A)). Qed.
Lemma lem1071851 {A : Type'} (list' : type1338 A) : term74 A list'.
Proof. exact (fun h0 : list' = (term75 A) => @lem1071849 A list' h0). Qed.
Lemma lem1071852 {A : Type'} : term76 A.
Proof. exact (@lem1071851 A (term75 A)). Qed.
Lemma lem1071853 {A : Type'} : term67 A.
Proof. exact (@lem1071852 A (@lem1071850 A)). Qed.
