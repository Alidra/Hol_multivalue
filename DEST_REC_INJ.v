Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DEST_REC_INJ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem1059698 {A : Type'} : (@_mk_rec A) = (@_mk_rec A).
Proof. exact (eq_refl (@_mk_rec A)). Qed.
Lemma lem1059699 {A : Type'} (x : recspace A) (y : recspace A) (h1 : (@_dest_rec A x) = (@_dest_rec A y)) : (@_dest_rec A x) = (@_dest_rec A y).
Proof. exact (h1). Qed.
Lemma lem1059708 {A : Type'} (x : recspace A) (y : recspace A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1059709 {A : Type'} : (@_dest_rec A) = (@_dest_rec A).
Proof. exact (eq_refl (@_dest_rec A)). Qed.
Lemma lem1059710 {A : Type'} (x : recspace A) (y : recspace A) (h1 : x = y) : (@_dest_rec A x) = (@_dest_rec A y).
Proof. exact (MK_COMB (@lem1059709 A) (@lem1059708 A x y h1)). Qed.
Lemma lem1059711 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1059712 {A : Type'} (x : recspace A) (y : recspace A) (h1 : x = y) : (term0 A x) = (term0 A y).
Proof. exact (MK_COMB (@lem1059711 A) (@lem1059710 A x y h1)). Qed.
Lemma lem1059713 {A : Type'} (y : recspace A) : (@_dest_rec A y) = (@_dest_rec A y).
Proof. exact (eq_refl (@_dest_rec A y)). Qed.
Lemma lem1059714 {A : Type'} (x : recspace A) (y : recspace A) (h1 : x = y) : ((@_dest_rec A x) = (@_dest_rec A y)) = ((@_dest_rec A y) = (@_dest_rec A y)).
Proof. exact (MK_COMB (@lem1059712 A x y h1) (@lem1059713 A y)). Qed.
Lemma lem1059716 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1059717 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1059716 (type1597 A) x). Qed.
Lemma lem1059718 {A : Type'} (y : recspace A) : ((@_dest_rec A y) = (@_dest_rec A y)) = True.
Proof. exact (@lem1059717 A (@_dest_rec A y)). Qed.
Lemma lem1059719 {A : Type'} (x : recspace A) (y : recspace A) (h1 : x = y) : ((@_dest_rec A x) = (@_dest_rec A y)) = True.
Proof. exact (TRANS (@lem1059714 A x y h1) (@lem1059718 A y)). Qed.
Lemma lem1059720 {A : Type'} (x : recspace A) (y : recspace A) (h1 : x = y) : True = ((@_dest_rec A x) = (@_dest_rec A y)).
Proof. exact (SYM (@lem1059719 A x y h1)). Qed.
Lemma lem1059721 {A : Type'} (x : recspace A) (y : recspace A) (h1 : x = y) : (@_dest_rec A x) = (@_dest_rec A y).
Proof. exact (EQ_MP (@lem1059720 A x y h1) (@lem0)). Qed.
Lemma lem1059722 {A : Type'} (x : recspace A) (y : recspace A) (h1 : (@_dest_rec A x) = (@_dest_rec A y)) : (term1 A x) = (term1 A y).
Proof. exact (MK_COMB (@lem1059698 A) (@lem1059699 A x y h1)). Qed.
Lemma lem1059730 {A : Type'} (a : recspace A) : (term1 A a) = a.
Proof. exact (@axiom_9 A a). Qed.
Lemma lem1059731 {A : Type'} (a : recspace A) : (term1 A a) = a.
Proof. exact (@lem1059730 A a). Qed.
Lemma lem1059732 {A : Type'} (x : recspace A) : (term1 A x) = x.
Proof. exact (@lem1059731 A x). Qed.
Lemma lem1059733 {A : Type'} : (@eq (recspace A)) = (@eq (recspace A)).
Proof. exact (eq_refl (@eq (recspace A))). Qed.
Lemma lem1059734 {A : Type'} (x : recspace A) : (term2 A x) = (@eq (recspace A) x).
Proof. exact (MK_COMB (@lem1059733 A) (@lem1059732 A x)). Qed.
Lemma lem1059736 {A : Type'} (a : recspace A) : (term1 A a) = a.
Proof. exact (@axiom_9 A a). Qed.
Lemma lem1059737 {A : Type'} (a : recspace A) : (term1 A a) = a.
Proof. exact (@lem1059736 A a). Qed.
Lemma lem1059738 {A : Type'} (y : recspace A) : (term1 A y) = y.
Proof. exact (@lem1059737 A y). Qed.
Lemma lem1059739 {A : Type'} (x : recspace A) (y : recspace A) : ((term1 A x) = (term1 A y)) = (x = y).
Proof. exact (MK_COMB (@lem1059734 A x) (@lem1059738 A y)). Qed.
Lemma lem1059742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1059743 {A : Type'} (x : recspace A) (y : recspace A) : (term3 A x y) = (term4 A x y).
Proof. exact (MK_COMB (@lem1059742) (@lem1059739 A x y)). Qed.
Lemma lem1059746 {A : Type'} (x : recspace A) (y : recspace A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1059747 {A : Type'} (x : recspace A) (y : recspace A) : (term5 A x y) = (term6 A x y).
Proof. exact (MK_COMB (@lem1059743 A x y) (@lem1059746 A x y)). Qed.
Lemma lem1059751 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1059752 {A : Type'} (x : recspace A) (y : recspace A) : (term6 A x y) = True.
Proof. exact (@lem1059751 (x = y)). Qed.
Lemma lem1059753 {A : Type'} (x : recspace A) (y : recspace A) : (term5 A x y) = True.
Proof. exact (TRANS (@lem1059747 A x y) (@lem1059752 A x y)). Qed.
Lemma lem1059754 {A : Type'} (x : recspace A) (y : recspace A) : True = (term5 A x y).
Proof. exact (SYM (@lem1059753 A x y)). Qed.
Lemma lem1059755 {A : Type'} (x : recspace A) (y : recspace A) : term5 A x y.
Proof. exact (EQ_MP (@lem1059754 A x y) (@lem0)). Qed.
Lemma lem1059757 {A : Type'} (x : recspace A) (y : recspace A) (h1 : (@_dest_rec A x) = (@_dest_rec A y)) : x = y.
Proof. exact (@lem1059755 A x y (@lem1059722 A x y h1)). Qed.
Lemma lem1059758 {A : Type'} (x : recspace A) (y : recspace A) : term7 A x y.
Proof. exact (fun h0 : x = y => @lem1059721 A x y h0). Qed.
Lemma lem1059759 {A : Type'} (x : recspace A) (y : recspace A) : term8 A x y.
Proof. exact (fun h0 : (@_dest_rec A x) = (@_dest_rec A y) => @lem1059757 A x y h0). Qed.
Lemma lem1059760 {A : Type'} (x : recspace A) (y : recspace A) : term9 A x y.
Proof. exact (conj (@lem1059759 A x y) (@lem1059758 A x y)). Qed.
Lemma lem1059761 {A : Type'} (x : recspace A) (y : recspace A) : (term9 A x y) = (((@_dest_rec A x) = (@_dest_rec A y)) = (x = y)).
Proof. exact (@lem32 ((@_dest_rec A x) = (@_dest_rec A y)) (x = y)). Qed.
Lemma lem1059762 {A : Type'} (x : recspace A) (y : recspace A) : ((@_dest_rec A x) = (@_dest_rec A y)) = (x = y).
Proof. exact (EQ_MP (@lem1059761 A x y) (@lem1059760 A x y)). Qed.
Lemma lem1059767 {A : Type'} (x : recspace A) : term10 A x.
Proof. exact (fun y : recspace A => @lem1059762 A x y). Qed.
Lemma lem1059772 {A : Type'} : term11 A.
Proof. exact (fun x : recspace A => @lem1059767 A x). Qed.
