Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_SYM_term_abbrevs.
Require Import TREAL_ADD_SYM_EQ_spec.
Require Import TREAL_EQ_AP_spec.
Lemma lem1327752 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1327753 (x : prod hreal hreal) (h1 : term0) : term1 x.
Proof. exact (@lem1327752 h1 x). Qed.
Lemma lem1327754 (x : prod hreal hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1327755 (x : prod hreal hreal) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1327754 x) (@lem1327753 x h1)). Qed.
Lemma lem1327756 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term3 x y.
Proof. exact (@lem1327755 x h1 y). Qed.
Lemma lem1327757 (x : prod hreal hreal) (y : prod hreal hreal) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1327758 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1327757 x y) (@lem1327756 x y h1)). Qed.
Lemma lem1327759 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1327760 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) (h2 : x = y) : treal_eq x y.
Proof. exact (@lem1327758 x y h1 (@lem1327759 x y h2)). Qed.
Lemma lem1327761 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : term5 x y.
Proof. exact (fun h0 : term0 => @lem1327760 x y h0 h1). Qed.
Lemma lem1327762 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1327763 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) (h2 : x = y) : treal_eq x y.
Proof. exact (@lem1327761 x y h2 (@lem1327762 h1)). Qed.
Lemma lem1327764 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : x = y => @lem1327763 x y h1 h0). Qed.
Lemma lem1327765 (x : prod hreal hreal) (h1 : term0) : term2 x.
Proof. exact (fun y : prod hreal hreal => @lem1327764 x y h1). Qed.
Lemma lem1327766 (h1 : term0) : term0.
Proof. exact (fun x : prod hreal hreal => @lem1327765 x h1). Qed.
Lemma lem1327767 : term6.
Proof. exact (fun h0 : term0 => @lem1327766 h0). Qed.
Lemma lem1327768 : term0.
Proof. exact (@lem1327767 (@lem1326851)). Qed.
Lemma lem1327769 (x : prod hreal hreal) : term1 x.
Proof. exact (@lem1327768 x). Qed.
Lemma lem1327770 (x : prod hreal hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1327771 (x : prod hreal hreal) : term2 x.
Proof. exact (EQ_MP (@lem1327770 x) (@lem1327769 x)). Qed.
Lemma lem1327772 (x : prod hreal hreal) (y : prod hreal hreal) : term3 x y.
Proof. exact (@lem1327771 x y). Qed.
Lemma lem1327773 (x : prod hreal hreal) (y : prod hreal hreal) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1327776 (x : prod hreal hreal) (y : prod hreal hreal) : term4 x y.
Proof. exact (EQ_MP (@lem1327773 x y) (@lem1327772 x y)). Qed.
Lemma lem1327777 (y : prod hreal hreal) (x : prod hreal hreal) : term7 y x.
Proof. exact (@lem1327776 (treal_add x y) (treal_add y x)). Qed.
Lemma lem1327778 (x : prod hreal hreal) : term8 x.
Proof. exact (@lem1327521 x). Qed.
Lemma lem1327779 (x : prod hreal hreal) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1327780 (x : prod hreal hreal) : term9 x.
Proof. exact (EQ_MP (@lem1327779 x) (@lem1327778 x)). Qed.
Lemma lem1327781 (x : prod hreal hreal) (y : prod hreal hreal) : term10 x y.
Proof. exact (@lem1327780 x y). Qed.
Lemma lem1327782 (y : prod hreal hreal) (x : prod hreal hreal) : (term10 x y) = ((treal_add x y) = (treal_add y x)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1327785 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_add x y) = (treal_add y x).
Proof. exact (EQ_MP (@lem1327782 y x) (@lem1327781 x y)). Qed.
Lemma lem1327786 (y : prod hreal hreal) (x : prod hreal hreal) : term11 y x.
Proof. exact (@lem1327777 y x (@lem1327785 y x)). Qed.
Lemma lem1327791 (x : prod hreal hreal) : term12 x.
Proof. exact (fun y : prod hreal hreal => @lem1327786 y x). Qed.
Lemma lem1327796 : term13.
Proof. exact (fun x : prod hreal hreal => @lem1327791 x). Qed.
