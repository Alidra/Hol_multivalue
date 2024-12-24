Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_ADD_RID_term_abbrevs.
Require Import thm1320004_spec.
Require Import thm1320277_spec.
Lemma lem1321660 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1321661 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321662 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321661 x) (@lem1321660 x)). Qed.
Lemma lem1321663 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321662 x y). Qed.
Lemma lem1321664 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321673 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1321664 y x) (@lem1321663 x y)). Qed.
Lemma lem1321674 (n : hreal) : (term3 n) = (term4 n).
Proof. exact (@lem1321673 term5 n). Qed.
Lemma lem1321675 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321676 (n : hreal) : (term6 n) = (term7 n).
Proof. exact (MK_COMB (@lem1321675) (@lem1321674 n)). Qed.
Lemma lem1321677 (n : hreal) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1321678 (n : hreal) : ((term3 n) = n) = ((term4 n) = n).
Proof. exact (MK_COMB (@lem1321676 n) (@lem1321677 n)). Qed.
Lemma lem1321679 : term8 = term9.
Proof. exact (fun_ext (fun n : hreal => @lem1321678 n)). Qed.
Lemma lem1321680 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321681 : term10 = term11.
Proof. exact (MK_COMB (@lem1321680) (@lem1321679)). Qed.
Lemma lem1321682 : term11 = term10.
Proof. exact (SYM (@lem1321681)). Qed.
Lemma lem1321683 (x : hreal) : term12 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1321684 (x : hreal) : (term12 x) = ((term4 x) = x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1321687 (x : hreal) : (term4 x) = x.
Proof. exact (EQ_MP (@lem1321684 x) (@lem1321683 x)). Qed.
Lemma lem1321688 (n : hreal) : (term4 n) = n.
Proof. exact (@lem1321687 n). Qed.
Lemma lem1321693 : term11.
Proof. exact (fun n : hreal => @lem1321688 n). Qed.
Lemma lem1321694 : term10.
Proof. exact (EQ_MP (@lem1321682) (@lem1321693)). Qed.
