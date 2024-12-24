Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_LE_ADD_RCANCEL_term_abbrevs.
Require Import HREAL_LE_ADD_LCANCEL_spec.
Require Import thm1320004_spec.
Lemma lem1321589 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1321590 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321591 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321590 x) (@lem1321589 x)). Qed.
Lemma lem1321592 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321591 x y). Qed.
Lemma lem1321593 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321610 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1321593 y x) (@lem1321592 x y)). Qed.
Lemma lem1321611 (p : hreal) (m : hreal) : (hreal_add m p) = (hreal_add p m).
Proof. exact (@lem1321610 p m). Qed.
Lemma lem1321612 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1321613 (p : hreal) (m : hreal) : (term3 m p) = (term3 p m).
Proof. exact (MK_COMB (@lem1321612) (@lem1321611 p m)). Qed.
Lemma lem1321615 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1321593 y x) (@lem1321592 x y)). Qed.
Lemma lem1321616 (p : hreal) (n : hreal) : (hreal_add n p) = (hreal_add p n).
Proof. exact (@lem1321615 p n). Qed.
Lemma lem1321617 (m : hreal) (p : hreal) (n : hreal) : (term4 m n p) = (term5 m p n).
Proof. exact (MK_COMB (@lem1321613 p m) (@lem1321616 p n)). Qed.
Lemma lem1321618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321619 (m : hreal) (p : hreal) (n : hreal) : (term6 m n p) = (term7 m p n).
Proof. exact (MK_COMB (@lem1321618) (@lem1321617 m p n)). Qed.
Lemma lem1321620 (m : hreal) (n : hreal) : (hreal_le m n) = (hreal_le m n).
Proof. exact (eq_refl (hreal_le m n)). Qed.
Lemma lem1321621 (p : hreal) (m : hreal) (n : hreal) : ((term4 m n p) = (hreal_le m n)) = ((term5 m p n) = (hreal_le m n)).
Proof. exact (MK_COMB (@lem1321619 m p n) (@lem1321620 m n)). Qed.
Lemma lem1321622 (m : hreal) (n : hreal) : (term8 m n) = (term9 m n).
Proof. exact (fun_ext (fun p : hreal => @lem1321621 p m n)). Qed.
Lemma lem1321623 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321624 (m : hreal) (n : hreal) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem1321623) (@lem1321622 m n)). Qed.
Lemma lem1321625 (m : hreal) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : hreal => @lem1321624 m n)). Qed.
Lemma lem1321626 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321627 (m : hreal) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem1321626) (@lem1321625 m)). Qed.
Lemma lem1321628 : term16 = term17.
Proof. exact (fun_ext (fun m : hreal => @lem1321627 m)). Qed.
Lemma lem1321629 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321630 : term18 = term19.
Proof. exact (MK_COMB (@lem1321629) (@lem1321628)). Qed.
Lemma lem1321631 : term19 = term18.
Proof. exact (SYM (@lem1321630)). Qed.
Lemma lem1321632 (m : hreal) : term20 m.
Proof. exact (@lem1321588 m). Qed.
Lemma lem1321633 (m : hreal) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1321634 (m : hreal) : term21 m.
Proof. exact (EQ_MP (@lem1321633 m) (@lem1321632 m)). Qed.
Lemma lem1321635 (m : hreal) (n : hreal) : term22 m n.
Proof. exact (@lem1321634 m n). Qed.
Lemma lem1321636 (m : hreal) (n : hreal) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1321637 (m : hreal) (n : hreal) : term23 m n.
Proof. exact (EQ_MP (@lem1321636 m n) (@lem1321635 m n)). Qed.
Lemma lem1321638 (m : hreal) (n : hreal) (p : hreal) : term24 m n p.
Proof. exact (@lem1321637 m n p). Qed.
Lemma lem1321639 (m : hreal) (n : hreal) (p : hreal) : (term24 m n p) = ((term5 n m p) = (hreal_le n p)).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem1321642 (m : hreal) (n : hreal) (p : hreal) : (term5 n m p) = (hreal_le n p).
Proof. exact (EQ_MP (@lem1321639 m n p) (@lem1321638 m n p)). Qed.
Lemma lem1321643 (p : hreal) (m : hreal) (n : hreal) : (term5 m p n) = (hreal_le m n).
Proof. exact (@lem1321642 p m n). Qed.
Lemma lem1321648 (m : hreal) (n : hreal) : term11 m n.
Proof. exact (fun p : hreal => @lem1321643 p m n). Qed.
Lemma lem1321653 (m : hreal) : term15 m.
Proof. exact (fun n : hreal => @lem1321648 m n). Qed.
Lemma lem1321658 : term19.
Proof. exact (fun m : hreal => @lem1321653 m). Qed.
Lemma lem1321659 : term18.
Proof. exact (EQ_MP (@lem1321631) (@lem1321658)). Qed.
