Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1396812_term_abbrevs.
Require Import REAL_POS_spec.
Require Import real_ge_spec.
Lemma lem1396786 (n : nat) : term0 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1396787 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1396788 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1396787 n) (@lem1396786 n)). Qed.
Lemma lem1396791 (y : real) (x : real) (h1 : (real_ge x y) = (real_le y x)) : (real_ge x y) = (real_le y x).
Proof. exact (h1). Qed.
Lemma lem1396792 (y : real) (x : real) (h1 : (real_ge x y) = (real_le y x)) : (real_le y x) = (real_ge x y).
Proof. exact (SYM (@lem1396791 y x h1)). Qed.
Lemma lem1396793 (x : real) (y : real) (h1 : (real_le y x) = (real_ge x y)) : (real_le y x) = (real_ge x y).
Proof. exact (h1). Qed.
Lemma lem1396794 (x : real) (y : real) (h1 : (real_le y x) = (real_ge x y)) : (real_ge x y) = (real_le y x).
Proof. exact (SYM (@lem1396793 x y h1)). Qed.
Lemma lem1396795 (x : real) (y : real) : ((real_ge x y) = (real_le y x)) = ((real_le y x) = (real_ge x y)).
Proof. exact (prop_ext (fun h1 : (real_ge x y) = (real_le y x) => @lem1396792 y x h1) (fun h1 : (real_le y x) = (real_ge x y) => @lem1396794 x y h1)). Qed.
Lemma lem1396796 (y : real) : (term2 y) = (term3 y).
Proof. exact (fun_ext (fun x : real => @lem1396795 x y)). Qed.
Lemma lem1396797 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396798 (y : real) : (term4 y) = (term5 y).
Proof. exact (MK_COMB (@lem1396797) (@lem1396796 y)). Qed.
Lemma lem1396799 : term6 = term7.
Proof. exact (fun_ext (fun y : real => @lem1396798 y)). Qed.
Lemma lem1396800 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396801 : term8 = term9.
Proof. exact (MK_COMB (@lem1396800) (@lem1396799)). Qed.
Lemma lem1396802 : term9.
Proof. exact (EQ_MP (@lem1396801) (@lem1342163)). Qed.
Lemma lem1396803 (y : real) : term10 y.
Proof. exact (@lem1396802 y). Qed.
Lemma lem1396804 (y : real) : (term10 y) = (term5 y).
Proof. exact (eq_refl (term10 y)). Qed.
Lemma lem1396805 (y : real) : term5 y.
Proof. exact (EQ_MP (@lem1396804 y) (@lem1396803 y)). Qed.
Lemma lem1396806 (y : real) (x : real) : term11 y x.
Proof. exact (@lem1396805 y x). Qed.
Lemma lem1396807 (x : real) (y : real) : (term11 y x) = ((real_le y x) = (real_ge x y)).
Proof. exact (eq_refl (term11 y x)). Qed.
Lemma lem1396810 (x : real) (y : real) : (real_le y x) = (real_ge x y).
Proof. exact (EQ_MP (@lem1396807 x y) (@lem1396806 y x)). Qed.
Lemma lem1396811 (n : nat) : (term1 n) = (term12 n).
Proof. exact (@lem1396810 (real_of_num n) term13). Qed.
Lemma lem1396812 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem1396811 n) (@lem1396788 n)). Qed.
