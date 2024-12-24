Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_MUL_RZERO_term_abbrevs.
Require Import HREAL_MUL_LZERO_spec.
Require Import thm1320617_spec.
Lemma lem1321876 (x : hreal) : term0 x.
Proof. exact (@lem1320617 x). Qed.
Lemma lem1321877 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321878 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321877 x) (@lem1321876 x)). Qed.
Lemma lem1321879 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321878 x y). Qed.
Lemma lem1321880 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_mul x y) = (hreal_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321889 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1321880 y x) (@lem1321879 x y)). Qed.
Lemma lem1321890 (m : hreal) : (term3 m) = (term4 m).
Proof. exact (@lem1321889 term5 m). Qed.
Lemma lem1321891 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321892 (m : hreal) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem1321891) (@lem1321890 m)). Qed.
Lemma lem1321893 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1321894 (m : hreal) : ((term3 m) = term5) = ((term4 m) = term5).
Proof. exact (MK_COMB (@lem1321892 m) (@lem1321893)). Qed.
Lemma lem1321895 : term8 = term9.
Proof. exact (fun_ext (fun m : hreal => @lem1321894 m)). Qed.
Lemma lem1321896 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321897 : term10 = term11.
Proof. exact (MK_COMB (@lem1321896) (@lem1321895)). Qed.
Lemma lem1321898 : term11 = term10.
Proof. exact (SYM (@lem1321897)). Qed.
Lemma lem1321899 (m : hreal) : term12 m.
Proof. exact (@lem1321875 m). Qed.
Lemma lem1321900 (m : hreal) : (term12 m) = ((term4 m) = term5).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem1321903 (m : hreal) : (term4 m) = term5.
Proof. exact (EQ_MP (@lem1321900 m) (@lem1321899 m)). Qed.
Lemma lem1321908 : term11.
Proof. exact (fun m : hreal => @lem1321903 m). Qed.
Lemma lem1321909 : term10.
Proof. exact (EQ_MP (@lem1321898) (@lem1321908)). Qed.
