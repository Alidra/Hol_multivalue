Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm712018_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem711954 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem711955 : term1.
Proof. exact (proj2 (@lem711954)). Qed.
Lemma lem711956 : term2.
Proof. exact (proj2 (@lem711955)). Qed.
Lemma lem711957 : term3.
Proof. exact (proj2 (@lem711956)). Qed.
Lemma lem711958 : term4.
Proof. exact (proj2 (@lem711957)). Qed.
Lemma lem711990 : term5.
Proof. exact (proj1 (@lem711958)). Qed.
Lemma lem711991 (n : nat) : term6 n.
Proof. exact (@lem711990 n). Qed.
Lemma lem711992 (n : nat) : (term6 n) = ((term7 n) = (BIT1 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem712015 (n : nat) : (term7 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem711992 n) (@lem711991 n)). Qed.
Lemma lem712016 : term8 = (BIT1 0).
Proof. exact (@lem712015 0). Qed.
Lemma lem712017 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem712018 : term9 = term10.
Proof. exact (MK_COMB (@lem712017) (@lem712016)). Qed.
