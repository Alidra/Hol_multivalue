Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299866_term_abbrevs.
Require Import int_pow_th_spec.
Lemma lem2299855 (x : int) (n : nat) (h1 : (term0 x n) = (term1 x n)) : (term0 x n) = (term1 x n).
Proof. exact (h1). Qed.
Lemma lem2299856 (x : int) (n : nat) (h1 : (term0 x n) = (term1 x n)) : (term1 x n) = (term0 x n).
Proof. exact (SYM (@lem2299855 x n h1)). Qed.
Lemma lem2299857 (x : int) (n : nat) (h1 : (term1 x n) = (term0 x n)) : (term1 x n) = (term0 x n).
Proof. exact (h1). Qed.
Lemma lem2299858 (x : int) (n : nat) (h1 : (term1 x n) = (term0 x n)) : (term0 x n) = (term1 x n).
Proof. exact (SYM (@lem2299857 x n h1)). Qed.
Lemma lem2299859 (x : int) (n : nat) : ((term0 x n) = (term1 x n)) = ((term1 x n) = (term0 x n)).
Proof. exact (prop_ext (fun h1 : (term0 x n) = (term1 x n) => @lem2299856 x n h1) (fun h1 : (term1 x n) = (term0 x n) => @lem2299858 x n h1)). Qed.
Lemma lem2299860 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun n : nat => @lem2299859 x n)). Qed.
Lemma lem2299861 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2299862 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2299861) (@lem2299860 x)). Qed.
Lemma lem2299863 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2299862 x)). Qed.
Lemma lem2299864 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299865 : term8 = term9.
Proof. exact (MK_COMB (@lem2299864) (@lem2299863)). Qed.
Lemma lem2299866 : term9.
Proof. exact (EQ_MP (@lem2299865) (@lem2294268)). Qed.
