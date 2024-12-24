Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LET_TRANS_term_abbrevs.
Require Import REAL_LET_TRANS_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302132 (x : int) : term0 x.
Proof. exact (@lem1371386 (real_of_int x)). Qed.
Lemma lem2302133 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302134 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302133 x) (@lem2302132 x)). Qed.
Lemma lem2302135 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302134 x (real_of_int y)). Qed.
Lemma lem2302136 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302137 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2302136 y x) (@lem2302135 x y)). Qed.
Lemma lem2302138 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2302137 y x (real_of_int z)). Qed.
Lemma lem2302139 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2302140 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2302139 y x z) (@lem2302138 y x z)). Qed.
Lemma lem2302142 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302144 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2302143) (@lem2302142 x y)). Qed.
Lemma lem2302146 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302147 (y : int) (z : int) : (term9 y z) = (int_lt y z).
Proof. exact (@lem2302146 y z). Qed.
Lemma lem2302148 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2302144 x y) (@lem2302147 y z)). Qed.
Lemma lem2302149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302150 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (MK_COMB (@lem2302149) (@lem2302148 x y z)). Qed.
Lemma lem2302152 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302153 (x : int) (z : int) : (term9 x z) = (int_lt x z).
Proof. exact (@lem2302152 x z). Qed.
Lemma lem2302154 (y : int) (x : int) (z : int) : (term5 y x z) = (term14 y x z).
Proof. exact (MK_COMB (@lem2302150 x y z) (@lem2302153 x z)). Qed.
Lemma lem2302155 (y : int) (x : int) (z : int) : term14 y x z.
Proof. exact (EQ_MP (@lem2302154 y x z) (@lem2302140 y x z)). Qed.
Lemma lem2302156 (y : int) (x : int) : term15 y x.
Proof. exact (fun z : int => @lem2302155 y x z). Qed.
Lemma lem2302157 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2302156 y x). Qed.
Lemma lem2302158 : term17.
Proof. exact (fun x : int => @lem2302157 x). Qed.
