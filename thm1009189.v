Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009189_term_abbrevs.
Require Import BIT1_spec.
Require Import thm75543_spec.
Require Import thm86199_spec.
Lemma lem1009125 (n : nat) : term0 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem1009126 (n : nat) : (term0 n) = ((BIT1 n) = (term1 n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1009128 (n : nat) : term2 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem1009129 (n : nat) : (term2 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1009131 : term3.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem1009141 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1009129 n) (@lem1009128 n)). Qed.
Lemma lem1009142 : (NUMERAL 0) = 0.
Proof. exact (@lem1009141 0). Qed.
Lemma lem1009143 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem1009144 (m : nat) : (term4 m) = (Nat.pow m 0).
Proof. exact (MK_COMB (@lem1009143 m) (@lem1009142)). Qed.
Lemma lem1009145 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1009146 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem1009145) (@lem1009144 m)). Qed.
Lemma lem1009148 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1009129 n) (@lem1009128 n)). Qed.
Lemma lem1009149 : term7 = (BIT1 0).
Proof. exact (@lem1009148 (BIT1 0)). Qed.
Lemma lem1009151 (n : nat) : (BIT1 n) = (term1 n).
Proof. exact (EQ_MP (@lem1009126 n) (@lem1009125 n)). Qed.
Lemma lem1009152 : (BIT1 0) = term8.
Proof. exact (@lem1009151 0). Qed.
Lemma lem1009153 : term7 = term8.
Proof. exact (TRANS (@lem1009149) (@lem1009152)). Qed.
Lemma lem1009154 (m : nat) : ((term4 m) = term7) = ((Nat.pow m 0) = term8).
Proof. exact (MK_COMB (@lem1009146 m) (@lem1009153)). Qed.
Lemma lem1009157 : term9 = term10.
Proof. exact (fun_ext (fun m : nat => @lem1009154 m)). Qed.
Lemma lem1009158 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009159 : term3 = term11.
Proof. exact (MK_COMB (@lem1009158) (@lem1009157)). Qed.
Lemma lem1009164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1009165 : term12 = term13.
Proof. exact (MK_COMB (@lem1009164) (@lem1009159)). Qed.
Lemma lem1009169 (n : nat) : (BIT1 n) = (term1 n).
Proof. exact (EQ_MP (@lem1009126 n) (@lem1009125 n)). Qed.
Lemma lem1009170 : (BIT1 0) = term8.
Proof. exact (@lem1009169 0). Qed.
Lemma lem1009171 (m : nat) : (term6 m) = (term6 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1009172 (m : nat) : ((Nat.pow m 0) = (BIT1 0)) = ((Nat.pow m 0) = term8).
Proof. exact (MK_COMB (@lem1009171 m) (@lem1009170)). Qed.
Lemma lem1009175 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem1009165) (@lem1009172 m)). Qed.
Lemma lem1009178 (m : nat) : (term15 m) = (term14 m).
Proof. exact (SYM (@lem1009175 m)). Qed.
Lemma lem1009179 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1009180 (m : nat) (h1 : term11) : term16 m.
Proof. exact (@lem1009179 h1 m). Qed.
Lemma lem1009181 (m : nat) : (term16 m) = ((Nat.pow m 0) = term8).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1009184 (m : nat) (h1 : term11) : (Nat.pow m 0) = term8.
Proof. exact (EQ_MP (@lem1009181 m) (@lem1009180 m h1)). Qed.
Lemma lem1009185 (m : nat) : term15 m.
Proof. exact (fun h0 : term11 => @lem1009184 m h0). Qed.
Lemma lem1009186 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1009178 m) (@lem1009185 m)). Qed.
Lemma lem1009189 (m : nat) : (Nat.pow m 0) = (BIT1 0).
Proof. exact (@lem1009186 m (@lem1009131)). Qed.
