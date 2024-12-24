Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm86199_term_abbrevs.
Require Import thm85971_spec.
Require Import thm86148_spec.
Lemma lem86149 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem86150 : term1.
Proof. exact (EQ_MP (@lem86149) (@lem85971)). Qed.
Lemma lem86151 : term2.
Proof. exact (@lem86150 term3). Qed.
Lemma lem86152 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem86153 : term4.
Proof. exact (EQ_MP (@lem86152) (@lem86151)). Qed.
Lemma lem86154 (h1 : Nat.pow = term5) : Nat.pow = term5.
Proof. exact (h1). Qed.
Lemma lem86155 (h1 : Nat.pow = term5) : term5 = Nat.pow.
Proof. exact (SYM (@lem86154 h1)). Qed.
Lemma lem86156 (h1 : term5 = Nat.pow) : term5 = Nat.pow.
Proof. exact (h1). Qed.
Lemma lem86157 (h1 : term5 = Nat.pow) : Nat.pow = term5.
Proof. exact (SYM (@lem86156 h1)). Qed.
Lemma lem86158 : (Nat.pow = term5) = (term5 = Nat.pow).
Proof. exact (prop_ext (fun h1 : Nat.pow = term5 => @lem86155 h1) (fun h1 : term5 = Nat.pow => @lem86157 h1)). Qed.
Lemma lem86161 : term5 = Nat.pow.
Proof. exact (EQ_MP (@lem86158) (@lem86148)). Qed.
Lemma lem86162 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem86163 (m : nat) : (term6 m) = (Nat.pow m).
Proof. exact (MK_COMB (@lem86161) (@lem86162 m)). Qed.
Lemma lem86164 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem86165 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem86163 m) (@lem86164)). Qed.
Lemma lem86166 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem86167 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem86166) (@lem86165 m)). Qed.
Lemma lem86168 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem86169 (m : nat) : ((term7 m) = term11) = ((term8 m) = term11).
Proof. exact (MK_COMB (@lem86167 m) (@lem86168)). Qed.
Lemma lem86170 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem86169 m)). Qed.
Lemma lem86171 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86172 : term14 = term15.
Proof. exact (MK_COMB (@lem86171) (@lem86170)). Qed.
Lemma lem86173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86174 : term16 = term17.
Proof. exact (MK_COMB (@lem86173) (@lem86172)). Qed.
Lemma lem86176 : term5 = Nat.pow.
Proof. exact (EQ_MP (@lem86158) (@lem86148)). Qed.
Lemma lem86177 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem86178 (m : nat) : (term6 m) = (Nat.pow m).
Proof. exact (MK_COMB (@lem86176) (@lem86177 m)). Qed.
Lemma lem86179 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem86180 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem86178 m) (@lem86179 n)). Qed.
Lemma lem86181 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem86182 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem86181) (@lem86180 m n)). Qed.
Lemma lem86184 : term5 = Nat.pow.
Proof. exact (EQ_MP (@lem86158) (@lem86148)). Qed.
Lemma lem86185 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem86186 (m : nat) : (term6 m) = (Nat.pow m).
Proof. exact (MK_COMB (@lem86184) (@lem86185 m)). Qed.
Lemma lem86187 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem86188 (m : nat) (n : nat) : (term22 m n) = (Nat.pow m n).
Proof. exact (MK_COMB (@lem86186 m) (@lem86187 n)). Qed.
Lemma lem86189 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem86190 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem86189 m) (@lem86188 m n)). Qed.
Lemma lem86191 (m : nat) (n : nat) : ((term18 m n) = (term23 m n)) = ((term19 m n) = (term24 m n)).
Proof. exact (MK_COMB (@lem86182 m n) (@lem86190 m n)). Qed.
Lemma lem86192 (m : nat) : (term25 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem86191 m n)). Qed.
Lemma lem86193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86194 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem86193) (@lem86192 m)). Qed.
Lemma lem86195 : term29 = term30.
Proof. exact (fun_ext (fun m : nat => @lem86194 m)). Qed.
Lemma lem86196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86197 : term31 = term32.
Proof. exact (MK_COMB (@lem86196) (@lem86195)). Qed.
Lemma lem86198 : term4 = term33.
Proof. exact (MK_COMB (@lem86174) (@lem86197)). Qed.
Lemma lem86199 : term33.
Proof. exact (EQ_MP (@lem86198) (@lem86153)). Qed.
