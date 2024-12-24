Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIT1_THM_term_abbrevs.
Require Import BIT1_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem80166 (n : nat) : term0 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem80167 (n : nat) : (term0 n) = ((BIT1 n) = (term1 n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem80169 (n : nat) : term2 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem80170 (n : nat) : (term2 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem80179 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80170 n) (@lem80169 n)). Qed.
Lemma lem80180 (n : nat) : (term3 n) = (BIT1 n).
Proof. exact (@lem80179 (BIT1 n)). Qed.
Lemma lem80182 (n : nat) : (BIT1 n) = (term1 n).
Proof. exact (EQ_MP (@lem80167 n) (@lem80166 n)). Qed.
Lemma lem80183 (n : nat) : (term3 n) = (term1 n).
Proof. exact (TRANS (@lem80180 n) (@lem80182 n)). Qed.
Lemma lem80184 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80185 (n : nat) : (term4 n) = (term5 n).
Proof. exact (MK_COMB (@lem80184) (@lem80183 n)). Qed.
Lemma lem80187 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80170 n) (@lem80169 n)). Qed.
Lemma lem80188 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem80189 (n : nat) : (term6 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem80188) (@lem80187 n)). Qed.
Lemma lem80191 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80170 n) (@lem80169 n)). Qed.
Lemma lem80192 (n : nat) : (term7 n) = (Nat.add n n).
Proof. exact (MK_COMB (@lem80189 n) (@lem80191 n)). Qed.
Lemma lem80193 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80194 (n : nat) : (term8 n) = (term1 n).
Proof. exact (MK_COMB (@lem80193) (@lem80192 n)). Qed.
Lemma lem80195 (n : nat) : ((term3 n) = (term8 n)) = ((term1 n) = (term1 n)).
Proof. exact (MK_COMB (@lem80185 n) (@lem80194 n)). Qed.
Lemma lem80197 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80198 (x : nat) : (x = x) = True.
Proof. exact (@lem80197 nat x). Qed.
Lemma lem80199 (n : nat) : ((term1 n) = (term1 n)) = True.
Proof. exact (@lem80198 (term1 n)). Qed.
Lemma lem80200 (n : nat) : ((term3 n) = (term8 n)) = True.
Proof. exact (TRANS (@lem80195 n) (@lem80199 n)). Qed.
Lemma lem80201 : term9 = term10.
Proof. exact (fun_ext (fun n : nat => @lem80200 n)). Qed.
Lemma lem80202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80203 : term11 = term12.
Proof. exact (MK_COMB (@lem80202) (@lem80201)). Qed.
Lemma lem80205 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem80206 (t : Prop) : (term14 t) = t.
Proof. exact (@lem80205 nat t). Qed.
Lemma lem80207 : term12 = True.
Proof. exact (@lem80206 True). Qed.
Lemma lem80208 : term11 = True.
Proof. exact (TRANS (@lem80203) (@lem80207)). Qed.
Lemma lem80209 : True = term11.
Proof. exact (SYM (@lem80208)). Qed.
Lemma lem80210 : term11.
Proof. exact (EQ_MP (@lem80209) (@lem0)). Qed.
