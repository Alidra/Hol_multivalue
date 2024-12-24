Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm124233_term_abbrevs.
Require Import thm123979_spec.
Require Import thm124194_spec.
Lemma lem124195 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem124196 : term1.
Proof. exact (EQ_MP (@lem124195) (@lem123979)). Qed.
Lemma lem124197 : term2.
Proof. exact (@lem124196 term3). Qed.
Lemma lem124198 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem124199 : term4.
Proof. exact (EQ_MP (@lem124198) (@lem124197)). Qed.
Lemma lem124200 (h1 : Coq.Arith.PeanoNat.Nat.Even = term5) : Coq.Arith.PeanoNat.Nat.Even = term5.
Proof. exact (h1). Qed.
Lemma lem124201 (h1 : Coq.Arith.PeanoNat.Nat.Even = term5) : term5 = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (SYM (@lem124200 h1)). Qed.
Lemma lem124202 (h1 : term5 = Coq.Arith.PeanoNat.Nat.Even) : term5 = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (h1). Qed.
Lemma lem124203 (h1 : term5 = Coq.Arith.PeanoNat.Nat.Even) : Coq.Arith.PeanoNat.Nat.Even = term5.
Proof. exact (SYM (@lem124202 h1)). Qed.
Lemma lem124204 : (Coq.Arith.PeanoNat.Nat.Even = term5) = (term5 = Coq.Arith.PeanoNat.Nat.Even).
Proof. exact (prop_ext (fun h1 : Coq.Arith.PeanoNat.Nat.Even = term5 => @lem124201 h1) (fun h1 : term5 = Coq.Arith.PeanoNat.Nat.Even => @lem124203 h1)). Qed.
Lemma lem124207 : term5 = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (EQ_MP (@lem124204) (@lem124194)). Qed.
Lemma lem124208 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem124209 : term6 = term7.
Proof. exact (MK_COMB (@lem124207) (@lem124208)). Qed.
Lemma lem124210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124211 : term8 = term9.
Proof. exact (MK_COMB (@lem124210) (@lem124209)). Qed.
Lemma lem124212 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem124213 : (term6 = True) = (term7 = True).
Proof. exact (MK_COMB (@lem124211) (@lem124212)). Qed.
Lemma lem124214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem124215 : term10 = term11.
Proof. exact (MK_COMB (@lem124214) (@lem124213)). Qed.
Lemma lem124217 : term5 = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (EQ_MP (@lem124204) (@lem124194)). Qed.
Lemma lem124218 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem124219 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem124217) (@lem124218 n)). Qed.
Lemma lem124220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124221 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem124220) (@lem124219 n)). Qed.
Lemma lem124223 : term5 = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (EQ_MP (@lem124204) (@lem124194)). Qed.
Lemma lem124224 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem124225 (n : nat) : (term16 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (MK_COMB (@lem124223) (@lem124224 n)). Qed.
Lemma lem124226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem124227 (n : nat) : (term17 n) = (term18 n).
Proof. exact (MK_COMB (@lem124226) (@lem124225 n)). Qed.
Lemma lem124228 (n : nat) : ((term12 n) = (term17 n)) = ((term13 n) = (term18 n)).
Proof. exact (MK_COMB (@lem124221 n) (@lem124227 n)). Qed.
Lemma lem124229 : term19 = term20.
Proof. exact (fun_ext (fun n : nat => @lem124228 n)). Qed.
Lemma lem124230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124231 : term21 = term22.
Proof. exact (MK_COMB (@lem124230) (@lem124229)). Qed.
Lemma lem124232 : term4 = term23.
Proof. exact (MK_COMB (@lem124215) (@lem124231)). Qed.
Lemma lem124233 : term23.
Proof. exact (EQ_MP (@lem124232) (@lem124199)). Qed.
