Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm124616_term_abbrevs.
Require Import thm124360_spec.
Require Import thm124577_spec.
Lemma lem124578 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem124579 : term1.
Proof. exact (EQ_MP (@lem124578) (@lem124360)). Qed.
Lemma lem124580 : term2.
Proof. exact (@lem124579 term3). Qed.
Lemma lem124581 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem124582 : term4.
Proof. exact (EQ_MP (@lem124581) (@lem124580)). Qed.
Lemma lem124583 (h1 : Coq.Arith.PeanoNat.Nat.Odd = term5) : Coq.Arith.PeanoNat.Nat.Odd = term5.
Proof. exact (h1). Qed.
Lemma lem124584 (h1 : Coq.Arith.PeanoNat.Nat.Odd = term5) : term5 = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (SYM (@lem124583 h1)). Qed.
Lemma lem124585 (h1 : term5 = Coq.Arith.PeanoNat.Nat.Odd) : term5 = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (h1). Qed.
Lemma lem124586 (h1 : term5 = Coq.Arith.PeanoNat.Nat.Odd) : Coq.Arith.PeanoNat.Nat.Odd = term5.
Proof. exact (SYM (@lem124585 h1)). Qed.
Lemma lem124587 : (Coq.Arith.PeanoNat.Nat.Odd = term5) = (term5 = Coq.Arith.PeanoNat.Nat.Odd).
Proof. exact (prop_ext (fun h1 : Coq.Arith.PeanoNat.Nat.Odd = term5 => @lem124584 h1) (fun h1 : term5 = Coq.Arith.PeanoNat.Nat.Odd => @lem124586 h1)). Qed.
Lemma lem124590 : term5 = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (EQ_MP (@lem124587) (@lem124577)). Qed.
Lemma lem124591 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem124592 : term6 = term7.
Proof. exact (MK_COMB (@lem124590) (@lem124591)). Qed.
Lemma lem124593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124594 : term8 = term9.
Proof. exact (MK_COMB (@lem124593) (@lem124592)). Qed.
Lemma lem124595 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem124596 : (term6 = False) = (term7 = False).
Proof. exact (MK_COMB (@lem124594) (@lem124595)). Qed.
Lemma lem124597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem124598 : term10 = term11.
Proof. exact (MK_COMB (@lem124597) (@lem124596)). Qed.
Lemma lem124600 : term5 = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (EQ_MP (@lem124587) (@lem124577)). Qed.
Lemma lem124601 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem124602 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem124600) (@lem124601 n)). Qed.
Lemma lem124603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124604 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem124603) (@lem124602 n)). Qed.
Lemma lem124606 : term5 = Coq.Arith.PeanoNat.Nat.Odd.
Proof. exact (EQ_MP (@lem124587) (@lem124577)). Qed.
Lemma lem124607 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem124608 (n : nat) : (term16 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (MK_COMB (@lem124606) (@lem124607 n)). Qed.
Lemma lem124609 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem124610 (n : nat) : (term17 n) = (term18 n).
Proof. exact (MK_COMB (@lem124609) (@lem124608 n)). Qed.
Lemma lem124611 (n : nat) : ((term12 n) = (term17 n)) = ((term13 n) = (term18 n)).
Proof. exact (MK_COMB (@lem124604 n) (@lem124610 n)). Qed.
Lemma lem124612 : term19 = term20.
Proof. exact (fun_ext (fun n : nat => @lem124611 n)). Qed.
Lemma lem124613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124614 : term21 = term22.
Proof. exact (MK_COMB (@lem124613) (@lem124612)). Qed.
Lemma lem124615 : term4 = term23.
Proof. exact (MK_COMB (@lem124598) (@lem124614)). Qed.
Lemma lem124616 : term23.
Proof. exact (EQ_MP (@lem124615) (@lem124582)). Qed.
