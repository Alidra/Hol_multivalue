Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_AND_ODD_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_DEF_spec.
Require Import NOT_EVEN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem124922 (p : Prop) (h1 : term0 p) : term0 p.
Proof. exact (h1). Qed.
Lemma lem124923 (p : Prop) (h1 : term0 p) : ~ p.
Proof. exact (proj2 (@lem124922 p h1)). Qed.
Lemma lem124924 (p : Prop) (h1 : term0 p) : p.
Proof. exact (proj1 (@lem124922 p h1)). Qed.
Lemma lem124925 (p : Prop) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem124926 (p : Prop) : (~ p) = (term1 p).
Proof. exact (MK_COMB (@lem56) (@lem124925 p)). Qed.
Lemma lem124927 (p : Prop) : (term1 p) = (p -> False).
Proof. exact (eq_refl (term1 p)). Qed.
Lemma lem124928 (p : Prop) : (term2 p) = (term2 p).
Proof. exact (eq_refl (term2 p)). Qed.
Lemma lem124929 (p : Prop) : ((~ p) = (term1 p)) = ((~ p) = (p -> False)).
Proof. exact (MK_COMB (@lem124928 p) (@lem124927 p)). Qed.
Lemma lem124930 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem124929 p) (@lem124926 p)). Qed.
Lemma lem124931 (p : Prop) (h1 : term0 p) : p -> False.
Proof. exact (EQ_MP (@lem124930 p) (@lem124923 p h1)). Qed.
Lemma lem124932 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem124933 (p : Prop) (h1 : p) (h2 : term0 p) : False.
Proof. exact (@lem124931 p h2 (@lem124932 p h1)). Qed.
Lemma lem124934 (p : Prop) (h1 : term0 p) : p = False.
Proof. exact (prop_ext (fun h2 : p => @lem124933 p h2 h1) (fun h2 : False => @lem124924 p h1)). Qed.
Lemma lem124935 (p : Prop) (h1 : term0 p) : False.
Proof. exact (EQ_MP (@lem124934 p h1) (@lem124924 p h1)). Qed.
Lemma lem124936 (p : Prop) : term3 p.
Proof. exact (fun h0 : term0 p => @lem124935 p h0). Qed.
Lemma lem124937 (p : Prop) : (term3 p) = (term4 p).
Proof. exact (@lem69 (term0 p)). Qed.
Lemma lem124938 (p : Prop) : term4 p.
Proof. exact (EQ_MP (@lem124937 p) (@lem124936 p)). Qed.
Lemma lem124940 (n : nat) (h1 : (term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem124941 (n : nat) (h1 : (term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n).
Proof. exact (SYM (@lem124940 n h1)). Qed.
Lemma lem124942 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n).
Proof. exact (h1). Qed.
Lemma lem124943 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n)) : (term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem124942 n h1)). Qed.
Lemma lem124944 (n : nat) : ((term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n)).
Proof. exact (prop_ext (fun h1 : (term5 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem124941 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n) => @lem124943 n h1)). Qed.
Lemma lem124945 : term6 = term7.
Proof. exact (fun_ext (fun n : nat => @lem124944 n)). Qed.
Lemma lem124946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124947 : term8 = term9.
Proof. exact (MK_COMB (@lem124946) (@lem124945)). Qed.
Lemma lem124948 : term9.
Proof. exact (EQ_MP (@lem124947) (@lem124715)). Qed.
Lemma lem124949 (p : Prop) : term10 p.
Proof. exact (@lem82 (term0 p)). Qed.
Lemma lem124951 (n : nat) : term11 n.
Proof. exact (@lem124948 n). Qed.
Lemma lem124952 (n : nat) : (term11 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n)).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem124961 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term5 n).
Proof. exact (EQ_MP (@lem124952 n) (@lem124951 n)). Qed.
Lemma lem124962 (n : nat) : (term12 n) = (term12 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem124963 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem124962 n) (@lem124961 n)). Qed.
Lemma lem124965 (p : Prop) : (term0 p) = False.
Proof. exact (@lem124949 p (@lem124938 p)). Qed.
Lemma lem124966 (n : nat) : (term14 n) = False.
Proof. exact (@lem124965 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem124967 (n : nat) : (term13 n) = False.
Proof. exact (TRANS (@lem124963 n) (@lem124966 n)). Qed.
Lemma lem124968 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem124969 (n : nat) : (term15 n) = (~ False).
Proof. exact (MK_COMB (@lem124968) (@lem124967 n)). Qed.
Lemma lem124971 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem124972 (n : nat) : (term15 n) = True.
Proof. exact (TRANS (@lem124969 n) (@lem124971)). Qed.
Lemma lem124973 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem124972 n)). Qed.
Lemma lem124974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124975 : term18 = term19.
Proof. exact (MK_COMB (@lem124974) (@lem124973)). Qed.
Lemma lem124977 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem124978 (t : Prop) : (term21 t) = t.
Proof. exact (@lem124977 nat t). Qed.
Lemma lem124979 : term19 = True.
Proof. exact (@lem124978 True). Qed.
Lemma lem124980 : term18 = True.
Proof. exact (TRANS (@lem124975) (@lem124979)). Qed.
Lemma lem124981 : True = term18.
Proof. exact (SYM (@lem124980)). Qed.
Lemma lem124982 : term18.
Proof. exact (EQ_MP (@lem124981) (@lem0)). Qed.
