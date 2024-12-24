Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm89994_term_abbrevs.
Require Import thm89762_spec.
Require Import thm89943_spec.
Lemma lem89944 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem89945 : term1.
Proof. exact (EQ_MP (@lem89944) (@lem89762)). Qed.
Lemma lem89946 : term2.
Proof. exact (@lem89945 term3). Qed.
Lemma lem89947 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem89948 : term4.
Proof. exact (EQ_MP (@lem89947) (@lem89946)). Qed.
Lemma lem89949 (h1 : Peano.lt = term5) : Peano.lt = term5.
Proof. exact (h1). Qed.
Lemma lem89950 (h1 : Peano.lt = term5) : term5 = Peano.lt.
Proof. exact (SYM (@lem89949 h1)). Qed.
Lemma lem89951 (h1 : term5 = Peano.lt) : term5 = Peano.lt.
Proof. exact (h1). Qed.
Lemma lem89952 (h1 : term5 = Peano.lt) : Peano.lt = term5.
Proof. exact (SYM (@lem89951 h1)). Qed.
Lemma lem89953 : (Peano.lt = term5) = (term5 = Peano.lt).
Proof. exact (prop_ext (fun h1 : Peano.lt = term5 => @lem89950 h1) (fun h1 : term5 = Peano.lt => @lem89952 h1)). Qed.
Lemma lem89956 : term5 = Peano.lt.
Proof. exact (EQ_MP (@lem89953) (@lem89943)). Qed.
Lemma lem89957 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89958 (m : nat) : (term6 m) = (Peano.lt m).
Proof. exact (MK_COMB (@lem89956) (@lem89957 m)). Qed.
Lemma lem89959 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem89960 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem89958 m) (@lem89959)). Qed.
Lemma lem89961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89962 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem89961) (@lem89960 m)). Qed.
Lemma lem89963 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem89964 (m : nat) : ((term7 m) = False) = ((term8 m) = False).
Proof. exact (MK_COMB (@lem89962 m) (@lem89963)). Qed.
Lemma lem89965 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem89964 m)). Qed.
Lemma lem89966 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89967 : term13 = term14.
Proof. exact (MK_COMB (@lem89966) (@lem89965)). Qed.
Lemma lem89968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem89969 : term15 = term16.
Proof. exact (MK_COMB (@lem89968) (@lem89967)). Qed.
Lemma lem89971 : term5 = Peano.lt.
Proof. exact (EQ_MP (@lem89953) (@lem89943)). Qed.
Lemma lem89972 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89973 (m : nat) : (term6 m) = (Peano.lt m).
Proof. exact (MK_COMB (@lem89971) (@lem89972 m)). Qed.
Lemma lem89974 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem89975 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem89973 m) (@lem89974 n)). Qed.
Lemma lem89976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89977 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem89976) (@lem89975 m n)). Qed.
Lemma lem89979 : term5 = Peano.lt.
Proof. exact (EQ_MP (@lem89953) (@lem89943)). Qed.
Lemma lem89980 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89981 (m : nat) : (term6 m) = (Peano.lt m).
Proof. exact (MK_COMB (@lem89979) (@lem89980 m)). Qed.
Lemma lem89982 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89983 (m : nat) (n : nat) : (term21 m n) = (Peano.lt m n).
Proof. exact (MK_COMB (@lem89981 m) (@lem89982 n)). Qed.
Lemma lem89984 (m : nat) (n : nat) : (term22 m n) = (term22 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem89985 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem89984 m n) (@lem89983 m n)). Qed.
Lemma lem89986 (m : nat) (n : nat) : ((term17 m n) = (term23 m n)) = ((term18 m n) = (term24 m n)).
Proof. exact (MK_COMB (@lem89977 m n) (@lem89985 m n)). Qed.
Lemma lem89987 (m : nat) : (term25 m) = (term26 m).
Proof. exact (fun_ext (fun n : nat => @lem89986 m n)). Qed.
Lemma lem89988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89989 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem89988) (@lem89987 m)). Qed.
Lemma lem89990 : term29 = term30.
Proof. exact (fun_ext (fun m : nat => @lem89989 m)). Qed.
Lemma lem89991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89992 : term31 = term32.
Proof. exact (MK_COMB (@lem89991) (@lem89990)). Qed.
Lemma lem89993 : term4 = term33.
Proof. exact (MK_COMB (@lem89969) (@lem89992)). Qed.
Lemma lem89994 : term33.
Proof. exact (EQ_MP (@lem89993) (@lem89948)). Qed.
