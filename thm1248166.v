Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248166_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1248147 (_22840 : nat) (_22841 : nat) (d : nat) (n : nat) (q : nat) : (term0 d n q _22841 _22840) = (term1 _22840 _22841 d n q).
Proof. exact (@lem1246844 _22840 _22841 (term2 d n q)). Qed.
Lemma lem1248148 (p : nat) (d : nat) (n : nat) (q : nat) : (term3 d n p q) = (term4 p d n q).
Proof. exact (@lem1248147 (Nat.add p q) (term5 p d n) d n q). Qed.
Lemma lem1248149 (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 d n q d') = (term7 d d' n q).
Proof. exact (eq_refl (term6 d n q d')). Qed.
Lemma lem1248150 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term8 q p d n d') = (term8 q p d n d').
Proof. exact (eq_refl (term8 q p d n d')). Qed.
Lemma lem1248151 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term9 p d n q d') = (term10 p d d' n q).
Proof. exact (MK_COMB (@lem1248150 q p d n d') (@lem1248149 d d' n q)). Qed.
Lemma lem1248152 (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 d n q d') = (term7 d d' n q).
Proof. exact (eq_refl (term6 d n q d')). Qed.
Lemma lem1248153 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) : (term11 d n p q d') = (term11 d n p q d').
Proof. exact (eq_refl (term11 d n p q d')). Qed.
Lemma lem1248154 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term12 p d n q d') = (term13 p d d' n q).
Proof. exact (MK_COMB (@lem1248153 d n p q d') (@lem1248152 d d' n q)). Qed.
Lemma lem1248155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1248156 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term14 p d n q d') = (term15 p d d' n q).
Proof. exact (MK_COMB (@lem1248155) (@lem1248154 p d d' n q)). Qed.
Lemma lem1248157 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term16 p d n q d') = (term17 p d d' n q).
Proof. exact (MK_COMB (@lem1248156 p d d' n q) (@lem1248151 p d d' n q)). Qed.
Lemma lem1248158 (p : nat) (d : nat) (n : nat) (q : nat) : (term18 p d n q) = (term19 p d n q).
Proof. exact (fun_ext (fun d' : nat => @lem1248157 p d d' n q)). Qed.
Lemma lem1248159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1248160 (p : nat) (d : nat) (n : nat) (q : nat) : (term4 p d n q) = (term20 p d n q).
Proof. exact (MK_COMB (@lem1248159) (@lem1248158 p d n q)). Qed.
Lemma lem1248161 (d : nat) (p : nat) (n : nat) (q : nat) : (term3 d n p q) = (term21 d p n q).
Proof. exact (eq_refl (term3 d n p q)). Qed.
Lemma lem1248162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248163 (d : nat) (p : nat) (n : nat) (q : nat) : (term22 d n p q) = (term23 d p n q).
Proof. exact (MK_COMB (@lem1248162) (@lem1248161 d p n q)). Qed.
Lemma lem1248164 (p : nat) (d : nat) (n : nat) (q : nat) : ((term3 d n p q) = (term4 p d n q)) = ((term21 d p n q) = (term20 p d n q)).
Proof. exact (MK_COMB (@lem1248163 d p n q) (@lem1248160 p d n q)). Qed.
Lemma lem1248165 (p : nat) (d : nat) (n : nat) (q : nat) : (term21 d p n q) = (term20 p d n q).
Proof. exact (EQ_MP (@lem1248164 p d n q) (@lem1248148 p d n q)). Qed.
Lemma lem1248166 (d : nat) (p : nat) (n : nat) (q : nat) : (term20 p d n q) = (term21 d p n q).
Proof. exact (SYM (@lem1248165 p d n q)). Qed.
