Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA2_term_abbrevs.
Require Import NADD_MUL_LINV_LEMMA1_spec.
Require Import NADD_NONZERO_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem1302076 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1302077 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1302076 h1 x). Qed.
Lemma lem1302078 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1302079 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1302078 x) (@lem1302077 x h1)). Qed.
Lemma lem1302080 (x : nadd) (n : nat) (h1 : term0) : term3 x n.
Proof. exact (@lem1302079 x h1 n). Qed.
Lemma lem1302081 (x : nadd) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1302082 (x : nadd) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (EQ_MP (@lem1302081 x n) (@lem1302080 x n h1)). Qed.
Lemma lem1302083 (x : nadd) (n : nat) (h1 : term5 x n) : term5 x n.
Proof. exact (h1). Qed.
Lemma lem1302084 (x : nadd) (n : nat) (h1 : term0) (h2 : term5 x n) : term6 x n.
Proof. exact (@lem1302082 x n h1 (@lem1302083 x n h2)). Qed.
Lemma lem1302085 (x : nadd) (n : nat) (h1 : term5 x n) : term7 x n.
Proof. exact (fun h0 : term0 => @lem1302084 x n h0 h1). Qed.
Lemma lem1302086 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1302087 (x : nadd) (n : nat) (h1 : term0) (h2 : term5 x n) : term6 x n.
Proof. exact (@lem1302085 x n h2 (@lem1302086 h1)). Qed.
Lemma lem1302088 (x : nadd) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (fun h0 : term5 x n => @lem1302087 x n h1 h0). Qed.
Lemma lem1302089 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (fun n : nat => @lem1302088 x n h1). Qed.
Lemma lem1302090 (h1 : term0) : term0.
Proof. exact (fun x : nadd => @lem1302089 x h1). Qed.
Lemma lem1302091 : term8.
Proof. exact (fun h0 : term0 => @lem1302090 h0). Qed.
Lemma lem1302092 : term0.
Proof. exact (@lem1302091 (@lem1302075)). Qed.
Lemma lem1302093 (x : nadd) : term1 x.
Proof. exact (@lem1302092 x). Qed.
Lemma lem1302094 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1302095 (x : nadd) : term2 x.
Proof. exact (EQ_MP (@lem1302094 x) (@lem1302093 x)). Qed.
Lemma lem1302096 (x : nadd) (n : nat) : term3 x n.
Proof. exact (@lem1302095 x n). Qed.
Lemma lem1302097 (x : nadd) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1302099 (x : nadd) : term9 x.
Proof. exact (@lem1299985 x). Qed.
Lemma lem1302100 (x : nadd) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1302102 (x : nadd) (h1 : term11 x) : term11 x.
Proof. exact (h1). Qed.
Lemma lem1302104 (x : nadd) : term10 x.
Proof. exact (EQ_MP (@lem1302100 x) (@lem1302099 x)). Qed.
Lemma lem1302105 (x : nadd) (h1 : term11 x) : term12 x.
Proof. exact (@lem1302104 x (@lem1302102 x h1)). Qed.
Lemma lem1302106 (x : nadd) (h1 : term12 x) : term12 x.
Proof. exact (h1). Qed.
Lemma lem1302107 (N : nat) (x : nadd) (h1 : term13 N x) : term13 N x.
Proof. exact (h1). Qed.
Lemma lem1302108 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302110 (x : nadd) (n : nat) : term4 x n.
Proof. exact (EQ_MP (@lem1302097 x n) (@lem1302096 x n)). Qed.
Lemma lem1302111 (N : nat) (x : nadd) (h1 : term13 N x) : term13 N x.
Proof. exact (h1). Qed.
Lemma lem1302112 (n : nat) (N : nat) (x : nadd) (h1 : term13 N x) : term14 N x n.
Proof. exact (@lem1302111 N x h1 n). Qed.
Lemma lem1302113 (N : nat) (x : nadd) (n : nat) : (term14 N x n) = (term15 N x n).
Proof. exact (eq_refl (term14 N x n)). Qed.
Lemma lem1302114 (n : nat) (N : nat) (x : nadd) (h1 : term13 N x) : term15 N x n.
Proof. exact (EQ_MP (@lem1302113 N x n) (@lem1302112 n N x h1)). Qed.
Lemma lem1302115 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302116 (x : nadd) (N : nat) (n : nat) (h1 : term13 N x) (h2 : Peano.le N n) : term5 x n.
Proof. exact (@lem1302114 n N x h1 (@lem1302115 N n h2)). Qed.
Lemma lem1302117 (x : nadd) (N : nat) (n : nat) (h1 : Peano.le N n) : term16 N x n.
Proof. exact (fun h0 : term13 N x => @lem1302116 x N n h0 h1). Qed.
Lemma lem1302118 (N : nat) (x : nadd) (h1 : term13 N x) : term13 N x.
Proof. exact (h1). Qed.
Lemma lem1302119 (x : nadd) (N : nat) (n : nat) (h1 : term13 N x) (h2 : Peano.le N n) : term5 x n.
Proof. exact (@lem1302117 x N n h2 (@lem1302118 N x h1)). Qed.
Lemma lem1302120 (n : nat) (N : nat) (x : nadd) (h1 : term13 N x) : term15 N x n.
Proof. exact (fun h0 : Peano.le N n => @lem1302119 x N n h1 h0). Qed.
Lemma lem1302121 (N : nat) (x : nadd) (h1 : term13 N x) : term13 N x.
Proof. exact (fun n : nat => @lem1302120 n N x h1). Qed.
Lemma lem1302122 (N : nat) (x : nadd) : term17 N x.
Proof. exact (fun h0 : term13 N x => @lem1302121 N x h0). Qed.
Lemma lem1302123 (N : nat) (x : nadd) (h1 : term13 N x) : term13 N x.
Proof. exact (@lem1302122 N x (@lem1302107 N x h1)). Qed.
Lemma lem1302124 (n : nat) (N : nat) (x : nadd) (h1 : term13 N x) : term14 N x n.
Proof. exact (@lem1302123 N x h1 n). Qed.
Lemma lem1302125 (N : nat) (x : nadd) (n : nat) : (term14 N x n) = (term15 N x n).
Proof. exact (eq_refl (term14 N x n)). Qed.
Lemma lem1302128 (n : nat) (N : nat) (x : nadd) (h1 : term13 N x) : term15 N x n.
Proof. exact (EQ_MP (@lem1302125 N x n) (@lem1302124 n N x h1)). Qed.
Lemma lem1302134 (N : nat) (n : nat) : (Peano.le N n) = ((Peano.le N n) = True).
Proof. exact (@lem7 (Peano.le N n)). Qed.
Lemma lem1302137 (N : nat) (n : nat) (h1 : Peano.le N n) : (Peano.le N n) = True.
Proof. exact (EQ_MP (@lem1302134 N n) (@lem1302108 N n h1)). Qed.
Lemma lem1302138 (N : nat) (n : nat) (h1 : Peano.le N n) : True = (Peano.le N n).
Proof. exact (SYM (@lem1302137 N n h1)). Qed.
Lemma lem1302139 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (EQ_MP (@lem1302138 N n h1) (@lem0)). Qed.
Lemma lem1302140 (x : nadd) (N : nat) (n : nat) (h1 : term13 N x) (h2 : Peano.le N n) : term5 x n.
Proof. exact (@lem1302128 n N x h1 (@lem1302139 N n h2)). Qed.
Lemma lem1302141 (x : nadd) (N : nat) (n : nat) (h1 : term13 N x) (h2 : Peano.le N n) : term6 x n.
Proof. exact (@lem1302110 x n (@lem1302140 x N n h1 h2)). Qed.
Lemma lem1302142 (x : nadd) (N : nat) (n : nat) (h1 : term13 N x) (h2 : Peano.le N n) : (Peano.le N n) = (term6 x n).
Proof. exact (prop_ext (fun h3 : Peano.le N n => @lem1302141 x N n h1 h2) (fun h3 : term6 x n => @lem1302108 N n h2)). Qed.
Lemma lem1302143 (x : nadd) (N : nat) (n : nat) (h1 : term13 N x) (h2 : Peano.le N n) : term6 x n.
Proof. exact (EQ_MP (@lem1302142 x N n h1 h2) (@lem1302108 N n h2)). Qed.
Lemma lem1302144 (n : nat) (N : nat) (x : nadd) (h1 : term13 N x) : term18 N x n.
Proof. exact (fun h0 : Peano.le N n => @lem1302143 x N n h1 h0). Qed.
Lemma lem1302149 (N : nat) (x : nadd) (h1 : term13 N x) : term19 N x.
Proof. exact (fun n : nat => @lem1302144 n N x h1). Qed.
Lemma lem1302150 (N : nat) (x : nadd) (h1 : term13 N x) : term20 x.
Proof. exact (ex_intro (term21 x) N (@lem1302149 N x h1)). Qed.
Lemma lem1302151 (x : nadd) (h1 : term12 x) : term20 x.
Proof. exact (ex_elim (@lem1302106 x h1) (fun N : nat => fun h0 : term22 x N => @lem1302150 N x h0)). Qed.
Lemma lem1302152 (x : nadd) : term23 x.
Proof. exact (fun h0 : term12 x => @lem1302151 x h0). Qed.
Lemma lem1302153 (x : nadd) (h1 : term11 x) : term20 x.
Proof. exact (@lem1302152 x (@lem1302105 x h1)). Qed.
Lemma lem1302154 (x : nadd) : term24 x.
Proof. exact (fun h0 : term11 x => @lem1302153 x h0). Qed.
Lemma lem1302159 : term25.
Proof. exact (fun x : nadd => @lem1302154 x). Qed.
