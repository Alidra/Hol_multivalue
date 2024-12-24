Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_EQ_TRANS_term_abbrevs.
Require Import LE_ADD2_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1259719_spec.
Require Import thm1842_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1268061 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1268062 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1268061 h1 m). Qed.
Lemma lem1268063 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1268064 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1268063 m) (@lem1268062 m h1)). Qed.
Lemma lem1268065 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1268064 m h1 n). Qed.
Lemma lem1268066 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1268067 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem1268066 m n) (@lem1268065 m n h1)). Qed.
Lemma lem1268068 (m : nat) (n : nat) (p : nat) (h1 : term0) : term5 m n p.
Proof. exact (@lem1268067 m n h1 p). Qed.
Lemma lem1268069 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1268070 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (EQ_MP (@lem1268069 m n p) (@lem1268068 m n p h1)). Qed.
Lemma lem1268071 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term7 m n p q.
Proof. exact (@lem1268070 m n p h1 q). Qed.
Lemma lem1268072 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1268073 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (EQ_MP (@lem1268072 m n p q) (@lem1268071 m n p q h1)). Qed.
Lemma lem1268074 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term9 m p n q.
Proof. exact (h1). Qed.
Lemma lem1268075 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1268073 m n p q h1 (@lem1268074 m p n q h2)). Qed.
Lemma lem1268076 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term11 m n p q.
Proof. exact (fun h0 : term0 => @lem1268075 m p n q h0 h1). Qed.
Lemma lem1268077 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1268078 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1268076 m p n q h2 (@lem1268077 h1)). Qed.
Lemma lem1268079 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (fun h0 : term9 m p n q => @lem1268078 m p n q h1 h0). Qed.
Lemma lem1268080 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (fun q : nat => @lem1268079 m n p q h1). Qed.
Lemma lem1268081 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun p : nat => @lem1268080 m n p h1). Qed.
Lemma lem1268082 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem1268081 m n h1). Qed.
Lemma lem1268083 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem1268082 m h1). Qed.
Lemma lem1268084 : term12.
Proof. exact (fun h0 : term0 => @lem1268083 h0). Qed.
Lemma lem1268085 : term0.
Proof. exact (@lem1268084 (@lem101399)). Qed.
Lemma lem1268086 (m : nat) : term1 m.
Proof. exact (@lem1268085 m). Qed.
Lemma lem1268087 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1268088 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1268087 m) (@lem1268086 m)). Qed.
Lemma lem1268089 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1268088 m n). Qed.
Lemma lem1268090 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1268091 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1268090 m n) (@lem1268089 m n)). Qed.
Lemma lem1268092 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1268091 m n p). Qed.
Lemma lem1268093 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1268094 (m : nat) (n : nat) (p : nat) : term6 m n p.
Proof. exact (EQ_MP (@lem1268093 m n p) (@lem1268092 m n p)). Qed.
Lemma lem1268095 (m : nat) (n : nat) (p : nat) (q : nat) : term7 m n p q.
Proof. exact (@lem1268094 m n p q). Qed.
Lemma lem1268096 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1268098 (m : nat) : term13 m.
Proof. exact (@lem1259719 m). Qed.
Lemma lem1268099 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1268100 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1268099 m) (@lem1268098 m)). Qed.
Lemma lem1268101 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1268100 m n). Qed.
Lemma lem1268102 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1268103 (m : nat) (n : nat) : term16 m n.
Proof. exact (EQ_MP (@lem1268102 m n) (@lem1268101 m n)). Qed.
Lemma lem1268104 (m : nat) (n : nat) (p : nat) : term17 m n p.
Proof. exact (@lem1268103 m n p). Qed.
Lemma lem1268105 (m : nat) (n : nat) (p : nat) : (term17 m n p) = (term18 m n p).
Proof. exact (eq_refl (term17 m n p)). Qed.
Lemma lem1268106 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (EQ_MP (@lem1268105 m n p) (@lem1268104 m n p)). Qed.
Lemma lem1268107 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1268108 (m : nat) (h1 : term19) : term20 m.
Proof. exact (@lem1268107 h1 m). Qed.
Lemma lem1268109 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1268110 (m : nat) (h1 : term19) : term21 m.
Proof. exact (EQ_MP (@lem1268109 m) (@lem1268108 m h1)). Qed.
Lemma lem1268111 (m : nat) (n : nat) (h1 : term19) : term22 m n.
Proof. exact (@lem1268110 m h1 n). Qed.
Lemma lem1268112 (n : nat) (m : nat) : (term22 m n) = (term23 n m).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1268113 (n : nat) (m : nat) (h1 : term19) : term23 n m.
Proof. exact (EQ_MP (@lem1268112 n m) (@lem1268111 m n h1)). Qed.
Lemma lem1268114 (n : nat) (m : nat) (p : nat) (h1 : term19) : term24 n m p.
Proof. exact (@lem1268113 n m h1 p). Qed.
Lemma lem1268115 (n : nat) (m : nat) (p : nat) : (term24 n m p) = (term25 n m p).
Proof. exact (eq_refl (term24 n m p)). Qed.
Lemma lem1268116 (n : nat) (m : nat) (p : nat) (h1 : term19) : term25 n m p.
Proof. exact (EQ_MP (@lem1268115 n m p) (@lem1268114 n m p h1)). Qed.
Lemma lem1268117 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1268118 (p : nat) (m : nat) (n : nat) (h1 : term19) (h2 : Peano.le m n) : term26 n m p.
Proof. exact (@lem1268116 n m p h1 (@lem1268117 m n h2)). Qed.
Lemma lem1268119 (m : nat) (n : nat) (h1 : term19) (h2 : Peano.le m n) : term27 n m.
Proof. exact (fun p : nat => @lem1268118 p m n h1 h2). Qed.
Lemma lem1268120 (n : nat) (m : nat) (h1 : term19) : term28 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1268119 m n h1 h0). Qed.
Lemma lem1268121 (m : nat) (h1 : term19) : term29 m.
Proof. exact (fun n : nat => @lem1268120 n m h1). Qed.
Lemma lem1268122 (h1 : term19) : term30.
Proof. exact (fun m : nat => @lem1268121 m h1). Qed.
Lemma lem1268123 : term31.
Proof. exact (fun h0 : term19 => @lem1268122 h0). Qed.
Lemma lem1268124 : term30.
Proof. exact (@lem1268123 (@lem272809)). Qed.
Lemma lem1268125 (m : nat) : term32 m.
Proof. exact (@lem1268124 m). Qed.
Lemma lem1268126 (m : nat) : (term32 m) = (term29 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1268127 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1268126 m) (@lem1268125 m)). Qed.
Lemma lem1268128 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1268127 m n). Qed.
Lemma lem1268129 (n : nat) (m : nat) : (term33 m n) = (term28 n m).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1268132 (n : nat) (m : nat) : term28 n m.
Proof. exact (EQ_MP (@lem1268129 n m) (@lem1268128 m n)). Qed.
Lemma lem1268133 (n : nat) (m : nat) (p : nat) : term34 n m p.
Proof. exact (@lem1268132 (term35 m n p) (term36 m p)). Qed.
Lemma lem1268134 (n : nat) (m : nat) (p : nat) : term37 n m p.
Proof. exact (@lem1268133 n m p (@lem1268106 m n p)). Qed.
Lemma lem1268135 (n : nat) (m : nat) : term38 n m.
Proof. exact (fun p : nat => @lem1268134 n m p). Qed.
Lemma lem1268136 (n : nat) : term39 n.
Proof. exact (fun m : nat => @lem1268135 n m). Qed.
Lemma lem1268137 : term40.
Proof. exact (fun n : nat => @lem1268136 n). Qed.
Lemma lem1268138 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1268139 (n : nat) (h1 : term40) : term41 n.
Proof. exact (@lem1268138 h1 n). Qed.
Lemma lem1268140 (n : nat) : (term41 n) = (term39 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem1268141 (n : nat) (h1 : term40) : term39 n.
Proof. exact (EQ_MP (@lem1268140 n) (@lem1268139 n h1)). Qed.
Lemma lem1268142 (n : nat) (m : nat) (h1 : term40) : term42 n m.
Proof. exact (@lem1268141 n h1 m). Qed.
Lemma lem1268143 (n : nat) (m : nat) : (term42 n m) = (term38 n m).
Proof. exact (eq_refl (term42 n m)). Qed.
Lemma lem1268144 (n : nat) (m : nat) (h1 : term40) : term38 n m.
Proof. exact (EQ_MP (@lem1268143 n m) (@lem1268142 n m h1)). Qed.
Lemma lem1268145 (n : nat) (m : nat) (p : nat) (h1 : term40) : term43 n m p.
Proof. exact (@lem1268144 n m h1 p). Qed.
Lemma lem1268146 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term37 n m p).
Proof. exact (eq_refl (term43 n m p)). Qed.
Lemma lem1268147 (n : nat) (m : nat) (p : nat) (h1 : term40) : term37 n m p.
Proof. exact (EQ_MP (@lem1268146 n m p) (@lem1268145 n m p h1)). Qed.
Lemma lem1268148 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term40) : term44 n m p p'.
Proof. exact (@lem1268147 n m p h1 p'). Qed.
Lemma lem1268149 (n : nat) (m : nat) (p : nat) (p' : nat) : (term44 n m p p') = (term45 n m p p').
Proof. exact (eq_refl (term44 n m p p')). Qed.
Lemma lem1268150 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term40) : term45 n m p p'.
Proof. exact (EQ_MP (@lem1268149 n m p p') (@lem1268148 n m p p' h1)). Qed.
Lemma lem1268151 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term46 m n p p') : term46 m n p p'.
Proof. exact (h1). Qed.
Lemma lem1268152 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term40) (h2 : term46 m n p p') : term47 m p p'.
Proof. exact (@lem1268150 n m p p' h1 (@lem1268151 m n p p' h2)). Qed.
Lemma lem1268153 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term46 m n p p') : term48 m p p'.
Proof. exact (fun h0 : term40 => @lem1268152 m n p p' h0 h1). Qed.
Lemma lem1268154 (m : nat) (p : nat) (p' : nat) (h1 : term49 m p p') : term49 m p p'.
Proof. exact (h1). Qed.
Lemma lem1268155 (m : nat) (p : nat) (p' : nat) (h1 : term49 m p p') : term48 m p p'.
Proof. exact (ex_elim (@lem1268154 m p p' h1) (fun n : nat => fun h0 : term50 m p p' n => @lem1268153 m n p p' h0)). Qed.
Lemma lem1268156 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1268157 (m : nat) (p : nat) (p' : nat) (h1 : term40) (h2 : term49 m p p') : term47 m p p'.
Proof. exact (@lem1268155 m p p' h2 (@lem1268156 h1)). Qed.
Lemma lem1268158 (m : nat) (p : nat) (p' : nat) (h1 : term40) : term51 m p p'.
Proof. exact (fun h0 : term49 m p p' => @lem1268157 m p p' h1 h0). Qed.
Lemma lem1268159 (m : nat) (p : nat) (h1 : term40) : term52 m p.
Proof. exact (fun p' : nat => @lem1268158 m p p' h1). Qed.
Lemma lem1268160 (m : nat) (h1 : term40) : term53 m.
Proof. exact (fun p : nat => @lem1268159 m p h1). Qed.
Lemma lem1268161 (h1 : term40) : term54.
Proof. exact (fun m : nat => @lem1268160 m h1). Qed.
Lemma lem1268162 : term55.
Proof. exact (fun h0 : term40 => @lem1268161 h0). Qed.
Lemma lem1268163 : term54.
Proof. exact (@lem1268162 (@lem1268137)). Qed.
Lemma lem1268164 (m : nat) : term56 m.
Proof. exact (@lem1268163 m). Qed.
Lemma lem1268165 (m : nat) : (term56 m) = (term53 m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem1268166 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem1268165 m) (@lem1268164 m)). Qed.
Lemma lem1268167 (m : nat) (p : nat) : term57 m p.
Proof. exact (@lem1268166 m p). Qed.
Lemma lem1268168 (m : nat) (p : nat) : (term57 m p) = (term52 m p).
Proof. exact (eq_refl (term57 m p)). Qed.
Lemma lem1268169 (m : nat) (p : nat) : term52 m p.
Proof. exact (EQ_MP (@lem1268168 m p) (@lem1268167 m p)). Qed.
Lemma lem1268170 (m : nat) (p : nat) (p' : nat) : term58 m p p'.
Proof. exact (@lem1268169 m p p'). Qed.
Lemma lem1268171 (m : nat) (p : nat) (p' : nat) : (term58 m p p') = (term51 m p p').
Proof. exact (eq_refl (term58 m p p')). Qed.
Lemma lem1268173 (x : nadd) : term59 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1268174 (x : nadd) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1268175 (x : nadd) : term60 x.
Proof. exact (EQ_MP (@lem1268174 x) (@lem1268173 x)). Qed.
Lemma lem1268176 (x : nadd) (y : nadd) : term61 x y.
Proof. exact (@lem1268175 x y). Qed.
Lemma lem1268177 (x : nadd) (y : nadd) : (term61 x y) = ((nadd_eq x y) = (term62 x y)).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1268184 (x : nadd) (y : nadd) : (nadd_eq x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1268177 x y) (@lem1268176 x y)). Qed.
Lemma lem1268193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1268194 (x : nadd) (y : nadd) : (term63 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1268193) (@lem1268184 x y)). Qed.
Lemma lem1268196 (x : nadd) (y : nadd) : (nadd_eq x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1268177 x y) (@lem1268176 x y)). Qed.
Lemma lem1268197 (y : nadd) (z : nadd) : (nadd_eq y z) = (term62 y z).
Proof. exact (@lem1268196 y z). Qed.
Lemma lem1268206 (x : nadd) (y : nadd) (z : nadd) : (term65 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1268194 x y) (@lem1268197 y z)). Qed.
Lemma lem1268209 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1268210 (x : nadd) (y : nadd) (z : nadd) : (term67 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1268209) (@lem1268206 x y z)). Qed.
Lemma lem1268212 (x : nadd) (y : nadd) : (nadd_eq x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1268177 x y) (@lem1268176 x y)). Qed.
Lemma lem1268213 (x : nadd) (z : nadd) : (nadd_eq x z) = (term62 x z).
Proof. exact (@lem1268212 x z). Qed.
Lemma lem1268222 (y : nadd) (x : nadd) (z : nadd) : (term69 y x z) = (term70 y x z).
Proof. exact (MK_COMB (@lem1268210 x y z) (@lem1268213 x z)). Qed.
Lemma lem1268225 (y : nadd) (x : nadd) (z : nadd) : (term70 y x z) = (term69 y x z).
Proof. exact (SYM (@lem1268222 y x z)). Qed.
Lemma lem1268226 (x : nadd) (y : nadd) (z : nadd) (h1 : term66 x y z) : term66 x y z.
Proof. exact (h1). Qed.
Lemma lem1268227 (y : nadd) (z : nadd) (h1 : term62 y z) : term62 y z.
Proof. exact (h1). Qed.
Lemma lem1268228 (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 y z B2) : term71 y z B2.
Proof. exact (h1). Qed.
Lemma lem1268229 (x : nadd) (y : nadd) (h1 : term62 x y) : term62 x y.
Proof. exact (h1). Qed.
Lemma lem1268230 (x : nadd) (y : nadd) (B1 : nat) (h1 : term71 x y B1) : term71 x y B1.
Proof. exact (h1). Qed.
Lemma lem1268232 (m : nat) (p : nat) (p' : nat) : term51 m p p'.
Proof. exact (EQ_MP (@lem1268171 m p p') (@lem1268170 m p p')). Qed.
Lemma lem1268233 (x : nadd) (z : nadd) (n : nat) (B1 : nat) (B2 : nat) : term72 x z n B1 B2.
Proof. exact (@lem1268232 (dest_nadd x n) (dest_nadd z n) (Nat.add B1 B2)). Qed.
Lemma lem1268235 (m : nat) (n : nat) (p : nat) (q : nat) : term8 m n p q.
Proof. exact (EQ_MP (@lem1268096 m n p q) (@lem1268095 m n p q)). Qed.
Lemma lem1268236 (x : nadd) (y : nadd) (z : nadd) (n : nat) (B1 : nat) (B2 : nat) : term73 x y z n B1 B2.
Proof. exact (@lem1268235 (term74 x y n) (term74 y z n) B1 B2). Qed.
Lemma lem1268237 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term71 x y B1) : term75 x y B1 n.
Proof. exact (@lem1268230 x y B1 h1 n). Qed.
Lemma lem1268238 (x : nadd) (y : nadd) (n : nat) (B1 : nat) : (term75 x y B1 n) = (term76 x y n B1).
Proof. exact (eq_refl (term75 x y B1 n)). Qed.
Lemma lem1268239 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term71 x y B1) : term76 x y n B1.
Proof. exact (EQ_MP (@lem1268238 x y n B1) (@lem1268237 n x y B1 h1)). Qed.
Lemma lem1268240 (x : nadd) (y : nadd) (n : nat) (B1 : nat) : (term76 x y n B1) = ((term76 x y n B1) = True).
Proof. exact (@lem7 (term76 x y n B1)). Qed.
Lemma lem1268242 (n : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 y z B2) : term75 y z B2 n.
Proof. exact (@lem1268228 y z B2 h1 n). Qed.
Lemma lem1268243 (y : nadd) (z : nadd) (n : nat) (B2 : nat) : (term75 y z B2 n) = (term76 y z n B2).
Proof. exact (eq_refl (term75 y z B2 n)). Qed.
Lemma lem1268244 (n : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 y z B2) : term76 y z n B2.
Proof. exact (EQ_MP (@lem1268243 y z n B2) (@lem1268242 n y z B2 h1)). Qed.
Lemma lem1268245 (y : nadd) (z : nadd) (n : nat) (B2 : nat) : (term76 y z n B2) = ((term76 y z n B2) = True).
Proof. exact (@lem7 (term76 y z n B2)). Qed.
Lemma lem1268250 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term71 x y B1) : (term76 x y n B1) = True.
Proof. exact (EQ_MP (@lem1268240 x y n B1) (@lem1268239 n x y B1 h1)). Qed.
Lemma lem1268251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1268252 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term71 x y B1) : (term77 x y n B1) = (and True).
Proof. exact (MK_COMB (@lem1268251) (@lem1268250 n x y B1 h1)). Qed.
Lemma lem1268254 (n : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 y z B2) : (term76 y z n B2) = True.
Proof. exact (EQ_MP (@lem1268245 y z n B2) (@lem1268244 n y z B2 h1)). Qed.
Lemma lem1268255 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : (term78 x B1 y z n B2) = (True /\ True).
Proof. exact (MK_COMB (@lem1268252 n x y B1 h1) (@lem1268254 n y z B2 h2)). Qed.
Lemma lem1268257 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1268258 : (True /\ True) = True.
Proof. exact (@lem1268257 True). Qed.
Lemma lem1268259 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : (term78 x B1 y z n B2) = True.
Proof. exact (TRANS (@lem1268255 n x B1 y z B2 h1 h2) (@lem1268258)). Qed.
Lemma lem1268260 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : True = (term78 x B1 y z n B2).
Proof. exact (SYM (@lem1268259 n x B1 y z B2 h1 h2)). Qed.
Lemma lem1268261 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : term78 x B1 y z n B2.
Proof. exact (EQ_MP (@lem1268260 n x B1 y z B2 h1 h2) (@lem0)). Qed.
Lemma lem1268262 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : term79 x y z n B1 B2.
Proof. exact (@lem1268236 x y z n B1 B2 (@lem1268261 n x B1 y z B2 h1 h2)). Qed.
Lemma lem1268263 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : term80 x z n B1 B2.
Proof. exact (ex_intro (term81 x z n B1 B2) (dest_nadd y n) (@lem1268262 n x B1 y z B2 h1 h2)). Qed.
Lemma lem1268264 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : term82 x z n B1 B2.
Proof. exact (@lem1268233 x z n B1 B2 (@lem1268263 n x B1 y z B2 h1 h2)). Qed.
Lemma lem1268269 (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : term83 x z B1 B2.
Proof. exact (fun n : nat => @lem1268264 n x B1 y z B2 h1 h2). Qed.
Lemma lem1268270 (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term71 x y B1) (h2 : term71 y z B2) : term62 x z.
Proof. exact (ex_intro (term84 x z) (Nat.add B1 B2) (@lem1268269 x B1 y z B2 h1 h2)). Qed.
Lemma lem1268271 (x : nadd) (y : nadd) (z : nadd) (h1 : term66 x y z) : term62 y z.
Proof. exact (proj2 (@lem1268226 x y z h1)). Qed.
Lemma lem1268272 (x : nadd) (y : nadd) (z : nadd) (h1 : term66 x y z) : term62 x y.
Proof. exact (proj1 (@lem1268226 x y z h1)). Qed.
Lemma lem1268273 (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (h1 : term71 x y B1) (h2 : term62 y z) : term62 x z.
Proof. exact (ex_elim (@lem1268227 y z h2) (fun B2 : nat => fun h0 : term84 y z B2 => @lem1268270 x B1 y z B2 h1 h0)). Qed.
Lemma lem1268274 (x : nadd) (y : nadd) (z : nadd) (h1 : term62 x y) (h2 : term62 y z) : term62 x z.
Proof. exact (ex_elim (@lem1268229 x y h1) (fun B1 : nat => fun h0 : term84 x y B1 => @lem1268273 x B1 y z h0 h2)). Qed.
Lemma lem1268275 (x : nadd) (y : nadd) (z : nadd) (h1 : term62 x y) (h2 : term66 x y z) : (term62 y z) = (term62 x z).
Proof. exact (prop_ext (fun h3 : term62 y z => @lem1268274 x y z h1 h3) (fun h3 : term62 x z => @lem1268271 x y z h2)). Qed.
Lemma lem1268276 (x : nadd) (y : nadd) (z : nadd) (h1 : term62 x y) (h2 : term66 x y z) : term62 x z.
Proof. exact (EQ_MP (@lem1268275 x y z h1 h2) (@lem1268271 x y z h2)). Qed.
Lemma lem1268277 (x : nadd) (y : nadd) (z : nadd) (h1 : term66 x y z) : (term62 x y) = (term62 x z).
Proof. exact (prop_ext (fun h2 : term62 x y => @lem1268276 x y z h2 h1) (fun h2 : term62 x z => @lem1268272 x y z h1)). Qed.
Lemma lem1268278 (x : nadd) (y : nadd) (z : nadd) (h1 : term66 x y z) : term62 x z.
Proof. exact (EQ_MP (@lem1268277 x y z h1) (@lem1268272 x y z h1)). Qed.
Lemma lem1268279 (y : nadd) (x : nadd) (z : nadd) : term70 y x z.
Proof. exact (fun h0 : term66 x y z => @lem1268278 x y z h0). Qed.
Lemma lem1268280 (y : nadd) (x : nadd) (z : nadd) : term69 y x z.
Proof. exact (EQ_MP (@lem1268225 y x z) (@lem1268279 y x z)). Qed.
Lemma lem1268285 (y : nadd) (x : nadd) : term85 y x.
Proof. exact (fun z : nadd => @lem1268280 y x z). Qed.
Lemma lem1268290 (x : nadd) : term86 x.
Proof. exact (fun y : nadd => @lem1268285 y x). Qed.
Lemma lem1268295 : term87.
Proof. exact (fun x : nadd => @lem1268290 x). Qed.
