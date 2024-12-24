Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_EXISTS_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DIST_LMUL_spec.
Require Import DIST_RADD_0_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD2_spec.
Require Import LE_EXISTS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_REFL_spec.
Require Import MULT_SYM_spec.
Require Import NADD_ADD_spec.
Require Import NADD_CAUCHY_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import SKOLEM_THM_spec.
Require Import is_nadd_spec.
Require Import nadd_eq_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1247221_spec.
Require Import thm1259720_spec.
Require Import thm1259721_spec.
Require Import thm1262760_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1275086 (n : nat) (m : nat) (p : nat) (h1 : (term0 m n p) = (term1 n m p)) : (term0 m n p) = (term1 n m p).
Proof. exact (h1). Qed.
Lemma lem1275087 (n : nat) (m : nat) (p : nat) (h1 : (term0 m n p) = (term1 n m p)) : (term1 n m p) = (term0 m n p).
Proof. exact (SYM (@lem1275086 n m p h1)). Qed.
Lemma lem1275088 (m : nat) (n : nat) (p : nat) (h1 : (term1 n m p) = (term0 m n p)) : (term1 n m p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1275089 (m : nat) (n : nat) (p : nat) (h1 : (term1 n m p) = (term0 m n p)) : (term0 m n p) = (term1 n m p).
Proof. exact (SYM (@lem1275088 m n p h1)). Qed.
Lemma lem1275090 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 n m p)) = ((term1 n m p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 n m p) => @lem1275087 n m p h1) (fun h1 : (term1 n m p) = (term0 m n p) => @lem1275089 m n p h1)). Qed.
Lemma lem1275091 (m : nat) (n : nat) : (term2 n m) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1275090 m n p)). Qed.
Lemma lem1275092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275093 (m : nat) (n : nat) : (term4 n m) = (term5 m n).
Proof. exact (MK_COMB (@lem1275092) (@lem1275091 m n)). Qed.
Lemma lem1275094 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1275093 m n)). Qed.
Lemma lem1275095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275096 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1275095) (@lem1275094 m)). Qed.
Lemma lem1275097 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1275096 m)). Qed.
Lemma lem1275098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275099 : term12 = term13.
Proof. exact (MK_COMB (@lem1275098) (@lem1275097)). Qed.
Lemma lem1275100 : term13.
Proof. exact (EQ_MP (@lem1275099) (@lem1245388)). Qed.
Lemma lem1275101 (m : nat) : term14 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1275102 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1275103 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1275102 m) (@lem1275101 m)). Qed.
Lemma lem1275104 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1275103 m n). Qed.
Lemma lem1275105 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1275106 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1275105 m n) (@lem1275104 m n)). Qed.
Lemma lem1275107 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (@lem1275106 m n p). Qed.
Lemma lem1275108 (m : nat) (n : nat) (p : nat) : (term18 m n p) = ((term19 n m p) = (term20 m n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem1275110 (m : nat) : term21 m.
Proof. exact (@lem1247221 m). Qed.
Lemma lem1275111 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1275112 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1275111 m) (@lem1275110 m)). Qed.
Lemma lem1275113 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1275112 m n). Qed.
Lemma lem1275114 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1275115 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1275114 m n) (@lem1275113 m n)). Qed.
Lemma lem1275116 (m : nat) (n : nat) : (term24 m n) = ((term24 m n) = True).
Proof. exact (@lem7 (term24 m n)). Qed.
Lemma lem1275118 (m : nat) : term25 m.
Proof. exact (@lem1275100 m). Qed.
Lemma lem1275119 (m : nat) : (term25 m) = (term9 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem1275120 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1275119 m) (@lem1275118 m)). Qed.
Lemma lem1275121 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1275120 m n). Qed.
Lemma lem1275122 (m : nat) (n : nat) : (term26 m n) = (term5 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1275123 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1275122 m n) (@lem1275121 m n)). Qed.
Lemma lem1275124 (m : nat) (n : nat) (p : nat) : term27 m n p.
Proof. exact (@lem1275123 m n p). Qed.
Lemma lem1275125 (m : nat) (n : nat) (p : nat) : (term27 m n p) = ((term1 n m p) = (term0 m n p)).
Proof. exact (eq_refl (term27 m n p)). Qed.
Lemma lem1275127 (m : nat) : term28 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1275128 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1275129 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1275128 m) (@lem1275127 m)). Qed.
Lemma lem1275130 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1275129 m n). Qed.
Lemma lem1275131 (n : nat) (m : nat) : (term30 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1275133 (m : nat) : term31 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1275134 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1275135 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1275134 m) (@lem1275133 m)). Qed.
Lemma lem1275136 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1275135 m n). Qed.
Lemma lem1275137 (n : nat) (m : nat) : (term33 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1275139 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1275140 (m : nat) (h1 : term34) : term35 m.
Proof. exact (@lem1275139 h1 m). Qed.
Lemma lem1275141 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1275142 (m : nat) (h1 : term34) : term36 m.
Proof. exact (EQ_MP (@lem1275141 m) (@lem1275140 m h1)). Qed.
Lemma lem1275143 (m : nat) (n : nat) (h1 : term34) : term37 m n.
Proof. exact (@lem1275142 m h1 n). Qed.
Lemma lem1275144 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1275145 (m : nat) (n : nat) (h1 : term34) : term38 m n.
Proof. exact (EQ_MP (@lem1275144 m n) (@lem1275143 m n h1)). Qed.
Lemma lem1275146 (m : nat) (n : nat) (p : nat) (h1 : term34) : term39 m n p.
Proof. exact (@lem1275145 m n h1 p). Qed.
Lemma lem1275147 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term40 m n p).
Proof. exact (eq_refl (term39 m n p)). Qed.
Lemma lem1275148 (m : nat) (n : nat) (p : nat) (h1 : term34) : term40 m n p.
Proof. exact (EQ_MP (@lem1275147 m n p) (@lem1275146 m n p h1)). Qed.
Lemma lem1275149 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term34) : term41 m n p q.
Proof. exact (@lem1275148 m n p h1 q). Qed.
Lemma lem1275150 (m : nat) (n : nat) (p : nat) (q : nat) : (term41 m n p q) = (term42 m n p q).
Proof. exact (eq_refl (term41 m n p q)). Qed.
Lemma lem1275151 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term34) : term42 m n p q.
Proof. exact (EQ_MP (@lem1275150 m n p q) (@lem1275149 m n p q h1)). Qed.
Lemma lem1275152 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term43 m p n q) : term43 m p n q.
Proof. exact (h1). Qed.
Lemma lem1275153 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term34) (h2 : term43 m p n q) : term44 m n p q.
Proof. exact (@lem1275151 m n p q h1 (@lem1275152 m p n q h2)). Qed.
Lemma lem1275154 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term43 m p n q) : term45 m n p q.
Proof. exact (fun h0 : term34 => @lem1275153 m p n q h0 h1). Qed.
Lemma lem1275155 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1275156 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term34) (h2 : term43 m p n q) : term44 m n p q.
Proof. exact (@lem1275154 m p n q h2 (@lem1275155 h1)). Qed.
Lemma lem1275157 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term34) : term42 m n p q.
Proof. exact (fun h0 : term43 m p n q => @lem1275156 m p n q h1 h0). Qed.
Lemma lem1275158 (m : nat) (n : nat) (p : nat) (h1 : term34) : term40 m n p.
Proof. exact (fun q : nat => @lem1275157 m n p q h1). Qed.
Lemma lem1275159 (m : nat) (n : nat) (h1 : term34) : term38 m n.
Proof. exact (fun p : nat => @lem1275158 m n p h1). Qed.
Lemma lem1275160 (m : nat) (h1 : term34) : term36 m.
Proof. exact (fun n : nat => @lem1275159 m n h1). Qed.
Lemma lem1275161 (h1 : term34) : term34.
Proof. exact (fun m : nat => @lem1275160 m h1). Qed.
Lemma lem1275162 : term46.
Proof. exact (fun h0 : term34 => @lem1275161 h0). Qed.
Lemma lem1275163 : term34.
Proof. exact (@lem1275162 (@lem101399)). Qed.
Lemma lem1275164 (m : nat) : term35 m.
Proof. exact (@lem1275163 m). Qed.
Lemma lem1275165 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1275166 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1275165 m) (@lem1275164 m)). Qed.
Lemma lem1275167 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem1275166 m n). Qed.
Lemma lem1275168 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1275169 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem1275168 m n) (@lem1275167 m n)). Qed.
Lemma lem1275170 (m : nat) (n : nat) (p : nat) : term39 m n p.
Proof. exact (@lem1275169 m n p). Qed.
Lemma lem1275171 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term40 m n p).
Proof. exact (eq_refl (term39 m n p)). Qed.
Lemma lem1275172 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (EQ_MP (@lem1275171 m n p) (@lem1275170 m n p)). Qed.
Lemma lem1275173 (m : nat) (n : nat) (p : nat) (q : nat) : term41 m n p q.
Proof. exact (@lem1275172 m n p q). Qed.
Lemma lem1275174 (m : nat) (n : nat) (p : nat) (q : nat) : (term41 m n p q) = (term42 m n p q).
Proof. exact (eq_refl (term41 m n p q)). Qed.
Lemma lem1275176 (m : nat) : term31 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1275177 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1275178 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1275177 m) (@lem1275176 m)). Qed.
Lemma lem1275179 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1275178 m n). Qed.
Lemma lem1275180 (n : nat) (m : nat) : (term33 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1275182 (m : nat) : term47 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1275183 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1275184 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem1275183 m) (@lem1275182 m)). Qed.
Lemma lem1275185 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1275184 m n). Qed.
Lemma lem1275186 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1275187 (m : nat) (n : nat) : term50 m n.
Proof. exact (EQ_MP (@lem1275186 m n) (@lem1275185 m n)). Qed.
Lemma lem1275188 (m : nat) (n : nat) (p : nat) : term51 m n p.
Proof. exact (@lem1275187 m n p). Qed.
Lemma lem1275189 (m : nat) (n : nat) (p : nat) : (term51 m n p) = ((term52 m n p) = (term53 m n p)).
Proof. exact (eq_refl (term51 m n p)). Qed.
Lemma lem1275191 (m : nat) : term54 m.
Proof. exact (@lem1259721 m). Qed.
Lemma lem1275192 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem1275193 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem1275192 m) (@lem1275191 m)). Qed.
Lemma lem1275194 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem1275193 m n). Qed.
Lemma lem1275195 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem1275196 (m : nat) (n : nat) : term57 m n.
Proof. exact (EQ_MP (@lem1275195 m n) (@lem1275194 m n)). Qed.
Lemma lem1275197 (m : nat) (n : nat) (p : nat) : term58 m n p.
Proof. exact (@lem1275196 m n p). Qed.
Lemma lem1275198 (m : nat) (p : nat) (n : nat) : (term58 m n p) = (term59 m p n).
Proof. exact (eq_refl (term58 m n p)). Qed.
Lemma lem1275199 (m : nat) (p : nat) (n : nat) : term59 m p n.
Proof. exact (EQ_MP (@lem1275198 m p n) (@lem1275197 m n p)). Qed.
Lemma lem1275200 (m : nat) (p : nat) (n : nat) (q : nat) : term60 m p n q.
Proof. exact (@lem1275199 m p n q). Qed.
Lemma lem1275201 (m : nat) (p : nat) (n : nat) (q : nat) : (term60 m p n q) = (term61 m p n q).
Proof. exact (eq_refl (term60 m p n q)). Qed.
Lemma lem1275202 (m : nat) (p : nat) (n : nat) (q : nat) : term61 m p n q.
Proof. exact (EQ_MP (@lem1275201 m p n q) (@lem1275200 m p n q)). Qed.
Lemma lem1275203 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem1275204 (m : nat) (h1 : term62) : term63 m.
Proof. exact (@lem1275203 h1 m). Qed.
Lemma lem1275205 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1275206 (m : nat) (h1 : term62) : term64 m.
Proof. exact (EQ_MP (@lem1275205 m) (@lem1275204 m h1)). Qed.
Lemma lem1275207 (m : nat) (n : nat) (h1 : term62) : term65 m n.
Proof. exact (@lem1275206 m h1 n). Qed.
Lemma lem1275208 (n : nat) (m : nat) : (term65 m n) = (term66 n m).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1275209 (n : nat) (m : nat) (h1 : term62) : term66 n m.
Proof. exact (EQ_MP (@lem1275208 n m) (@lem1275207 m n h1)). Qed.
Lemma lem1275210 (n : nat) (m : nat) (p : nat) (h1 : term62) : term67 n m p.
Proof. exact (@lem1275209 n m h1 p). Qed.
Lemma lem1275211 (n : nat) (m : nat) (p : nat) : (term67 n m p) = (term68 n m p).
Proof. exact (eq_refl (term67 n m p)). Qed.
Lemma lem1275212 (n : nat) (m : nat) (p : nat) (h1 : term62) : term68 n m p.
Proof. exact (EQ_MP (@lem1275211 n m p) (@lem1275210 n m p h1)). Qed.
Lemma lem1275213 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1275214 (p : nat) (m : nat) (n : nat) (h1 : term62) (h2 : Peano.le m n) : term69 n m p.
Proof. exact (@lem1275212 n m p h1 (@lem1275213 m n h2)). Qed.
Lemma lem1275215 (m : nat) (n : nat) (h1 : term62) (h2 : Peano.le m n) : term70 n m.
Proof. exact (fun p : nat => @lem1275214 p m n h1 h2). Qed.
Lemma lem1275216 (n : nat) (m : nat) (h1 : term62) : term71 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1275215 m n h1 h0). Qed.
Lemma lem1275217 (m : nat) (h1 : term62) : term72 m.
Proof. exact (fun n : nat => @lem1275216 n m h1). Qed.
Lemma lem1275218 (h1 : term62) : term73.
Proof. exact (fun m : nat => @lem1275217 m h1). Qed.
Lemma lem1275219 : term74.
Proof. exact (fun h0 : term62 => @lem1275218 h0). Qed.
Lemma lem1275220 : term73.
Proof. exact (@lem1275219 (@lem272809)). Qed.
Lemma lem1275221 (m : nat) : term75 m.
Proof. exact (@lem1275220 m). Qed.
Lemma lem1275222 (m : nat) : (term75 m) = (term72 m).
Proof. exact (eq_refl (term75 m)). Qed.
Lemma lem1275223 (m : nat) : term72 m.
Proof. exact (EQ_MP (@lem1275222 m) (@lem1275221 m)). Qed.
Lemma lem1275224 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1275223 m n). Qed.
Lemma lem1275225 (n : nat) (m : nat) : (term76 m n) = (term71 n m).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem1275228 (n : nat) (m : nat) : term71 n m.
Proof. exact (EQ_MP (@lem1275225 n m) (@lem1275224 m n)). Qed.
Lemma lem1275229 (m : nat) (n : nat) (p : nat) (q : nat) : term77 m n p q.
Proof. exact (@lem1275228 (term78 m p n q) (term79 m n p q)). Qed.
Lemma lem1275230 (m : nat) (n : nat) (p : nat) (q : nat) : term80 m n p q.
Proof. exact (@lem1275229 m n p q (@lem1275202 m p n q)). Qed.
Lemma lem1275231 (m : nat) (n : nat) (p : nat) : term81 m n p.
Proof. exact (fun q : nat => @lem1275230 m n p q). Qed.
Lemma lem1275232 (m : nat) (n : nat) : term82 m n.
Proof. exact (fun p : nat => @lem1275231 m n p). Qed.
Lemma lem1275233 (m : nat) : term83 m.
Proof. exact (fun n : nat => @lem1275232 m n). Qed.
Lemma lem1275234 : term84.
Proof. exact (fun m : nat => @lem1275233 m). Qed.
Lemma lem1275235 (h1 : term84) : term84.
Proof. exact (h1). Qed.
Lemma lem1275236 (m : nat) (h1 : term84) : term85 m.
Proof. exact (@lem1275235 h1 m). Qed.
Lemma lem1275237 (m : nat) : (term85 m) = (term83 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem1275238 (m : nat) (h1 : term84) : term83 m.
Proof. exact (EQ_MP (@lem1275237 m) (@lem1275236 m h1)). Qed.
Lemma lem1275239 (m : nat) (n : nat) (h1 : term84) : term86 m n.
Proof. exact (@lem1275238 m h1 n). Qed.
Lemma lem1275240 (m : nat) (n : nat) : (term86 m n) = (term82 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem1275241 (m : nat) (n : nat) (h1 : term84) : term82 m n.
Proof. exact (EQ_MP (@lem1275240 m n) (@lem1275239 m n h1)). Qed.
Lemma lem1275242 (m : nat) (n : nat) (p : nat) (h1 : term84) : term87 m n p.
Proof. exact (@lem1275241 m n h1 p). Qed.
Lemma lem1275243 (m : nat) (n : nat) (p : nat) : (term87 m n p) = (term81 m n p).
Proof. exact (eq_refl (term87 m n p)). Qed.
Lemma lem1275244 (m : nat) (n : nat) (p : nat) (h1 : term84) : term81 m n p.
Proof. exact (EQ_MP (@lem1275243 m n p) (@lem1275242 m n p h1)). Qed.
Lemma lem1275245 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term84) : term88 m n p q.
Proof. exact (@lem1275244 m n p h1 q). Qed.
Lemma lem1275246 (m : nat) (n : nat) (p : nat) (q : nat) : (term88 m n p q) = (term80 m n p q).
Proof. exact (eq_refl (term88 m n p q)). Qed.
Lemma lem1275247 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term84) : term80 m n p q.
Proof. exact (EQ_MP (@lem1275246 m n p q) (@lem1275245 m n p q h1)). Qed.
Lemma lem1275248 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term84) : term89 m n p q p'.
Proof. exact (@lem1275247 m n p q h1 p'). Qed.
Lemma lem1275249 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term89 m n p q p') = (term90 m n p q p').
Proof. exact (eq_refl (term89 m n p q p')). Qed.
Lemma lem1275250 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term84) : term90 m n p q p'.
Proof. exact (EQ_MP (@lem1275249 m n p q p') (@lem1275248 m n p q p' h1)). Qed.
Lemma lem1275251 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term91 m p n q p') : term91 m p n q p'.
Proof. exact (h1). Qed.
Lemma lem1275252 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term84) (h2 : term91 m p n q p') : term92 m n p q p'.
Proof. exact (@lem1275250 m n p q p' h1 (@lem1275251 m p n q p' h2)). Qed.
Lemma lem1275253 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term91 m p n q p') : term93 m n p q p'.
Proof. exact (fun h0 : term84 => @lem1275252 m p n q p' h0 h1). Qed.
Lemma lem1275254 (h1 : term84) : term84.
Proof. exact (h1). Qed.
Lemma lem1275255 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term84) (h2 : term91 m p n q p') : term92 m n p q p'.
Proof. exact (@lem1275253 m p n q p' h2 (@lem1275254 h1)). Qed.
Lemma lem1275256 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term84) : term90 m n p q p'.
Proof. exact (fun h0 : term91 m p n q p' => @lem1275255 m p n q p' h1 h0). Qed.
Lemma lem1275257 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term84) : term80 m n p q.
Proof. exact (fun p' : nat => @lem1275256 m n p q p' h1). Qed.
Lemma lem1275258 (m : nat) (n : nat) (p : nat) (h1 : term84) : term81 m n p.
Proof. exact (fun q : nat => @lem1275257 m n p q h1). Qed.
Lemma lem1275259 (m : nat) (n : nat) (h1 : term84) : term82 m n.
Proof. exact (fun p : nat => @lem1275258 m n p h1). Qed.
Lemma lem1275260 (m : nat) (h1 : term84) : term83 m.
Proof. exact (fun n : nat => @lem1275259 m n h1). Qed.
Lemma lem1275261 (h1 : term84) : term84.
Proof. exact (fun m : nat => @lem1275260 m h1). Qed.
Lemma lem1275262 : term94.
Proof. exact (fun h0 : term84 => @lem1275261 h0). Qed.
Lemma lem1275263 : term84.
Proof. exact (@lem1275262 (@lem1275234)). Qed.
Lemma lem1275264 (m : nat) : term85 m.
Proof. exact (@lem1275263 m). Qed.
Lemma lem1275265 (m : nat) : (term85 m) = (term83 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem1275266 (m : nat) : term83 m.
Proof. exact (EQ_MP (@lem1275265 m) (@lem1275264 m)). Qed.
Lemma lem1275267 (m : nat) (n : nat) : term86 m n.
Proof. exact (@lem1275266 m n). Qed.
Lemma lem1275268 (m : nat) (n : nat) : (term86 m n) = (term82 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem1275269 (m : nat) (n : nat) : term82 m n.
Proof. exact (EQ_MP (@lem1275268 m n) (@lem1275267 m n)). Qed.
Lemma lem1275270 (m : nat) (n : nat) (p : nat) : term87 m n p.
Proof. exact (@lem1275269 m n p). Qed.
Lemma lem1275271 (m : nat) (n : nat) (p : nat) : (term87 m n p) = (term81 m n p).
Proof. exact (eq_refl (term87 m n p)). Qed.
Lemma lem1275272 (m : nat) (n : nat) (p : nat) : term81 m n p.
Proof. exact (EQ_MP (@lem1275271 m n p) (@lem1275270 m n p)). Qed.
Lemma lem1275273 (m : nat) (n : nat) (p : nat) (q : nat) : term88 m n p q.
Proof. exact (@lem1275272 m n p q). Qed.
Lemma lem1275274 (m : nat) (n : nat) (p : nat) (q : nat) : (term88 m n p q) = (term80 m n p q).
Proof. exact (eq_refl (term88 m n p q)). Qed.
Lemma lem1275275 (m : nat) (n : nat) (p : nat) (q : nat) : term80 m n p q.
Proof. exact (EQ_MP (@lem1275274 m n p q) (@lem1275273 m n p q)). Qed.
Lemma lem1275276 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term89 m n p q p'.
Proof. exact (@lem1275275 m n p q p'). Qed.
Lemma lem1275277 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term89 m n p q p') = (term90 m n p q p').
Proof. exact (eq_refl (term89 m n p q p')). Qed.
Lemma lem1275279 (m : nat) : term95 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1275280 (m : nat) : (term95 m) = (term96 m).
Proof. exact (eq_refl (term95 m)). Qed.
Lemma lem1275281 (m : nat) : term96 m.
Proof. exact (EQ_MP (@lem1275280 m) (@lem1275279 m)). Qed.
Lemma lem1275282 (m : nat) (n : nat) : term97 m n.
Proof. exact (@lem1275281 m n). Qed.
Lemma lem1275283 (n : nat) (m : nat) : (term97 m n) = (term98 n m).
Proof. exact (eq_refl (term97 m n)). Qed.
Lemma lem1275284 (n : nat) (m : nat) : term98 n m.
Proof. exact (EQ_MP (@lem1275283 n m) (@lem1275282 m n)). Qed.
Lemma lem1275285 (n : nat) (m : nat) (p : nat) : term99 n m p.
Proof. exact (@lem1275284 n m p). Qed.
Lemma lem1275286 (n : nat) (m : nat) (p : nat) : (term99 n m p) = ((term100 m n p) = (term101 n m p)).
Proof. exact (eq_refl (term99 n m p)). Qed.
Lemma lem1275291 (n : nat) (m : nat) (p : nat) (h1 : (term100 m n p) = (term101 n m p)) : (term100 m n p) = (term101 n m p).
Proof. exact (h1). Qed.
Lemma lem1275292 (n : nat) (m : nat) (p : nat) (h1 : (term100 m n p) = (term101 n m p)) : (term101 n m p) = (term100 m n p).
Proof. exact (SYM (@lem1275291 n m p h1)). Qed.
Lemma lem1275293 (m : nat) (n : nat) (p : nat) (h1 : (term101 n m p) = (term100 m n p)) : (term101 n m p) = (term100 m n p).
Proof. exact (h1). Qed.
Lemma lem1275294 (m : nat) (n : nat) (p : nat) (h1 : (term101 n m p) = (term100 m n p)) : (term100 m n p) = (term101 n m p).
Proof. exact (SYM (@lem1275293 m n p h1)). Qed.
Lemma lem1275295 (m : nat) (n : nat) (p : nat) : ((term100 m n p) = (term101 n m p)) = ((term101 n m p) = (term100 m n p)).
Proof. exact (prop_ext (fun h1 : (term100 m n p) = (term101 n m p) => @lem1275292 n m p h1) (fun h1 : (term101 n m p) = (term100 m n p) => @lem1275294 m n p h1)). Qed.
Lemma lem1275296 (m : nat) (n : nat) : (term102 n m) = (term103 m n).
Proof. exact (fun_ext (fun p : nat => @lem1275295 m n p)). Qed.
Lemma lem1275297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275298 (m : nat) (n : nat) : (term98 n m) = (term104 m n).
Proof. exact (MK_COMB (@lem1275297) (@lem1275296 m n)). Qed.
Lemma lem1275299 (m : nat) : (term105 m) = (term106 m).
Proof. exact (fun_ext (fun n : nat => @lem1275298 m n)). Qed.
Lemma lem1275300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275301 (m : nat) : (term96 m) = (term107 m).
Proof. exact (MK_COMB (@lem1275300) (@lem1275299 m)). Qed.
Lemma lem1275302 : term108 = term109.
Proof. exact (fun_ext (fun m : nat => @lem1275301 m)). Qed.
Lemma lem1275303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275304 : term110 = term111.
Proof. exact (MK_COMB (@lem1275303) (@lem1275302)). Qed.
Lemma lem1275305 : term111.
Proof. exact (EQ_MP (@lem1275304) (@lem82055)). Qed.
Lemma lem1275306 (m : nat) : term31 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1275307 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1275308 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1275307 m) (@lem1275306 m)). Qed.
Lemma lem1275309 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1275308 m n). Qed.
Lemma lem1275310 (n : nat) (m : nat) : (term33 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1275312 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1275313 (m : nat) (h1 : term34) : term35 m.
Proof. exact (@lem1275312 h1 m). Qed.
Lemma lem1275314 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1275315 (m : nat) (h1 : term34) : term36 m.
Proof. exact (EQ_MP (@lem1275314 m) (@lem1275313 m h1)). Qed.
Lemma lem1275316 (m : nat) (n : nat) (h1 : term34) : term37 m n.
Proof. exact (@lem1275315 m h1 n). Qed.
Lemma lem1275317 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1275318 (m : nat) (n : nat) (h1 : term34) : term38 m n.
Proof. exact (EQ_MP (@lem1275317 m n) (@lem1275316 m n h1)). Qed.
Lemma lem1275319 (m : nat) (n : nat) (p : nat) (h1 : term34) : term39 m n p.
Proof. exact (@lem1275318 m n h1 p). Qed.
Lemma lem1275320 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term40 m n p).
Proof. exact (eq_refl (term39 m n p)). Qed.
Lemma lem1275321 (m : nat) (n : nat) (p : nat) (h1 : term34) : term40 m n p.
Proof. exact (EQ_MP (@lem1275320 m n p) (@lem1275319 m n p h1)). Qed.
Lemma lem1275322 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term34) : term41 m n p q.
Proof. exact (@lem1275321 m n p h1 q). Qed.
Lemma lem1275323 (m : nat) (n : nat) (p : nat) (q : nat) : (term41 m n p q) = (term42 m n p q).
Proof. exact (eq_refl (term41 m n p q)). Qed.
Lemma lem1275324 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term34) : term42 m n p q.
Proof. exact (EQ_MP (@lem1275323 m n p q) (@lem1275322 m n p q h1)). Qed.
Lemma lem1275325 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term43 m p n q) : term43 m p n q.
Proof. exact (h1). Qed.
Lemma lem1275326 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term34) (h2 : term43 m p n q) : term44 m n p q.
Proof. exact (@lem1275324 m n p q h1 (@lem1275325 m p n q h2)). Qed.
Lemma lem1275327 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term43 m p n q) : term45 m n p q.
Proof. exact (fun h0 : term34 => @lem1275326 m p n q h0 h1). Qed.
Lemma lem1275328 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1275329 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term34) (h2 : term43 m p n q) : term44 m n p q.
Proof. exact (@lem1275327 m p n q h2 (@lem1275328 h1)). Qed.
Lemma lem1275330 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term34) : term42 m n p q.
Proof. exact (fun h0 : term43 m p n q => @lem1275329 m p n q h1 h0). Qed.
Lemma lem1275331 (m : nat) (n : nat) (p : nat) (h1 : term34) : term40 m n p.
Proof. exact (fun q : nat => @lem1275330 m n p q h1). Qed.
Lemma lem1275332 (m : nat) (n : nat) (h1 : term34) : term38 m n.
Proof. exact (fun p : nat => @lem1275331 m n p h1). Qed.
Lemma lem1275333 (m : nat) (h1 : term34) : term36 m.
Proof. exact (fun n : nat => @lem1275332 m n h1). Qed.
Lemma lem1275334 (h1 : term34) : term34.
Proof. exact (fun m : nat => @lem1275333 m h1). Qed.
Lemma lem1275335 : term46.
Proof. exact (fun h0 : term34 => @lem1275334 h0). Qed.
Lemma lem1275336 : term34.
Proof. exact (@lem1275335 (@lem101399)). Qed.
Lemma lem1275337 (m : nat) : term35 m.
Proof. exact (@lem1275336 m). Qed.
Lemma lem1275338 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1275339 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1275338 m) (@lem1275337 m)). Qed.
Lemma lem1275340 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem1275339 m n). Qed.
Lemma lem1275341 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1275342 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem1275341 m n) (@lem1275340 m n)). Qed.
Lemma lem1275343 (m : nat) (n : nat) (p : nat) : term39 m n p.
Proof. exact (@lem1275342 m n p). Qed.
Lemma lem1275344 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term40 m n p).
Proof. exact (eq_refl (term39 m n p)). Qed.
Lemma lem1275345 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (EQ_MP (@lem1275344 m n p) (@lem1275343 m n p)). Qed.
Lemma lem1275346 (m : nat) (n : nat) (p : nat) (q : nat) : term41 m n p q.
Proof. exact (@lem1275345 m n p q). Qed.
Lemma lem1275347 (m : nat) (n : nat) (p : nat) (q : nat) : (term41 m n p q) = (term42 m n p q).
Proof. exact (eq_refl (term41 m n p q)). Qed.
Lemma lem1275349 (m : nat) : term31 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1275350 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1275351 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1275350 m) (@lem1275349 m)). Qed.
Lemma lem1275352 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1275351 m n). Qed.
Lemma lem1275353 (n : nat) (m : nat) : (term33 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1275355 (m : nat) : term47 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1275356 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1275357 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem1275356 m) (@lem1275355 m)). Qed.
Lemma lem1275358 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1275357 m n). Qed.
Lemma lem1275359 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1275360 (m : nat) (n : nat) : term50 m n.
Proof. exact (EQ_MP (@lem1275359 m n) (@lem1275358 m n)). Qed.
Lemma lem1275361 (m : nat) (n : nat) (p : nat) : term51 m n p.
Proof. exact (@lem1275360 m n p). Qed.
Lemma lem1275362 (m : nat) (n : nat) (p : nat) : (term51 m n p) = ((term52 m n p) = (term53 m n p)).
Proof. exact (eq_refl (term51 m n p)). Qed.
Lemma lem1275364 (m : nat) : term112 m.
Proof. exact (@lem1259720 m). Qed.
Lemma lem1275365 (m : nat) : (term112 m) = (term113 m).
Proof. exact (eq_refl (term112 m)). Qed.
Lemma lem1275366 (m : nat) : term113 m.
Proof. exact (EQ_MP (@lem1275365 m) (@lem1275364 m)). Qed.
Lemma lem1275367 (m : nat) (n : nat) : term114 m n.
Proof. exact (@lem1275366 m n). Qed.
Lemma lem1275368 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (eq_refl (term114 m n)). Qed.
Lemma lem1275369 (m : nat) (n : nat) : term115 m n.
Proof. exact (EQ_MP (@lem1275368 m n) (@lem1275367 m n)). Qed.
Lemma lem1275370 (m : nat) (n : nat) (p : nat) : term116 m n p.
Proof. exact (@lem1275369 m n p). Qed.
Lemma lem1275371 (m : nat) (p : nat) (n : nat) : (term116 m n p) = (term117 m p n).
Proof. exact (eq_refl (term116 m n p)). Qed.
Lemma lem1275372 (m : nat) (p : nat) (n : nat) : term117 m p n.
Proof. exact (EQ_MP (@lem1275371 m p n) (@lem1275370 m n p)). Qed.
Lemma lem1275373 (m : nat) (p : nat) (n : nat) (q : nat) : term118 m p n q.
Proof. exact (@lem1275372 m p n q). Qed.
Lemma lem1275374 (m : nat) (p : nat) (n : nat) (q : nat) : (term118 m p n q) = (term119 m p n q).
Proof. exact (eq_refl (term118 m p n q)). Qed.
Lemma lem1275375 (m : nat) (p : nat) (n : nat) (q : nat) : term119 m p n q.
Proof. exact (EQ_MP (@lem1275374 m p n q) (@lem1275373 m p n q)). Qed.
Lemma lem1275376 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem1275377 (m : nat) (h1 : term62) : term63 m.
Proof. exact (@lem1275376 h1 m). Qed.
Lemma lem1275378 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1275379 (m : nat) (h1 : term62) : term64 m.
Proof. exact (EQ_MP (@lem1275378 m) (@lem1275377 m h1)). Qed.
Lemma lem1275380 (m : nat) (n : nat) (h1 : term62) : term65 m n.
Proof. exact (@lem1275379 m h1 n). Qed.
Lemma lem1275381 (n : nat) (m : nat) : (term65 m n) = (term66 n m).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1275382 (n : nat) (m : nat) (h1 : term62) : term66 n m.
Proof. exact (EQ_MP (@lem1275381 n m) (@lem1275380 m n h1)). Qed.
Lemma lem1275383 (n : nat) (m : nat) (p : nat) (h1 : term62) : term67 n m p.
Proof. exact (@lem1275382 n m h1 p). Qed.
Lemma lem1275384 (n : nat) (m : nat) (p : nat) : (term67 n m p) = (term68 n m p).
Proof. exact (eq_refl (term67 n m p)). Qed.
Lemma lem1275385 (n : nat) (m : nat) (p : nat) (h1 : term62) : term68 n m p.
Proof. exact (EQ_MP (@lem1275384 n m p) (@lem1275383 n m p h1)). Qed.
Lemma lem1275386 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1275387 (p : nat) (m : nat) (n : nat) (h1 : term62) (h2 : Peano.le m n) : term69 n m p.
Proof. exact (@lem1275385 n m p h1 (@lem1275386 m n h2)). Qed.
Lemma lem1275388 (m : nat) (n : nat) (h1 : term62) (h2 : Peano.le m n) : term70 n m.
Proof. exact (fun p : nat => @lem1275387 p m n h1 h2). Qed.
Lemma lem1275389 (n : nat) (m : nat) (h1 : term62) : term71 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1275388 m n h1 h0). Qed.
Lemma lem1275390 (m : nat) (h1 : term62) : term72 m.
Proof. exact (fun n : nat => @lem1275389 n m h1). Qed.
Lemma lem1275391 (h1 : term62) : term73.
Proof. exact (fun m : nat => @lem1275390 m h1). Qed.
Lemma lem1275392 : term74.
Proof. exact (fun h0 : term62 => @lem1275391 h0). Qed.
Lemma lem1275393 : term73.
Proof. exact (@lem1275392 (@lem272809)). Qed.
Lemma lem1275394 (m : nat) : term75 m.
Proof. exact (@lem1275393 m). Qed.
Lemma lem1275395 (m : nat) : (term75 m) = (term72 m).
Proof. exact (eq_refl (term75 m)). Qed.
Lemma lem1275396 (m : nat) : term72 m.
Proof. exact (EQ_MP (@lem1275395 m) (@lem1275394 m)). Qed.
Lemma lem1275397 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1275396 m n). Qed.
Lemma lem1275398 (n : nat) (m : nat) : (term76 m n) = (term71 n m).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem1275401 (n : nat) (m : nat) : term71 n m.
Proof. exact (EQ_MP (@lem1275398 n m) (@lem1275397 m n)). Qed.
Lemma lem1275402 (n : nat) (q : nat) (m : nat) (p : nat) : term120 n q m p.
Proof. exact (@lem1275401 (term121 m p n q) (term122 m p)). Qed.
Lemma lem1275403 (n : nat) (q : nat) (m : nat) (p : nat) : term123 n q m p.
Proof. exact (@lem1275402 n q m p (@lem1275375 m p n q)). Qed.
Lemma lem1275404 (n : nat) (q : nat) (m : nat) : term124 n q m.
Proof. exact (fun p : nat => @lem1275403 n q m p). Qed.
Lemma lem1275405 (n : nat) (q : nat) : term125 n q.
Proof. exact (fun m : nat => @lem1275404 n q m). Qed.
Lemma lem1275406 (n : nat) : term126 n.
Proof. exact (fun q : nat => @lem1275405 n q). Qed.
Lemma lem1275407 : term127.
Proof. exact (fun n : nat => @lem1275406 n). Qed.
Lemma lem1275408 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1275409 (n : nat) (h1 : term127) : term128 n.
Proof. exact (@lem1275408 h1 n). Qed.
Lemma lem1275410 (n : nat) : (term128 n) = (term126 n).
Proof. exact (eq_refl (term128 n)). Qed.
Lemma lem1275411 (n : nat) (h1 : term127) : term126 n.
Proof. exact (EQ_MP (@lem1275410 n) (@lem1275409 n h1)). Qed.
Lemma lem1275412 (n : nat) (q : nat) (h1 : term127) : term129 n q.
Proof. exact (@lem1275411 n h1 q). Qed.
Lemma lem1275413 (n : nat) (q : nat) : (term129 n q) = (term125 n q).
Proof. exact (eq_refl (term129 n q)). Qed.
Lemma lem1275414 (n : nat) (q : nat) (h1 : term127) : term125 n q.
Proof. exact (EQ_MP (@lem1275413 n q) (@lem1275412 n q h1)). Qed.
Lemma lem1275415 (n : nat) (q : nat) (m : nat) (h1 : term127) : term130 n q m.
Proof. exact (@lem1275414 n q h1 m). Qed.
Lemma lem1275416 (n : nat) (q : nat) (m : nat) : (term130 n q m) = (term124 n q m).
Proof. exact (eq_refl (term130 n q m)). Qed.
Lemma lem1275417 (n : nat) (q : nat) (m : nat) (h1 : term127) : term124 n q m.
Proof. exact (EQ_MP (@lem1275416 n q m) (@lem1275415 n q m h1)). Qed.
Lemma lem1275418 (n : nat) (q : nat) (m : nat) (p : nat) (h1 : term127) : term131 n q m p.
Proof. exact (@lem1275417 n q m h1 p). Qed.
Lemma lem1275419 (n : nat) (q : nat) (m : nat) (p : nat) : (term131 n q m p) = (term123 n q m p).
Proof. exact (eq_refl (term131 n q m p)). Qed.
Lemma lem1275420 (n : nat) (q : nat) (m : nat) (p : nat) (h1 : term127) : term123 n q m p.
Proof. exact (EQ_MP (@lem1275419 n q m p) (@lem1275418 n q m p h1)). Qed.
Lemma lem1275421 (n : nat) (q : nat) (m : nat) (p : nat) (p' : nat) (h1 : term127) : term132 n q m p p'.
Proof. exact (@lem1275420 n q m p h1 p'). Qed.
Lemma lem1275422 (n : nat) (q : nat) (m : nat) (p : nat) (p' : nat) : (term132 n q m p p') = (term133 n q m p p').
Proof. exact (eq_refl (term132 n q m p p')). Qed.
Lemma lem1275423 (n : nat) (q : nat) (m : nat) (p : nat) (p' : nat) (h1 : term127) : term133 n q m p p'.
Proof. exact (EQ_MP (@lem1275422 n q m p p') (@lem1275421 n q m p p' h1)). Qed.
Lemma lem1275424 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term134 m p n q p') : term134 m p n q p'.
Proof. exact (h1). Qed.
Lemma lem1275425 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term127) (h2 : term134 m p n q p') : term135 m p p'.
Proof. exact (@lem1275423 n q m p p' h1 (@lem1275424 m p n q p' h2)). Qed.
Lemma lem1275426 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term134 m p n q p') : term136 m p p'.
Proof. exact (fun h0 : term127 => @lem1275425 m p n q p' h0 h1). Qed.
Lemma lem1275427 (m : nat) (p : nat) (n : nat) (p' : nat) (h1 : term137 m p n p') : term137 m p n p'.
Proof. exact (h1). Qed.
Lemma lem1275428 (m : nat) (p : nat) (n : nat) (p' : nat) (h1 : term137 m p n p') : term136 m p p'.
Proof. exact (ex_elim (@lem1275427 m p n p' h1) (fun q : nat => fun h0 : term138 m p n p' q => @lem1275426 m p n q p' h0)). Qed.
Lemma lem1275429 (m : nat) (p : nat) (p' : nat) (h1 : term139 m p p') : term139 m p p'.
Proof. exact (h1). Qed.
Lemma lem1275430 (m : nat) (p : nat) (p' : nat) (h1 : term139 m p p') : term136 m p p'.
Proof. exact (ex_elim (@lem1275429 m p p' h1) (fun n : nat => fun h0 : term140 m p p' n => @lem1275428 m p n p' h0)). Qed.
Lemma lem1275431 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1275432 (m : nat) (p : nat) (p' : nat) (h1 : term127) (h2 : term139 m p p') : term135 m p p'.
Proof. exact (@lem1275430 m p p' h2 (@lem1275431 h1)). Qed.
Lemma lem1275433 (m : nat) (p : nat) (p' : nat) (h1 : term127) : term141 m p p'.
Proof. exact (fun h0 : term139 m p p' => @lem1275432 m p p' h1 h0). Qed.
Lemma lem1275434 (m : nat) (p : nat) (h1 : term127) : term142 m p.
Proof. exact (fun p' : nat => @lem1275433 m p p' h1). Qed.
Lemma lem1275435 (m : nat) (h1 : term127) : term143 m.
Proof. exact (fun p : nat => @lem1275434 m p h1). Qed.
Lemma lem1275436 (h1 : term127) : term144.
Proof. exact (fun m : nat => @lem1275435 m h1). Qed.
Lemma lem1275437 : term145.
Proof. exact (fun h0 : term127 => @lem1275436 h0). Qed.
Lemma lem1275438 : term144.
Proof. exact (@lem1275437 (@lem1275407)). Qed.
Lemma lem1275439 (m : nat) : term146 m.
Proof. exact (@lem1275438 m). Qed.
Lemma lem1275440 (m : nat) : (term146 m) = (term143 m).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem1275441 (m : nat) : term143 m.
Proof. exact (EQ_MP (@lem1275440 m) (@lem1275439 m)). Qed.
Lemma lem1275442 (m : nat) (p : nat) : term147 m p.
Proof. exact (@lem1275441 m p). Qed.
Lemma lem1275443 (m : nat) (p : nat) : (term147 m p) = (term142 m p).
Proof. exact (eq_refl (term147 m p)). Qed.
Lemma lem1275444 (m : nat) (p : nat) : term142 m p.
Proof. exact (EQ_MP (@lem1275443 m p) (@lem1275442 m p)). Qed.
Lemma lem1275445 (m : nat) (p : nat) (p' : nat) : term148 m p p'.
Proof. exact (@lem1275444 m p p'). Qed.
Lemma lem1275446 (m : nat) (p : nat) (p' : nat) : (term148 m p p') = (term141 m p p').
Proof. exact (eq_refl (term148 m p p')). Qed.
Lemma lem1275448 (y : nadd) : term149 y.
Proof. exact (@lem1262851 y). Qed.
Lemma lem1275449 (y : nadd) : (term149 y) = (term150 y).
Proof. exact (eq_refl (term149 y)). Qed.
Lemma lem1275450 (y : nadd) : term150 y.
Proof. exact (EQ_MP (@lem1275449 y) (@lem1275448 y)). Qed.
Lemma lem1275451 (y : nadd) (B2 : nat) (h1 : term151 y B2) : term151 y B2.
Proof. exact (h1). Qed.
Lemma lem1275452 (x : nadd) : term149 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1275453 (x : nadd) : (term149 x) = (term150 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1275454 (x : nadd) : term150 x.
Proof. exact (EQ_MP (@lem1275453 x) (@lem1275452 x)). Qed.
Lemma lem1275455 (x : nadd) (B1 : nat) (h1 : term151 x B1) : term151 x B1.
Proof. exact (h1). Qed.
Lemma lem1275456 (r : nat -> nat) (h1 : (is_nadd r) = ((term152 r) = r)) : (is_nadd r) = ((term152 r) = r).
Proof. exact (h1). Qed.
Lemma lem1275457 (r : nat -> nat) (h1 : (is_nadd r) = ((term152 r) = r)) : ((term152 r) = r) = (is_nadd r).
Proof. exact (SYM (@lem1275456 r h1)). Qed.
Lemma lem1275458 (r : nat -> nat) (h1 : ((term152 r) = r) = (is_nadd r)) : ((term152 r) = r) = (is_nadd r).
Proof. exact (h1). Qed.
Lemma lem1275459 (r : nat -> nat) (h1 : ((term152 r) = r) = (is_nadd r)) : (is_nadd r) = ((term152 r) = r).
Proof. exact (SYM (@lem1275458 r h1)). Qed.
Lemma lem1275460 (r : nat -> nat) : ((is_nadd r) = ((term152 r) = r)) = (((term152 r) = r) = (is_nadd r)).
Proof. exact (prop_ext (fun h1 : (is_nadd r) = ((term152 r) = r) => @lem1275457 r h1) (fun h1 : ((term152 r) = r) = (is_nadd r) => @lem1275459 r h1)). Qed.
Lemma lem1275462 (x : nat -> nat) : term153 x.
Proof. exact (@lem1262615 x). Qed.
Lemma lem1275463 (x : nat -> nat) : (term153 x) = ((is_nadd x) = (term154 x)).
Proof. exact (eq_refl (term153 x)). Qed.
Lemma lem1275465 (x : nadd) : term155 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1275466 (x : nadd) : (term155 x) = (term156 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1275467 (x : nadd) : term156 x.
Proof. exact (EQ_MP (@lem1275466 x) (@lem1275465 x)). Qed.
Lemma lem1275468 (x : nadd) (y : nadd) : term157 x y.
Proof. exact (@lem1275467 x y). Qed.
Lemma lem1275469 (x : nadd) (y : nadd) : (term157 x y) = ((term158 x y) = (term159 x y)).
Proof. exact (eq_refl (term157 x y)). Qed.
Lemma lem1275471 (x : nadd) : term160 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1275472 (x : nadd) : (term160 x) = (term161 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1275473 (x : nadd) : term161 x.
Proof. exact (EQ_MP (@lem1275472 x) (@lem1275471 x)). Qed.
Lemma lem1275474 (x : nadd) (y : nadd) : term162 x y.
Proof. exact (@lem1275473 x y). Qed.
Lemma lem1275475 (x : nadd) (y : nadd) : (term162 x y) = ((nadd_eq x y) = (term163 x y)).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem1275477 {A B : Type'} (P : type1413 A B) : term164 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1275478 {A B : Type'} (P : type1413 A B) : (term164 A B P) = ((term165 A B P) = (term166 A B P)).
Proof. exact (eq_refl (term164 A B P)). Qed.
Lemma lem1275480 (m : nat) : term167 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1275481 (m : nat) : (term167 m) = (term168 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem1275482 (m : nat) : term168 m.
Proof. exact (EQ_MP (@lem1275481 m) (@lem1275480 m)). Qed.
Lemma lem1275483 (m : nat) (n : nat) : term169 m n.
Proof. exact (@lem1275482 m n). Qed.
Lemma lem1275484 (n : nat) (m : nat) : (term169 m n) = ((Peano.le m n) = (term170 n m)).
Proof. exact (eq_refl (term169 m n)). Qed.
Lemma lem1275486 (x : nadd) : term171 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1275487 (x : nadd) : (term171 x) = (term172 x).
Proof. exact (eq_refl (term171 x)). Qed.
Lemma lem1275488 (x : nadd) : term172 x.
Proof. exact (EQ_MP (@lem1275487 x) (@lem1275486 x)). Qed.
Lemma lem1275489 (x : nadd) (y : nadd) : term173 x y.
Proof. exact (@lem1275488 x y). Qed.
Lemma lem1275490 (x : nadd) (y : nadd) : (term173 x y) = ((nadd_le x y) = (term174 x y)).
Proof. exact (eq_refl (term173 x y)). Qed.
Lemma lem1275495 (x : nadd) (y : nadd) : (nadd_le x y) = (term174 x y).
Proof. exact (EQ_MP (@lem1275490 x y) (@lem1275489 x y)). Qed.
Lemma lem1275504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1275505 (x : nadd) (y : nadd) : (term175 x y) = (term176 x y).
Proof. exact (MK_COMB (@lem1275504) (@lem1275495 x y)). Qed.
Lemma lem1275510 (y : nadd) (x : nadd) : (term177 y x) = (term177 y x).
Proof. exact (eq_refl (term177 y x)). Qed.
Lemma lem1275511 (y : nadd) (x : nadd) : (term178 y x) = (term179 y x).
Proof. exact (MK_COMB (@lem1275505 x y) (@lem1275510 y x)). Qed.
Lemma lem1275514 (y : nadd) (x : nadd) : (term179 y x) = (term178 y x).
Proof. exact (SYM (@lem1275511 y x)). Qed.
Lemma lem1275515 (x : nadd) (y : nadd) (h1 : term174 x y) : term174 x y.
Proof. exact (h1). Qed.
Lemma lem1275516 (x : nadd) (y : nadd) (B : nat) (h1 : term180 x y B) : term180 x y B.
Proof. exact (h1). Qed.
Lemma lem1275524 (n : nat) (m : nat) : (Peano.le m n) = (term170 n m).
Proof. exact (EQ_MP (@lem1275484 n m) (@lem1275483 m n)). Qed.
Lemma lem1275525 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term181 x y n B) = (term182 y B x n).
Proof. exact (@lem1275524 (term183 y n B) (dest_nadd x n)). Qed.
Lemma lem1275532 (y : nadd) (B : nat) (x : nadd) : (term184 x y B) = (term185 y B x).
Proof. exact (fun_ext (fun n : nat => @lem1275525 y B x n)). Qed.
Lemma lem1275533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275534 (y : nadd) (B : nat) (x : nadd) : (term180 x y B) = (term186 y B x).
Proof. exact (MK_COMB (@lem1275533) (@lem1275532 y B x)). Qed.
Lemma lem1275536 {A B : Type'} (P : type1413 A B) : (term165 A B P) = (term166 A B P).
Proof. exact (EQ_MP (@lem1275478 A B P) (@lem1275477 A B P)). Qed.
Lemma lem1275537 (P : type1605) : (term187 P) = (term188 P).
Proof. exact (@lem1275536 nat nat P). Qed.
Lemma lem1275538 (y : nadd) (B : nat) (x : nadd) : (term189 y B x) = (term190 y B x).
Proof. exact (@lem1275537 (term191 y B x)). Qed.
Lemma lem1275539 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term192 y B x n) = (term193 y B x n).
Proof. exact (eq_refl (term192 y B x n)). Qed.
Lemma lem1275540 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1275541 (y : nadd) (B : nat) (x : nadd) (n : nat) (d : nat) : (term194 y B x n d) = (term195 y B x n d).
Proof. exact (MK_COMB (@lem1275539 y B x n) (@lem1275540 d)). Qed.
Lemma lem1275542 (y : nadd) (B : nat) (x : nadd) (n : nat) (d : nat) : (term195 y B x n d) = ((term183 y n B) = (term183 x n d)).
Proof. exact (eq_refl (term195 y B x n d)). Qed.
Lemma lem1275543 (y : nadd) (B : nat) (x : nadd) (n : nat) (d : nat) : (term194 y B x n d) = ((term183 y n B) = (term183 x n d)).
Proof. exact (TRANS (@lem1275541 y B x n d) (@lem1275542 y B x n d)). Qed.
Lemma lem1275544 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term196 y B x n) = (term193 y B x n).
Proof. exact (fun_ext (fun d : nat => @lem1275543 y B x n d)). Qed.
Lemma lem1275545 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1275546 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term197 y B x n) = (term182 y B x n).
Proof. exact (MK_COMB (@lem1275545) (@lem1275544 y B x n)). Qed.
Lemma lem1275547 (y : nadd) (B : nat) (x : nadd) : (term198 y B x) = (term185 y B x).
Proof. exact (fun_ext (fun n : nat => @lem1275546 y B x n)). Qed.
Lemma lem1275548 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275549 (y : nadd) (B : nat) (x : nadd) : (term189 y B x) = (term186 y B x).
Proof. exact (MK_COMB (@lem1275548) (@lem1275547 y B x)). Qed.
Lemma lem1275550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1275551 (y : nadd) (B : nat) (x : nadd) : (term199 y B x) = (term200 y B x).
Proof. exact (MK_COMB (@lem1275550) (@lem1275549 y B x)). Qed.
Lemma lem1275552 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term192 y B x n) = (term193 y B x n).
Proof. exact (eq_refl (term192 y B x n)). Qed.
Lemma lem1275553 (d : nat -> nat) (n : nat) : (d n) = (d n).
Proof. exact (eq_refl (d n)). Qed.
Lemma lem1275554 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (n : nat) : (term201 y B x d n) = (term202 y B x d n).
Proof. exact (MK_COMB (@lem1275552 y B x n) (@lem1275553 d n)). Qed.
Lemma lem1275555 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (n : nat) : (term202 y B x d n) = ((term183 y n B) = (term203 x d n)).
Proof. exact (eq_refl (term202 y B x d n)). Qed.
Lemma lem1275556 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (n : nat) : (term201 y B x d n) = ((term183 y n B) = (term203 x d n)).
Proof. exact (TRANS (@lem1275554 y B x d n) (@lem1275555 y B x d n)). Qed.
Lemma lem1275557 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) : (term204 y B x d) = (term205 y B x d).
Proof. exact (fun_ext (fun n : nat => @lem1275556 y B x d n)). Qed.
Lemma lem1275558 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275559 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) : (term206 y B x d) = (term207 y B x d).
Proof. exact (MK_COMB (@lem1275558) (@lem1275557 y B x d)). Qed.
Lemma lem1275560 (y : nadd) (B : nat) (x : nadd) : (term208 y B x) = (term209 y B x).
Proof. exact (fun_ext (fun d : nat -> nat => @lem1275559 y B x d)). Qed.
Lemma lem1275561 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1275562 (y : nadd) (B : nat) (x : nadd) : (term190 y B x) = (term210 y B x).
Proof. exact (MK_COMB (@lem1275561) (@lem1275560 y B x)). Qed.
Lemma lem1275563 (y : nadd) (B : nat) (x : nadd) : ((term189 y B x) = (term190 y B x)) = ((term186 y B x) = (term210 y B x)).
Proof. exact (MK_COMB (@lem1275551 y B x) (@lem1275562 y B x)). Qed.
Lemma lem1275564 (y : nadd) (B : nat) (x : nadd) : (term186 y B x) = (term210 y B x).
Proof. exact (EQ_MP (@lem1275563 y B x) (@lem1275538 y B x)). Qed.
Lemma lem1275575 (y : nadd) (B : nat) (x : nadd) : (term180 x y B) = (term210 y B x).
Proof. exact (TRANS (@lem1275534 y B x) (@lem1275564 y B x)). Qed.
Lemma lem1275576 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1275577 (y : nadd) (B : nat) (x : nadd) : (term211 x y B) = (term212 y B x).
Proof. exact (MK_COMB (@lem1275576) (@lem1275575 y B x)). Qed.
Lemma lem1275582 (y : nadd) (x : nadd) : (term177 y x) = (term177 y x).
Proof. exact (eq_refl (term177 y x)). Qed.
Lemma lem1275583 (B : nat) (y : nadd) (x : nadd) : (term213 B y x) = (term214 B y x).
Proof. exact (MK_COMB (@lem1275577 y B x) (@lem1275582 y x)). Qed.
Lemma lem1275586 (B : nat) (y : nadd) (x : nadd) : (term214 B y x) = (term213 B y x).
Proof. exact (SYM (@lem1275583 B y x)). Qed.
Lemma lem1275587 (y : nadd) (B : nat) (x : nadd) (h1 : term210 y B x) : term210 y B x.
Proof. exact (h1). Qed.
Lemma lem1275588 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term207 y B x d.
Proof. exact (h1). Qed.
Lemma lem1275590 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (n : nat) (h1 : (term183 y n B) = (term203 x d n)) : (term183 y n B) = (term203 x d n).
Proof. exact (h1). Qed.
Lemma lem1275591 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (n : nat) (h1 : (term183 y n B) = (term203 x d n)) : (term203 x d n) = (term183 y n B).
Proof. exact (SYM (@lem1275590 y B x d n h1)). Qed.
Lemma lem1275592 (x : nadd) (d : nat -> nat) (y : nadd) (n : nat) (B : nat) (h1 : (term203 x d n) = (term183 y n B)) : (term203 x d n) = (term183 y n B).
Proof. exact (h1). Qed.
Lemma lem1275593 (x : nadd) (d : nat -> nat) (y : nadd) (n : nat) (B : nat) (h1 : (term203 x d n) = (term183 y n B)) : (term183 y n B) = (term203 x d n).
Proof. exact (SYM (@lem1275592 x d y n B h1)). Qed.
Lemma lem1275594 (x : nadd) (d : nat -> nat) (y : nadd) (n : nat) (B : nat) : ((term183 y n B) = (term203 x d n)) = ((term203 x d n) = (term183 y n B)).
Proof. exact (prop_ext (fun h1 : (term183 y n B) = (term203 x d n) => @lem1275591 y B x d n h1) (fun h1 : (term203 x d n) = (term183 y n B) => @lem1275593 x d y n B h1)). Qed.
Lemma lem1275595 (x : nadd) (d : nat -> nat) (y : nadd) (B : nat) : (term205 y B x d) = (term215 x d y B).
Proof. exact (fun_ext (fun n : nat => @lem1275594 x d y n B)). Qed.
Lemma lem1275596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275597 (x : nadd) (d : nat -> nat) (y : nadd) (B : nat) : (term207 y B x d) = (term216 x d y B).
Proof. exact (MK_COMB (@lem1275596) (@lem1275595 x d y B)). Qed.
Lemma lem1275598 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term216 x d y B.
Proof. exact (EQ_MP (@lem1275597 x d y B) (@lem1275588 y B x d h1)). Qed.
Lemma lem1275600 (x : nadd) (y : nadd) : (nadd_eq x y) = (term163 x y).
Proof. exact (EQ_MP (@lem1275475 x y) (@lem1275474 x y)). Qed.
Lemma lem1275601 (y : nadd) (x : nadd) (d : nat -> nat) : (term217 y x d) = (term218 y x d).
Proof. exact (@lem1275600 y (term219 x d)). Qed.
Lemma lem1275611 (x : nadd) (y : nadd) : (term158 x y) = (term159 x y).
Proof. exact (EQ_MP (@lem1275469 x y) (@lem1275468 x y)). Qed.
Lemma lem1275612 (x : nadd) (d : nat -> nat) : (term220 x d) = (term221 x d).
Proof. exact (@lem1275611 x (mk_nadd d)). Qed.
Lemma lem1275613 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1275614 (x : nadd) (d : nat -> nat) (n : nat) : (term222 x d n) = (term223 x d n).
Proof. exact (MK_COMB (@lem1275612 x d) (@lem1275613 n)). Qed.
Lemma lem1275616 {A B : Type'} (f : A -> B) (y : A) : (term224 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1275617 (f : nat -> nat) (y : nat) : (term225 f y) = (f y).
Proof. exact (@lem1275616 nat nat f y). Qed.
Lemma lem1275618 (x : nadd) (d : nat -> nat) (n : nat) : (term226 x d n) = (term223 x d n).
Proof. exact (@lem1275617 (term221 x d) n). Qed.
Lemma lem1275619 (x : nadd) (d : nat -> nat) (n : nat) : (term223 x d n) = (term227 x d n).
Proof. exact (eq_refl (term223 x d n)). Qed.
Lemma lem1275620 (x : nadd) (d : nat -> nat) : (term228 x d) = (term221 x d).
Proof. exact (fun_ext (fun n : nat => @lem1275619 x d n)). Qed.
Lemma lem1275621 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1275622 (x : nadd) (d : nat -> nat) (n : nat) : (term226 x d n) = (term223 x d n).
Proof. exact (MK_COMB (@lem1275620 x d) (@lem1275621 n)). Qed.
Lemma lem1275623 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1275624 (x : nadd) (d : nat -> nat) (n : nat) : (term229 x d n) = (term230 x d n).
Proof. exact (MK_COMB (@lem1275623) (@lem1275622 x d n)). Qed.
Lemma lem1275625 (x : nadd) (d : nat -> nat) (n : nat) : (term223 x d n) = (term227 x d n).
Proof. exact (eq_refl (term223 x d n)). Qed.
Lemma lem1275626 (x : nadd) (d : nat -> nat) (n : nat) : ((term226 x d n) = (term223 x d n)) = ((term223 x d n) = (term227 x d n)).
Proof. exact (MK_COMB (@lem1275624 x d n) (@lem1275625 x d n)). Qed.
Lemma lem1275627 (x : nadd) (d : nat -> nat) (n : nat) : (term223 x d n) = (term227 x d n).
Proof. exact (EQ_MP (@lem1275626 x d n) (@lem1275618 x d n)). Qed.
Lemma lem1275628 (x : nadd) (d : nat -> nat) (n : nat) : (term222 x d n) = (term227 x d n).
Proof. exact (TRANS (@lem1275614 x d n) (@lem1275627 x d n)). Qed.
Lemma lem1275629 (y : nadd) (n : nat) : (term231 y n) = (term231 y n).
Proof. exact (eq_refl (term231 y n)). Qed.
Lemma lem1275630 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) : (term232 y x d n) = (term233 y x d n).
Proof. exact (MK_COMB (@lem1275629 y n) (@lem1275628 x d n)). Qed.
Lemma lem1275631 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1275632 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) : (term234 y x d n) = (term235 y x d n).
Proof. exact (MK_COMB (@lem1275631) (@lem1275630 y x d n)). Qed.
Lemma lem1275633 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1275634 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) : (term236 y x d n) = (term237 y x d n).
Proof. exact (MK_COMB (@lem1275633) (@lem1275632 y x d n)). Qed.
Lemma lem1275635 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1275636 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : (term238 y x d n B) = (term239 y x d n B).
Proof. exact (MK_COMB (@lem1275634 y x d n) (@lem1275635 B)). Qed.
Lemma lem1275637 (y : nadd) (x : nadd) (d : nat -> nat) (B : nat) : (term240 y x d B) = (term241 y x d B).
Proof. exact (fun_ext (fun n : nat => @lem1275636 y x d n B)). Qed.
Lemma lem1275638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1275639 (y : nadd) (x : nadd) (d : nat -> nat) (B : nat) : (term242 y x d B) = (term243 y x d B).
Proof. exact (MK_COMB (@lem1275638) (@lem1275637 y x d B)). Qed.
Lemma lem1275644 (y : nadd) (x : nadd) (d : nat -> nat) : (term244 y x d) = (term245 y x d).
Proof. exact (fun_ext (fun B : nat => @lem1275639 y x d B)). Qed.
Lemma lem1275645 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1275646 (y : nadd) (x : nadd) (d : nat -> nat) : (term218 y x d) = (term246 y x d).
Proof. exact (MK_COMB (@lem1275645) (@lem1275644 y x d)). Qed.
Lemma lem1275651 (y : nadd) (x : nadd) (d : nat -> nat) : (term217 y x d) = (term246 y x d).
Proof. exact (TRANS (@lem1275601 y x d) (@lem1275646 y x d)). Qed.
Lemma lem1275652 (y : nadd) (x : nadd) (d : nat -> nat) : (term246 y x d) = (term217 y x d).
Proof. exact (SYM (@lem1275651 y x d)). Qed.
Lemma lem1275653 (d : nat -> nat) (h1 : (term152 d) = d) : (term152 d) = d.
Proof. exact (h1). Qed.
Lemma lem1275654 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term247 y x n B) = (term247 y x n B).
Proof. exact (eq_refl (term247 y x n B)). Qed.
Lemma lem1275655 (y : nadd) (x : nadd) (n : nat) (B : nat) (d : nat -> nat) (h1 : (term152 d) = d) : (term248 y x n B d) = (term249 y x n B d).
Proof. exact (MK_COMB (@lem1275654 y x n B) (@lem1275653 d h1)). Qed.
Lemma lem1275656 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : (term249 y x n B d) = (term250 y x d n B).
Proof. exact (eq_refl (term249 y x n B d)). Qed.
Lemma lem1275657 (y : nadd) (x : nadd) (n : nat) (B : nat) (d : nat -> nat) : (term251 y x n B d) = (term251 y x n B d).
Proof. exact (eq_refl (term251 y x n B d)). Qed.
Lemma lem1275658 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : ((term248 y x n B d) = (term249 y x n B d)) = ((term248 y x n B d) = (term250 y x d n B)).
Proof. exact (MK_COMB (@lem1275657 y x n B d) (@lem1275656 y x d n B)). Qed.
Lemma lem1275659 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : (term248 y x n B d) = (term239 y x d n B).
Proof. exact (eq_refl (term248 y x n B d)). Qed.
Lemma lem1275660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1275661 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : (term251 y x n B d) = (term252 y x d n B).
Proof. exact (MK_COMB (@lem1275660) (@lem1275659 y x d n B)). Qed.
Lemma lem1275662 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : (term250 y x d n B) = (term250 y x d n B).
Proof. exact (eq_refl (term250 y x d n B)). Qed.
Lemma lem1275663 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : ((term248 y x n B d) = (term250 y x d n B)) = ((term239 y x d n B) = (term250 y x d n B)).
Proof. exact (MK_COMB (@lem1275661 y x d n B) (@lem1275662 y x d n B)). Qed.
Lemma lem1275664 (y : nadd) (x : nadd) (d : nat -> nat) (n : nat) (B : nat) : ((term248 y x n B d) = (term249 y x n B d)) = ((term239 y x d n B) = (term250 y x d n B)).
Proof. exact (TRANS (@lem1275658 y x d n B) (@lem1275663 y x d n B)). Qed.
Lemma lem1275665 (y : nadd) (x : nadd) (n : nat) (B : nat) (d : nat -> nat) (h1 : (term152 d) = d) : (term239 y x d n B) = (term250 y x d n B).
Proof. exact (EQ_MP (@lem1275664 y x d n B) (@lem1275655 y x n B d h1)). Qed.
Lemma lem1275666 (y : nadd) (x : nadd) (n : nat) (B : nat) (d : nat -> nat) (h1 : (term152 d) = d) : (term250 y x d n B) = (term239 y x d n B).
Proof. exact (SYM (@lem1275665 y x n B d h1)). Qed.
Lemma lem1275668 (r : nat -> nat) : ((term152 r) = r) = (is_nadd r).
Proof. exact (EQ_MP (@lem1275460 r) (@lem1262760 r)). Qed.
Lemma lem1275669 (d : nat -> nat) : ((term152 d) = d) = (is_nadd d).
Proof. exact (@lem1275668 d). Qed.
Lemma lem1275671 (x : nat -> nat) : (is_nadd x) = (term154 x).
Proof. exact (EQ_MP (@lem1275463 x) (@lem1275462 x)). Qed.
Lemma lem1275672 (d : nat -> nat) : (is_nadd d) = (term154 d).
Proof. exact (@lem1275671 d). Qed.
Lemma lem1275677 (d : nat -> nat) : ((term152 d) = d) = (term154 d).
Proof. exact (TRANS (@lem1275669 d) (@lem1275672 d)). Qed.
Lemma lem1275686 (d : nat -> nat) : (term154 d) = ((term152 d) = d).
Proof. exact (SYM (@lem1275677 d)). Qed.
Lemma lem1275688 (m : nat) (p : nat) (p' : nat) : term141 m p p'.
Proof. exact (EQ_MP (@lem1275446 m p p') (@lem1275445 m p p')). Qed.
Lemma lem1275689 (d : nat -> nat) (B1 : nat) (B2 : nat) (B : nat) (m : nat) (n : nat) : term253 d B1 B2 B m n.
Proof. exact (@lem1275688 (term254 m d n) (term254 n d m) (term255 B1 B2 B m n)). Qed.
Lemma lem1275691 (m : nat) (n : nat) (p : nat) : (term52 m n p) = (term53 m n p).
Proof. exact (EQ_MP (@lem1275362 m n p) (@lem1275361 m n p)). Qed.
Lemma lem1275692 (B1 : nat) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term255 B1 B2 B m n) = (term256 B1 B2 B m n).
Proof. exact (@lem1275691 B1 (Nat.add B2 B) (Nat.add m n)). Qed.
Lemma lem1275693 (d : nat -> nat) (n : nat) (x : nadd) (m : nat) : (term257 d n x m) = (term257 d n x m).
Proof. exact (eq_refl (term257 d n x m)). Qed.
Lemma lem1275694 (d : nat -> nat) (x : nadd) (B1 : nat) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term258 d x B1 B2 B m n) = (term259 d x B1 B2 B m n).
Proof. exact (MK_COMB (@lem1275693 d n x m) (@lem1275692 B1 B2 B m n)). Qed.
Lemma lem1275695 (d : nat -> nat) (x : nadd) (B1 : nat) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term259 d x B1 B2 B m n) = (term258 d x B1 B2 B m n).
Proof. exact (SYM (@lem1275694 d x B1 B2 B m n)). Qed.
Lemma lem1275697 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275353 n m) (@lem1275352 m n)). Qed.
Lemma lem1275698 (B2 : nat) (B : nat) (B1 : nat) (m : nat) (n : nat) : (term256 B1 B2 B m n) = (term260 B2 B B1 m n).
Proof. exact (@lem1275697 (term261 B2 B m n) (term100 B1 m n)). Qed.
Lemma lem1275699 (d : nat -> nat) (n : nat) (x : nadd) (m : nat) : (term257 d n x m) = (term257 d n x m).
Proof. exact (eq_refl (term257 d n x m)). Qed.
Lemma lem1275700 (d : nat -> nat) (x : nadd) (B2 : nat) (B : nat) (B1 : nat) (m : nat) (n : nat) : (term259 d x B1 B2 B m n) = (term262 d x B2 B B1 m n).
Proof. exact (MK_COMB (@lem1275699 d n x m) (@lem1275698 B2 B B1 m n)). Qed.
Lemma lem1275701 (d : nat -> nat) (x : nadd) (B1 : nat) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term262 d x B2 B B1 m n) = (term259 d x B1 B2 B m n).
Proof. exact (SYM (@lem1275700 d x B2 B B1 m n)). Qed.
Lemma lem1275703 (m : nat) (n : nat) (p : nat) (q : nat) : term42 m n p q.
Proof. exact (EQ_MP (@lem1275347 m n p q) (@lem1275346 m n p q)). Qed.
Lemma lem1275704 (d : nat -> nat) (x : nadd) (B2 : nat) (B : nat) (B1 : nat) (m : nat) (n : nat) : term263 d x B2 B B1 m n.
Proof. exact (@lem1275703 (term264 d n x m) (term265 n x m) (term261 B2 B m n) (term100 B1 m n)). Qed.
Lemma lem1275708 (m : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : term266 x B1 m.
Proof. exact (@lem1275455 x B1 h1 m). Qed.
Lemma lem1275709 (x : nadd) (B1 : nat) (m : nat) : (term266 x B1 m) = (term267 x B1 m).
Proof. exact (eq_refl (term266 x B1 m)). Qed.
Lemma lem1275710 (m : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : term267 x B1 m.
Proof. exact (EQ_MP (@lem1275709 x B1 m) (@lem1275708 m x B1 h1)). Qed.
Lemma lem1275711 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : term268 x B1 m n.
Proof. exact (@lem1275710 m x B1 h1 n). Qed.
Lemma lem1275712 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term268 x B1 m n) = (term269 x B1 m n).
Proof. exact (eq_refl (term268 x B1 m n)). Qed.
Lemma lem1275713 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : term269 x B1 m n.
Proof. exact (EQ_MP (@lem1275712 x B1 m n) (@lem1275711 m n x B1 h1)). Qed.
Lemma lem1275714 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term269 x B1 m n) = ((term269 x B1 m n) = True).
Proof. exact (@lem7 (term269 x B1 m n)). Qed.
Lemma lem1275727 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : (term269 x B1 m n) = True.
Proof. exact (EQ_MP (@lem1275714 x B1 m n) (@lem1275713 m n x B1 h1)). Qed.
Lemma lem1275728 (d : nat -> nat) (x : nadd) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term270 d x B2 B m n) = (term270 d x B2 B m n).
Proof. exact (eq_refl (term270 d x B2 B m n)). Qed.
Lemma lem1275729 (d : nat -> nat) (B2 : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : (term271 d B2 B x B1 m n) = (term272 d x B2 B m n).
Proof. exact (MK_COMB (@lem1275728 d x B2 B m n) (@lem1275727 m n x B1 h1)). Qed.
Lemma lem1275731 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1275732 (d : nat -> nat) (x : nadd) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term272 d x B2 B m n) = (term273 d x B2 B m n).
Proof. exact (@lem1275731 (term273 d x B2 B m n)). Qed.
Lemma lem1275733 (d : nat -> nat) (B2 : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : (term271 d B2 B x B1 m n) = (term273 d x B2 B m n).
Proof. exact (TRANS (@lem1275729 d B2 B m n x B1 h1) (@lem1275732 d x B2 B m n)). Qed.
Lemma lem1275734 (d : nat -> nat) (B2 : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term151 x B1) : (term273 d x B2 B m n) = (term271 d B2 B x B1 m n).
Proof. exact (SYM (@lem1275733 d B2 B m n x B1 h1)). Qed.
Lemma lem1275736 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275310 n m) (@lem1275309 m n)). Qed.
Lemma lem1275737 (x : nadd) (m : nat) (d : nat -> nat) (n : nat) : (term274 d m x n) = (term275 x m d n).
Proof. exact (@lem1275736 (term276 m x n) (term254 m d n)). Qed.
Lemma lem1275738 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1275739 (x : nadd) (m : nat) (d : nat -> nat) (n : nat) : (term277 d m x n) = (term278 x m d n).
Proof. exact (MK_COMB (@lem1275738) (@lem1275737 x m d n)). Qed.
Lemma lem1275741 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275310 n m) (@lem1275309 m n)). Qed.
Lemma lem1275742 (x : nadd) (n : nat) (d : nat -> nat) (m : nat) : (term274 d n x m) = (term275 x n d m).
Proof. exact (@lem1275741 (term276 n x m) (term254 n d m)). Qed.
Lemma lem1275743 (x : nadd) (n : nat) (d : nat -> nat) (m : nat) : (term279 d n x m) = (term280 x n d m).
Proof. exact (MK_COMB (@lem1275739 x m d n) (@lem1275742 x n d m)). Qed.
Lemma lem1275744 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1275745 (x : nadd) (n : nat) (d : nat -> nat) (m : nat) : (term264 d n x m) = (term281 x n d m).
Proof. exact (MK_COMB (@lem1275744) (@lem1275743 x n d m)). Qed.
Lemma lem1275746 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1275747 (x : nadd) (n : nat) (d : nat -> nat) (m : nat) : (term282 d n x m) = (term283 x n d m).
Proof. exact (MK_COMB (@lem1275746) (@lem1275745 x n d m)). Qed.
Lemma lem1275749 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275310 n m) (@lem1275309 m n)). Qed.
Lemma lem1275750 (B : nat) (B2 : nat) : (Nat.add B2 B) = (Nat.add B B2).
Proof. exact (@lem1275749 B B2). Qed.
Lemma lem1275751 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1275752 (B : nat) (B2 : nat) : (term284 B2 B) = (term284 B B2).
Proof. exact (MK_COMB (@lem1275751) (@lem1275750 B B2)). Qed.
Lemma lem1275754 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275310 n m) (@lem1275309 m n)). Qed.
Lemma lem1275755 (B : nat) (B2 : nat) (n : nat) (m : nat) : (term261 B2 B m n) = (term261 B B2 n m).
Proof. exact (MK_COMB (@lem1275752 B B2) (@lem1275754 n m)). Qed.
Lemma lem1275756 (x : nadd) (d : nat -> nat) (B : nat) (B2 : nat) (n : nat) (m : nat) : (term273 d x B2 B m n) = (term285 x d B B2 n m).
Proof. exact (MK_COMB (@lem1275747 x n d m) (@lem1275755 B B2 n m)). Qed.
Lemma lem1275757 (d : nat -> nat) (x : nadd) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term285 x d B B2 n m) = (term273 d x B2 B m n).
Proof. exact (SYM (@lem1275756 x d B B2 n m)). Qed.
Lemma lem1275758 (m : nat) : term286 m.
Proof. exact (@lem1275305 m). Qed.
Lemma lem1275759 (m : nat) : (term286 m) = (term107 m).
Proof. exact (eq_refl (term286 m)). Qed.
Lemma lem1275760 (m : nat) : term107 m.
Proof. exact (EQ_MP (@lem1275759 m) (@lem1275758 m)). Qed.
Lemma lem1275761 (m : nat) (n : nat) : term287 m n.
Proof. exact (@lem1275760 m n). Qed.
Lemma lem1275762 (m : nat) (n : nat) : (term287 m n) = (term104 m n).
Proof. exact (eq_refl (term287 m n)). Qed.
Lemma lem1275763 (m : nat) (n : nat) : term104 m n.
Proof. exact (EQ_MP (@lem1275762 m n) (@lem1275761 m n)). Qed.
Lemma lem1275764 (m : nat) (n : nat) (p : nat) : term288 m n p.
Proof. exact (@lem1275763 m n p). Qed.
Lemma lem1275765 (m : nat) (n : nat) (p : nat) : (term288 m n p) = ((term101 n m p) = (term100 m n p)).
Proof. exact (eq_refl (term288 m n p)). Qed.
Lemma lem1275767 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term289 x d y B n.
Proof. exact (@lem1275598 y B x d h1 n). Qed.
Lemma lem1275768 (x : nadd) (d : nat -> nat) (y : nadd) (n : nat) (B : nat) : (term289 x d y B n) = ((term203 x d n) = (term183 y n B)).
Proof. exact (eq_refl (term289 x d y B n)). Qed.
Lemma lem1275787 (m : nat) (n : nat) (p : nat) : (term101 n m p) = (term100 m n p).
Proof. exact (EQ_MP (@lem1275765 m n p) (@lem1275764 m n p)). Qed.
Lemma lem1275788 (m : nat) (x : nadd) (d : nat -> nat) (n : nat) : (term275 x m d n) = (term290 m x d n).
Proof. exact (@lem1275787 m (dest_nadd x n) (d n)). Qed.
Lemma lem1275790 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term203 x d n) = (term183 y n B).
Proof. exact (EQ_MP (@lem1275768 x d y n B) (@lem1275767 n y B x d h1)). Qed.
Lemma lem1275791 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1275792 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term290 m x d n) = (term291 m y n B).
Proof. exact (MK_COMB (@lem1275791 m) (@lem1275790 n y B x d h1)). Qed.
Lemma lem1275793 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term275 x m d n) = (term291 m y n B).
Proof. exact (TRANS (@lem1275788 m x d n) (@lem1275792 m n y B x d h1)). Qed.
Lemma lem1275794 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1275795 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term278 x m d n) = (term292 m y n B).
Proof. exact (MK_COMB (@lem1275794) (@lem1275793 m n y B x d h1)). Qed.
Lemma lem1275797 (m : nat) (n : nat) (p : nat) : (term101 n m p) = (term100 m n p).
Proof. exact (EQ_MP (@lem1275765 m n p) (@lem1275764 m n p)). Qed.
Lemma lem1275798 (n : nat) (x : nadd) (d : nat -> nat) (m : nat) : (term275 x n d m) = (term290 n x d m).
Proof. exact (@lem1275797 n (dest_nadd x m) (d m)). Qed.
Lemma lem1275800 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term203 x d n) = (term183 y n B).
Proof. exact (EQ_MP (@lem1275768 x d y n B) (@lem1275767 n y B x d h1)). Qed.
Lemma lem1275801 (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term203 x d m) = (term183 y m B).
Proof. exact (@lem1275800 m y B x d h1). Qed.
Lemma lem1275802 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1275803 (n : nat) (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term290 n x d m) = (term291 n y m B).
Proof. exact (MK_COMB (@lem1275802 n) (@lem1275801 m y B x d h1)). Qed.
Lemma lem1275804 (n : nat) (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term275 x n d m) = (term291 n y m B).
Proof. exact (TRANS (@lem1275798 n x d m) (@lem1275803 n m y B x d h1)). Qed.
Lemma lem1275805 (n : nat) (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term280 x n d m) = (term293 n y m B).
Proof. exact (MK_COMB (@lem1275795 m n y B x d h1) (@lem1275804 n m y B x d h1)). Qed.
Lemma lem1275806 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1275807 (n : nat) (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term281 x n d m) = (term294 n y m B).
Proof. exact (MK_COMB (@lem1275806) (@lem1275805 n m y B x d h1)). Qed.
Lemma lem1275808 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1275809 (n : nat) (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term283 x n d m) = (term295 n y m B).
Proof. exact (MK_COMB (@lem1275808) (@lem1275807 n m y B x d h1)). Qed.
Lemma lem1275810 (B : nat) (B2 : nat) (n : nat) (m : nat) : (term261 B B2 n m) = (term261 B B2 n m).
Proof. exact (eq_refl (term261 B B2 n m)). Qed.
Lemma lem1275811 (B2 : nat) (n : nat) (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term285 x d B B2 n m) = (term296 y B B2 n m).
Proof. exact (MK_COMB (@lem1275809 n m y B x d h1) (@lem1275810 B B2 n m)). Qed.
Lemma lem1275812 (B2 : nat) (n : nat) (m : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term296 y B B2 n m) = (term285 x d B B2 n m).
Proof. exact (SYM (@lem1275811 B2 n m y B x d h1)). Qed.
Lemma lem1275814 (n : nat) (m : nat) (p : nat) : (term100 m n p) = (term101 n m p).
Proof. exact (EQ_MP (@lem1275286 n m p) (@lem1275285 n m p)). Qed.
Lemma lem1275815 (y : nadd) (n : nat) (m : nat) (B : nat) : (term291 m y n B) = (term297 y n m B).
Proof. exact (@lem1275814 (dest_nadd y n) m B). Qed.
Lemma lem1275816 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1275817 (y : nadd) (n : nat) (m : nat) (B : nat) : (term292 m y n B) = (term298 y n m B).
Proof. exact (MK_COMB (@lem1275816) (@lem1275815 y n m B)). Qed.
Lemma lem1275819 (n : nat) (m : nat) (p : nat) : (term100 m n p) = (term101 n m p).
Proof. exact (EQ_MP (@lem1275286 n m p) (@lem1275285 n m p)). Qed.
Lemma lem1275820 (y : nadd) (m : nat) (n : nat) (B : nat) : (term291 n y m B) = (term297 y m n B).
Proof. exact (@lem1275819 (dest_nadd y m) n B). Qed.
Lemma lem1275821 (y : nadd) (m : nat) (n : nat) (B : nat) : (term293 n y m B) = (term299 y m n B).
Proof. exact (MK_COMB (@lem1275817 y n m B) (@lem1275820 y m n B)). Qed.
Lemma lem1275822 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1275823 (y : nadd) (m : nat) (n : nat) (B : nat) : (term294 n y m B) = (term300 y m n B).
Proof. exact (MK_COMB (@lem1275822) (@lem1275821 y m n B)). Qed.
Lemma lem1275824 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1275825 (y : nadd) (m : nat) (n : nat) (B : nat) : (term295 n y m B) = (term301 y m n B).
Proof. exact (MK_COMB (@lem1275824) (@lem1275823 y m n B)). Qed.
Lemma lem1275826 (B : nat) (B2 : nat) (n : nat) (m : nat) : (term261 B B2 n m) = (term261 B B2 n m).
Proof. exact (eq_refl (term261 B B2 n m)). Qed.
Lemma lem1275827 (y : nadd) (B : nat) (B2 : nat) (n : nat) (m : nat) : (term296 y B B2 n m) = (term302 y B B2 n m).
Proof. exact (MK_COMB (@lem1275825 y m n B) (@lem1275826 B B2 n m)). Qed.
Lemma lem1275828 (y : nadd) (B : nat) (B2 : nat) (n : nat) (m : nat) : (term302 y B B2 n m) = (term296 y B B2 n m).
Proof. exact (SYM (@lem1275827 y B B2 n m)). Qed.
Lemma lem1275830 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term90 m n p q p'.
Proof. exact (EQ_MP (@lem1275277 m n p q p') (@lem1275276 m n p q p')). Qed.
Lemma lem1275831 (y : nadd) (B : nat) (B2 : nat) (n : nat) (m : nat) : term303 y B B2 n m.
Proof. exact (@lem1275830 (term276 m y n) (Nat.mul m B) (term276 n y m) (Nat.mul n B) (term261 B B2 n m)). Qed.
Lemma lem1275833 (m : nat) (n : nat) (p : nat) : (term52 m n p) = (term53 m n p).
Proof. exact (EQ_MP (@lem1275189 m n p) (@lem1275188 m n p)). Qed.
Lemma lem1275834 (B : nat) (B2 : nat) (n : nat) (m : nat) : (term261 B B2 n m) = (term304 B B2 n m).
Proof. exact (@lem1275833 B B2 (Nat.add n m)). Qed.
Lemma lem1275835 (y : nadd) (m : nat) (n : nat) (B : nat) : (term305 y m n B) = (term305 y m n B).
Proof. exact (eq_refl (term305 y m n B)). Qed.
Lemma lem1275836 (y : nadd) (B : nat) (B2 : nat) (n : nat) (m : nat) : (term306 y B B2 n m) = (term307 y B B2 n m).
Proof. exact (MK_COMB (@lem1275835 y m n B) (@lem1275834 B B2 n m)). Qed.
Lemma lem1275837 (y : nadd) (B : nat) (B2 : nat) (n : nat) (m : nat) : (term307 y B B2 n m) = (term306 y B B2 n m).
Proof. exact (SYM (@lem1275836 y B B2 n m)). Qed.
Lemma lem1275839 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275180 n m) (@lem1275179 m n)). Qed.
Lemma lem1275840 (B2 : nat) (B : nat) (n : nat) (m : nat) : (term304 B B2 n m) = (term304 B2 B n m).
Proof. exact (@lem1275839 (term100 B2 n m) (term100 B n m)). Qed.
Lemma lem1275841 (y : nadd) (m : nat) (n : nat) (B : nat) : (term305 y m n B) = (term305 y m n B).
Proof. exact (eq_refl (term305 y m n B)). Qed.
Lemma lem1275842 (y : nadd) (B2 : nat) (B : nat) (n : nat) (m : nat) : (term307 y B B2 n m) = (term308 y B2 B n m).
Proof. exact (MK_COMB (@lem1275841 y m n B) (@lem1275840 B2 B n m)). Qed.
Lemma lem1275843 (y : nadd) (B : nat) (B2 : nat) (n : nat) (m : nat) : (term308 y B2 B n m) = (term307 y B B2 n m).
Proof. exact (SYM (@lem1275842 y B2 B n m)). Qed.
Lemma lem1275845 (m : nat) (n : nat) (p : nat) (q : nat) : term42 m n p q.
Proof. exact (EQ_MP (@lem1275174 m n p q) (@lem1275173 m n p q)). Qed.
Lemma lem1275846 (y : nadd) (B2 : nat) (B : nat) (n : nat) (m : nat) : term309 y B2 B n m.
Proof. exact (@lem1275845 (term265 n y m) (term310 m n B) (term100 B2 n m) (term100 B n m)). Qed.
Lemma lem1275850 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275137 n m) (@lem1275136 m n)). Qed.
Lemma lem1275851 (m : nat) (n : nat) : (Nat.add n m) = (Nat.add m n).
Proof. exact (@lem1275850 m n). Qed.
Lemma lem1275852 (B2 : nat) : (Nat.mul B2) = (Nat.mul B2).
Proof. exact (eq_refl (Nat.mul B2)). Qed.
Lemma lem1275853 (B2 : nat) (m : nat) (n : nat) : (term100 B2 n m) = (term100 B2 m n).
Proof. exact (MK_COMB (@lem1275852 B2) (@lem1275851 m n)). Qed.
Lemma lem1275854 (n : nat) (y : nadd) (m : nat) : (term311 n y m) = (term311 n y m).
Proof. exact (eq_refl (term311 n y m)). Qed.
Lemma lem1275855 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term312 y B2 n m) = (term269 y B2 m n).
Proof. exact (MK_COMB (@lem1275854 n y m) (@lem1275853 B2 m n)). Qed.
Lemma lem1275856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1275857 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term313 y B2 n m) = (term314 y B2 m n).
Proof. exact (MK_COMB (@lem1275856) (@lem1275855 y B2 m n)). Qed.
Lemma lem1275859 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1275137 n m) (@lem1275136 m n)). Qed.
Lemma lem1275860 (m : nat) (n : nat) : (Nat.add n m) = (Nat.add m n).
Proof. exact (@lem1275859 m n). Qed.
Lemma lem1275861 (B : nat) : (Nat.mul B) = (Nat.mul B).
Proof. exact (eq_refl (Nat.mul B)). Qed.
Lemma lem1275862 (B : nat) (m : nat) (n : nat) : (term100 B n m) = (term100 B m n).
Proof. exact (MK_COMB (@lem1275861 B) (@lem1275860 m n)). Qed.
Lemma lem1275863 (m : nat) (n : nat) (B : nat) : (term315 m n B) = (term315 m n B).
Proof. exact (eq_refl (term315 m n B)). Qed.
Lemma lem1275864 (B : nat) (m : nat) (n : nat) : (term316 B n m) = (term317 B m n).
Proof. exact (MK_COMB (@lem1275863 m n B) (@lem1275862 B m n)). Qed.
Lemma lem1275865 (y : nadd) (B2 : nat) (B : nat) (m : nat) (n : nat) : (term318 y B2 B n m) = (term319 y B2 B m n).
Proof. exact (MK_COMB (@lem1275857 y B2 m n) (@lem1275864 B m n)). Qed.
Lemma lem1275866 (y : nadd) (B2 : nat) (B : nat) (n : nat) (m : nat) : (term319 y B2 B m n) = (term318 y B2 B n m).
Proof. exact (SYM (@lem1275865 y B2 B m n)). Qed.
Lemma lem1275878 (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term266 y B2 m.
Proof. exact (@lem1275451 y B2 h1 m). Qed.
Lemma lem1275879 (y : nadd) (B2 : nat) (m : nat) : (term266 y B2 m) = (term267 y B2 m).
Proof. exact (eq_refl (term266 y B2 m)). Qed.
Lemma lem1275880 (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term267 y B2 m.
Proof. exact (EQ_MP (@lem1275879 y B2 m) (@lem1275878 m y B2 h1)). Qed.
Lemma lem1275881 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term268 y B2 m n.
Proof. exact (@lem1275880 m y B2 h1 n). Qed.
Lemma lem1275882 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term268 y B2 m n) = (term269 y B2 m n).
Proof. exact (eq_refl (term268 y B2 m n)). Qed.
Lemma lem1275883 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term269 y B2 m n.
Proof. exact (EQ_MP (@lem1275882 y B2 m n) (@lem1275881 m n y B2 h1)). Qed.
Lemma lem1275884 (y : nadd) (B2 : nat) (m : nat) (n : nat) : (term269 y B2 m n) = ((term269 y B2 m n) = True).
Proof. exact (@lem7 (term269 y B2 m n)). Qed.
Lemma lem1275889 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : (term269 y B2 m n) = True.
Proof. exact (EQ_MP (@lem1275884 y B2 m n) (@lem1275883 m n y B2 h1)). Qed.
Lemma lem1275890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1275891 (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : (term314 y B2 m n) = (and True).
Proof. exact (MK_COMB (@lem1275890) (@lem1275889 m n y B2 h1)). Qed.
Lemma lem1275892 (B : nat) (m : nat) (n : nat) : (term317 B m n) = (term317 B m n).
Proof. exact (eq_refl (term317 B m n)). Qed.
Lemma lem1275893 (B : nat) (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : (term319 y B2 B m n) = (term320 B m n).
Proof. exact (MK_COMB (@lem1275891 m n y B2 h1) (@lem1275892 B m n)). Qed.
Lemma lem1275895 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1275896 (B : nat) (m : nat) (n : nat) : (term320 B m n) = (term317 B m n).
Proof. exact (@lem1275895 (term317 B m n)). Qed.
Lemma lem1275897 (B : nat) (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : (term319 y B2 B m n) = (term317 B m n).
Proof. exact (TRANS (@lem1275893 B m n y B2 h1) (@lem1275896 B m n)). Qed.
Lemma lem1275898 (B : nat) (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : (term317 B m n) = (term319 y B2 B m n).
Proof. exact (SYM (@lem1275897 B m n y B2 h1)). Qed.
Lemma lem1275900 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1275131 n m) (@lem1275130 m n)). Qed.
Lemma lem1275901 (B : nat) (m : nat) : (Nat.mul m B) = (Nat.mul B m).
Proof. exact (@lem1275900 B m). Qed.
Lemma lem1275902 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1275903 (B : nat) (m : nat) : (term321 m B) = (term321 B m).
Proof. exact (MK_COMB (@lem1275902) (@lem1275901 B m)). Qed.
Lemma lem1275905 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1275131 n m) (@lem1275130 m n)). Qed.
Lemma lem1275906 (B : nat) (n : nat) : (Nat.mul n B) = (Nat.mul B n).
Proof. exact (@lem1275905 B n). Qed.
Lemma lem1275907 (m : nat) (B : nat) (n : nat) : (term322 m n B) = (term323 m B n).
Proof. exact (MK_COMB (@lem1275903 B m) (@lem1275906 B n)). Qed.
Lemma lem1275908 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1275909 (m : nat) (B : nat) (n : nat) : (term310 m n B) = (term1 m B n).
Proof. exact (MK_COMB (@lem1275908) (@lem1275907 m B n)). Qed.
Lemma lem1275910 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1275911 (m : nat) (B : nat) (n : nat) : (term315 m n B) = (term324 m B n).
Proof. exact (MK_COMB (@lem1275910) (@lem1275909 m B n)). Qed.
Lemma lem1275912 (B : nat) (m : nat) (n : nat) : (term100 B m n) = (term100 B m n).
Proof. exact (eq_refl (term100 B m n)). Qed.
Lemma lem1275913 (B : nat) (m : nat) (n : nat) : (term317 B m n) = (term325 B m n).
Proof. exact (MK_COMB (@lem1275911 m B n) (@lem1275912 B m n)). Qed.
Lemma lem1275914 (B : nat) (m : nat) (n : nat) : (term325 B m n) = (term317 B m n).
Proof. exact (SYM (@lem1275913 B m n)). Qed.
Lemma lem1275916 (m : nat) (n : nat) (p : nat) : (term1 n m p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1275125 m n p) (@lem1275124 m n p)). Qed.
Lemma lem1275917 (B : nat) (m : nat) (n : nat) : (term1 m B n) = (term0 B m n).
Proof. exact (@lem1275916 B m n). Qed.
Lemma lem1275918 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1275919 (B : nat) (m : nat) (n : nat) : (term324 m B n) = (term326 B m n).
Proof. exact (MK_COMB (@lem1275918) (@lem1275917 B m n)). Qed.
Lemma lem1275920 (B : nat) (m : nat) (n : nat) : (term100 B m n) = (term100 B m n).
Proof. exact (eq_refl (term100 B m n)). Qed.
Lemma lem1275921 (B : nat) (m : nat) (n : nat) : (term325 B m n) = (term327 B m n).
Proof. exact (MK_COMB (@lem1275919 B m n) (@lem1275920 B m n)). Qed.
Lemma lem1275923 (m : nat) (n : nat) (p : nat) : (term19 n m p) = (term20 m n p).
Proof. exact (EQ_MP (@lem1275108 m n p) (@lem1275107 m n p)). Qed.
Lemma lem1275924 (B : nat) (m : nat) (n : nat) : (term327 B m n) = (term328 B m n).
Proof. exact (@lem1275923 B (term122 m n) (Nat.add m n)). Qed.
Lemma lem1275930 (m : nat) (n : nat) : (term24 m n) = True.
Proof. exact (EQ_MP (@lem1275116 m n) (@lem1275115 m n)). Qed.
Lemma lem1275931 (B : nat) : (term329 B) = (term329 B).
Proof. exact (eq_refl (term329 B)). Qed.
Lemma lem1275932 (m : nat) (n : nat) (B : nat) : (term328 B m n) = (term330 B).
Proof. exact (MK_COMB (@lem1275931 B) (@lem1275930 m n)). Qed.
Lemma lem1275934 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1275935 (B : nat) : (term330 B) = True.
Proof. exact (@lem1275934 (B = (NUMERAL 0))). Qed.
Lemma lem1275936 (B : nat) (m : nat) (n : nat) : (term328 B m n) = True.
Proof. exact (TRANS (@lem1275932 m n B) (@lem1275935 B)). Qed.
Lemma lem1275937 (B : nat) (m : nat) (n : nat) : (term327 B m n) = True.
Proof. exact (TRANS (@lem1275924 B m n) (@lem1275936 B m n)). Qed.
Lemma lem1275938 (B : nat) (m : nat) (n : nat) : (term325 B m n) = True.
Proof. exact (TRANS (@lem1275921 B m n) (@lem1275937 B m n)). Qed.
Lemma lem1275939 (B : nat) (m : nat) (n : nat) : True = (term325 B m n).
Proof. exact (SYM (@lem1275938 B m n)). Qed.
Lemma lem1275940 (B : nat) (m : nat) (n : nat) : term325 B m n.
Proof. exact (EQ_MP (@lem1275939 B m n) (@lem0)). Qed.
Lemma lem1275941 (B : nat) (m : nat) (n : nat) : term317 B m n.
Proof. exact (EQ_MP (@lem1275914 B m n) (@lem1275940 B m n)). Qed.
Lemma lem1275942 (B : nat) (m : nat) (n : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term319 y B2 B m n.
Proof. exact (EQ_MP (@lem1275898 B m n y B2 h1) (@lem1275941 B m n)). Qed.
Lemma lem1275943 (B : nat) (n : nat) (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term318 y B2 B n m.
Proof. exact (EQ_MP (@lem1275866 y B2 B n m) (@lem1275942 B m n y B2 h1)). Qed.
Lemma lem1275944 (B : nat) (n : nat) (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term308 y B2 B n m.
Proof. exact (@lem1275846 y B2 B n m (@lem1275943 B n m y B2 h1)). Qed.
Lemma lem1275945 (B : nat) (n : nat) (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term307 y B B2 n m.
Proof. exact (EQ_MP (@lem1275843 y B B2 n m) (@lem1275944 B n m y B2 h1)). Qed.
Lemma lem1275946 (B : nat) (n : nat) (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term306 y B B2 n m.
Proof. exact (EQ_MP (@lem1275837 y B B2 n m) (@lem1275945 B n m y B2 h1)). Qed.
Lemma lem1275947 (B : nat) (n : nat) (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term302 y B B2 n m.
Proof. exact (@lem1275831 y B B2 n m (@lem1275946 B n m y B2 h1)). Qed.
Lemma lem1275948 (B : nat) (n : nat) (m : nat) (y : nadd) (B2 : nat) (h1 : term151 y B2) : term296 y B B2 n m.
Proof. exact (EQ_MP (@lem1275828 y B B2 n m) (@lem1275947 B n m y B2 h1)). Qed.
Lemma lem1275949 (n : nat) (m : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 y B2) (h2 : term207 y B x d) : term285 x d B B2 n m.
Proof. exact (EQ_MP (@lem1275812 B2 n m y B x d h2) (@lem1275948 B n m y B2 h1)). Qed.
Lemma lem1275950 (m : nat) (n : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 y B2) (h2 : term207 y B x d) : term273 d x B2 B m n.
Proof. exact (EQ_MP (@lem1275757 d x B2 B m n) (@lem1275949 n m B2 y B x d h1 h2)). Qed.
Lemma lem1275951 (m : nat) (n : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term271 d B2 B x B1 m n.
Proof. exact (EQ_MP (@lem1275734 d B2 B m n x B1 h1) (@lem1275950 m n B2 y B x d h2 h3)). Qed.
Lemma lem1275952 (m : nat) (n : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term262 d x B2 B B1 m n.
Proof. exact (@lem1275704 d x B2 B B1 m n (@lem1275951 m n B1 B2 y B x d h1 h2 h3)). Qed.
Lemma lem1275953 (m : nat) (n : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term259 d x B1 B2 B m n.
Proof. exact (EQ_MP (@lem1275701 d x B1 B2 B m n) (@lem1275952 m n B1 B2 y B x d h1 h2 h3)). Qed.
Lemma lem1275954 (m : nat) (n : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term258 d x B1 B2 B m n.
Proof. exact (EQ_MP (@lem1275695 d x B1 B2 B m n) (@lem1275953 m n B1 B2 y B x d h1 h2 h3)). Qed.
Lemma lem1275955 (m : nat) (n : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term331 d x B1 B2 B m n.
Proof. exact (ex_intro (term332 d x B1 B2 B m n) (term276 n x m) (@lem1275954 m n B1 B2 y B x d h1 h2 h3)). Qed.
Lemma lem1275956 (m : nat) (n : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term333 d B1 B2 B m n.
Proof. exact (ex_intro (term334 d B1 B2 B m n) (term276 m x n) (@lem1275955 m n B1 B2 y B x d h1 h2 h3)). Qed.
Lemma lem1275957 (m : nat) (n : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term335 d B1 B2 B m n.
Proof. exact (@lem1275689 d B1 B2 B m n (@lem1275956 m n B1 B2 y B x d h1 h2 h3)). Qed.
Lemma lem1275962 (m : nat) (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term336 d B1 B2 B m.
Proof. exact (fun n : nat => @lem1275957 m n B1 B2 y B x d h1 h2 h3). Qed.
Lemma lem1275967 (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term337 d B1 B2 B.
Proof. exact (fun m : nat => @lem1275962 m B1 B2 y B x d h1 h2 h3). Qed.
Lemma lem1275968 (B1 : nat) (B2 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term151 y B2) (h3 : term207 y B x d) : term154 d.
Proof. exact (ex_intro (term338 d) (term339 B1 B2 B) (@lem1275967 B1 B2 y B x d h1 h2 h3)). Qed.
Lemma lem1275969 (B1 : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term151 x B1) (h2 : term207 y B x d) : term154 d.
Proof. exact (ex_elim (@lem1275450 y) (fun B2 : nat => fun h0 : term340 y B2 => @lem1275968 B1 B2 y B x d h1 h0 h2)). Qed.
Lemma lem1275970 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term154 d.
Proof. exact (ex_elim (@lem1275454 x) (fun B1 : nat => fun h0 : term340 x B1 => @lem1275969 B1 y B x d h0 h1)). Qed.
Lemma lem1275971 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term152 d) = d.
Proof. exact (EQ_MP (@lem1275686 d) (@lem1275970 y B x d h1)). Qed.
Lemma lem1275972 (n : nat) : term341 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem1275973 (n : nat) : (term341 n) = (Peano.le n n).
Proof. exact (eq_refl (term341 n)). Qed.
Lemma lem1275974 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem1275973 n) (@lem1275972 n)). Qed.
Lemma lem1275975 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem1275977 (m : nat) : term342 m.
Proof. exact (@lem1245295 m). Qed.
Lemma lem1275978 (m : nat) : (term342 m) = (term343 m).
Proof. exact (eq_refl (term342 m)). Qed.
Lemma lem1275979 (m : nat) : term343 m.
Proof. exact (EQ_MP (@lem1275978 m) (@lem1275977 m)). Qed.
Lemma lem1275980 (m : nat) (n : nat) : term344 m n.
Proof. exact (@lem1275979 m n). Qed.
Lemma lem1275981 (m : nat) (n : nat) : (term344 m n) = ((term345 m n) = n).
Proof. exact (eq_refl (term344 m n)). Qed.
Lemma lem1275983 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term289 x d y B n.
Proof. exact (@lem1275598 y B x d h1 n). Qed.
Lemma lem1275984 (x : nadd) (d : nat -> nat) (y : nadd) (n : nat) (B : nat) : (term289 x d y B n) = ((term203 x d n) = (term183 y n B)).
Proof. exact (eq_refl (term289 x d y B n)). Qed.
Lemma lem1275991 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term203 x d n) = (term183 y n B).
Proof. exact (EQ_MP (@lem1275984 x d y n B) (@lem1275983 n y B x d h1)). Qed.
Lemma lem1275992 (y : nadd) (n : nat) : (term231 y n) = (term231 y n).
Proof. exact (eq_refl (term231 y n)). Qed.
Lemma lem1275993 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term346 y x d n) = (term347 y n B).
Proof. exact (MK_COMB (@lem1275992 y n) (@lem1275991 n y B x d h1)). Qed.
Lemma lem1275994 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1275995 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term348 y x d n) = (term349 y n B).
Proof. exact (MK_COMB (@lem1275994) (@lem1275993 n y B x d h1)). Qed.
Lemma lem1275997 (m : nat) (n : nat) : (term345 m n) = n.
Proof. exact (EQ_MP (@lem1275981 m n) (@lem1275980 m n)). Qed.
Lemma lem1275998 (y : nadd) (n : nat) (B : nat) : (term349 y n B) = B.
Proof. exact (@lem1275997 (dest_nadd y n) B). Qed.
Lemma lem1275999 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term348 y x d n) = B.
Proof. exact (TRANS (@lem1275995 n y B x d h1) (@lem1275998 y n B)). Qed.
Lemma lem1276000 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1276001 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term350 y x d n) = (Peano.le B).
Proof. exact (MK_COMB (@lem1276000) (@lem1275999 n y B x d h1)). Qed.
Lemma lem1276002 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1276003 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term250 y x d n B) = (Peano.le B B).
Proof. exact (MK_COMB (@lem1276001 n y B x d h1) (@lem1276002 B)). Qed.
Lemma lem1276005 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem1275975 n) (@lem1275974 n)). Qed.
Lemma lem1276006 (B : nat) : (Peano.le B B) = True.
Proof. exact (@lem1276005 B). Qed.
Lemma lem1276007 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : (term250 y x d n B) = True.
Proof. exact (TRANS (@lem1276003 n y B x d h1) (@lem1276006 B)). Qed.
Lemma lem1276008 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : True = (term250 y x d n B).
Proof. exact (SYM (@lem1276007 n y B x d h1)). Qed.
Lemma lem1276009 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term250 y x d n B.
Proof. exact (EQ_MP (@lem1276008 n y B x d h1) (@lem0)). Qed.
Lemma lem1276010 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) (h2 : (term152 d) = d) : term239 y x d n B.
Proof. exact (EQ_MP (@lem1275666 y x n B d h2) (@lem1276009 n y B x d h1)). Qed.
Lemma lem1276011 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : ((term152 d) = d) = (term239 y x d n B).
Proof. exact (prop_ext (fun h2 : (term152 d) = d => @lem1276010 n y B x d h1 h2) (fun h2 : term239 y x d n B => @lem1275971 y B x d h1)). Qed.
Lemma lem1276012 (n : nat) (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term239 y x d n B.
Proof. exact (EQ_MP (@lem1276011 n y B x d h1) (@lem1275971 y B x d h1)). Qed.
Lemma lem1276017 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term243 y x d B.
Proof. exact (fun n : nat => @lem1276012 n y B x d h1). Qed.
Lemma lem1276018 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term246 y x d.
Proof. exact (ex_intro (term245 y x d) B (@lem1276017 y B x d h1)). Qed.
Lemma lem1276019 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term217 y x d.
Proof. exact (EQ_MP (@lem1275652 y x d) (@lem1276018 y B x d h1)). Qed.
Lemma lem1276020 (y : nadd) (B : nat) (x : nadd) (d : nat -> nat) (h1 : term207 y B x d) : term177 y x.
Proof. exact (ex_intro (term351 y x) (mk_nadd d) (@lem1276019 y B x d h1)). Qed.
Lemma lem1276021 (y : nadd) (B : nat) (x : nadd) (h1 : term210 y B x) : term177 y x.
Proof. exact (ex_elim (@lem1275587 y B x h1) (fun d : nat -> nat => fun h0 : term209 y B x d => @lem1276020 y B x d h0)). Qed.
Lemma lem1276022 (B : nat) (y : nadd) (x : nadd) : term214 B y x.
Proof. exact (fun h0 : term210 y B x => @lem1276021 y B x h0). Qed.
Lemma lem1276023 (B : nat) (y : nadd) (x : nadd) : term213 B y x.
Proof. exact (EQ_MP (@lem1275586 B y x) (@lem1276022 B y x)). Qed.
Lemma lem1276024 (x : nadd) (y : nadd) (B : nat) (h1 : term180 x y B) : term177 y x.
Proof. exact (@lem1276023 B y x (@lem1275516 x y B h1)). Qed.
Lemma lem1276025 (x : nadd) (y : nadd) (h1 : term174 x y) : term177 y x.
Proof. exact (ex_elim (@lem1275515 x y h1) (fun B : nat => fun h0 : term352 x y B => @lem1276024 x y B h0)). Qed.
Lemma lem1276026 (y : nadd) (x : nadd) : term179 y x.
Proof. exact (fun h0 : term174 x y => @lem1276025 x y h0). Qed.
Lemma lem1276027 (y : nadd) (x : nadd) : term178 y x.
Proof. exact (EQ_MP (@lem1275514 y x) (@lem1276026 y x)). Qed.
Lemma lem1276032 (x : nadd) : term353 x.
Proof. exact (fun y : nadd => @lem1276027 y x). Qed.
Lemma lem1276037 : term354.
Proof. exact (fun x : nadd => @lem1276032 x). Qed.
