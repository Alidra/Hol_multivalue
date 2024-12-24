Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ALTMUL_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NADD_BOUND_spec.
Require Import NADD_CAUCHY_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1267119 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1267120 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1267119 m n p h1)). Qed.
Lemma lem1267121 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1267122 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1267121 m n p h1)). Qed.
Lemma lem1267123 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1267120 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1267122 m n p h1)). Qed.
Lemma lem1267124 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1267123 m n p)). Qed.
Lemma lem1267125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267126 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1267125) (@lem1267124 m n)). Qed.
Lemma lem1267127 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1267126 m n)). Qed.
Lemma lem1267128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267129 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1267128) (@lem1267127 m)). Qed.
Lemma lem1267130 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1267129 m)). Qed.
Lemma lem1267131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267132 : term12 = term13.
Proof. exact (MK_COMB (@lem1267131) (@lem1267130)). Qed.
Lemma lem1267133 : term13.
Proof. exact (EQ_MP (@lem1267132) (@lem82357)). Qed.
Lemma lem1267137 (n : nat) (m : nat) (p : nat) (h1 : (term14 m n p) = (term15 n m p)) : (term14 m n p) = (term15 n m p).
Proof. exact (h1). Qed.
Lemma lem1267138 (n : nat) (m : nat) (p : nat) (h1 : (term14 m n p) = (term15 n m p)) : (term15 n m p) = (term14 m n p).
Proof. exact (SYM (@lem1267137 n m p h1)). Qed.
Lemma lem1267139 (m : nat) (n : nat) (p : nat) (h1 : (term15 n m p) = (term14 m n p)) : (term15 n m p) = (term14 m n p).
Proof. exact (h1). Qed.
Lemma lem1267140 (m : nat) (n : nat) (p : nat) (h1 : (term15 n m p) = (term14 m n p)) : (term14 m n p) = (term15 n m p).
Proof. exact (SYM (@lem1267139 m n p h1)). Qed.
Lemma lem1267141 (m : nat) (n : nat) (p : nat) : ((term14 m n p) = (term15 n m p)) = ((term15 n m p) = (term14 m n p)).
Proof. exact (prop_ext (fun h1 : (term14 m n p) = (term15 n m p) => @lem1267138 n m p h1) (fun h1 : (term15 n m p) = (term14 m n p) => @lem1267140 m n p h1)). Qed.
Lemma lem1267142 (m : nat) (n : nat) : (term16 n m) = (term17 m n).
Proof. exact (fun_ext (fun p : nat => @lem1267141 m n p)). Qed.
Lemma lem1267143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267144 (m : nat) (n : nat) : (term18 n m) = (term19 m n).
Proof. exact (MK_COMB (@lem1267143) (@lem1267142 m n)). Qed.
Lemma lem1267145 (m : nat) : (term20 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem1267144 m n)). Qed.
Lemma lem1267146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267147 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem1267146) (@lem1267145 m)). Qed.
Lemma lem1267148 : term24 = term25.
Proof. exact (fun_ext (fun m : nat => @lem1267147 m)). Qed.
Lemma lem1267149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267150 : term26 = term27.
Proof. exact (MK_COMB (@lem1267149) (@lem1267148)). Qed.
Lemma lem1267151 : term27.
Proof. exact (EQ_MP (@lem1267150) (@lem82055)). Qed.
Lemma lem1267155 (m : nat) (n : nat) (p : nat) (h1 : (term28 m n p) = (term29 m n p)) : (term28 m n p) = (term29 m n p).
Proof. exact (h1). Qed.
Lemma lem1267156 (m : nat) (n : nat) (p : nat) (h1 : (term28 m n p) = (term29 m n p)) : (term29 m n p) = (term28 m n p).
Proof. exact (SYM (@lem1267155 m n p h1)). Qed.
Lemma lem1267157 (m : nat) (n : nat) (p : nat) (h1 : (term29 m n p) = (term28 m n p)) : (term29 m n p) = (term28 m n p).
Proof. exact (h1). Qed.
Lemma lem1267158 (m : nat) (n : nat) (p : nat) (h1 : (term29 m n p) = (term28 m n p)) : (term28 m n p) = (term29 m n p).
Proof. exact (SYM (@lem1267157 m n p h1)). Qed.
Lemma lem1267159 (m : nat) (n : nat) (p : nat) : ((term28 m n p) = (term29 m n p)) = ((term29 m n p) = (term28 m n p)).
Proof. exact (prop_ext (fun h1 : (term28 m n p) = (term29 m n p) => @lem1267156 m n p h1) (fun h1 : (term29 m n p) = (term28 m n p) => @lem1267158 m n p h1)). Qed.
Lemma lem1267160 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (fun_ext (fun p : nat => @lem1267159 m n p)). Qed.
Lemma lem1267161 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267162 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem1267161) (@lem1267160 m n)). Qed.
Lemma lem1267163 (m : nat) : (term34 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem1267162 m n)). Qed.
Lemma lem1267164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267165 (m : nat) : (term36 m) = (term37 m).
Proof. exact (MK_COMB (@lem1267164) (@lem1267163 m)). Qed.
Lemma lem1267166 : term38 = term39.
Proof. exact (fun_ext (fun m : nat => @lem1267165 m)). Qed.
Lemma lem1267167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267168 : term40 = term41.
Proof. exact (MK_COMB (@lem1267167) (@lem1267166)). Qed.
Lemma lem1267169 : term41.
Proof. exact (EQ_MP (@lem1267168) (@lem77960)). Qed.
Lemma lem1267170 (m : nat) : term42 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1267171 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem1267172 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem1267171 m) (@lem1267170 m)). Qed.
Lemma lem1267173 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem1267172 m n). Qed.
Lemma lem1267174 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem1267175 (m : nat) (n : nat) : term45 m n.
Proof. exact (EQ_MP (@lem1267174 m n) (@lem1267173 m n)). Qed.
Lemma lem1267176 (m : nat) (n : nat) (p : nat) : term46 m n p.
Proof. exact (@lem1267175 m n p). Qed.
Lemma lem1267177 (m : nat) (n : nat) (p : nat) : (term46 m n p) = ((term47 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term46 m n p)). Qed.
Lemma lem1267179 (m : nat) : term48 m.
Proof. exact (@lem1267169 m). Qed.
Lemma lem1267180 (m : nat) : (term48 m) = (term37 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem1267181 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1267180 m) (@lem1267179 m)). Qed.
Lemma lem1267182 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1267181 m n). Qed.
Lemma lem1267183 (m : nat) (n : nat) : (term49 m n) = (term33 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1267184 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem1267183 m n) (@lem1267182 m n)). Qed.
Lemma lem1267185 (m : nat) (n : nat) (p : nat) : term50 m n p.
Proof. exact (@lem1267184 m n p). Qed.
Lemma lem1267186 (m : nat) (n : nat) (p : nat) : (term50 m n p) = ((term29 m n p) = (term28 m n p)).
Proof. exact (eq_refl (term50 m n p)). Qed.
Lemma lem1267188 : term51.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1267189 : term52.
Proof. exact (proj2 (@lem1267188)). Qed.
Lemma lem1267190 : term53.
Proof. exact (proj2 (@lem1267189)). Qed.
Lemma lem1267206 : term54.
Proof. exact (proj1 (@lem1267190)). Qed.
Lemma lem1267207 (m : nat) : term55 m.
Proof. exact (@lem1267206 m). Qed.
Lemma lem1267208 (m : nat) : (term55 m) = ((term56 m) = m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem1267222 (m : nat) : term57 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1267223 (m : nat) : (term57 m) = (term58 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem1267224 (m : nat) : term58 m.
Proof. exact (EQ_MP (@lem1267223 m) (@lem1267222 m)). Qed.
Lemma lem1267225 (m : nat) (n : nat) : term59 m n.
Proof. exact (@lem1267224 m n). Qed.
Lemma lem1267226 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem1267227 (m : nat) (n : nat) : term60 m n.
Proof. exact (EQ_MP (@lem1267226 m n) (@lem1267225 m n)). Qed.
Lemma lem1267228 (m : nat) (n : nat) (p : nat) : term61 m n p.
Proof. exact (@lem1267227 m n p). Qed.
Lemma lem1267229 (m : nat) (n : nat) (p : nat) : (term61 m n p) = ((term62 m n p) = (term63 m n p)).
Proof. exact (eq_refl (term61 m n p)). Qed.
Lemma lem1267231 (m : nat) : term64 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1267232 (m : nat) : (term64 m) = (term22 m).
Proof. exact (eq_refl (term64 m)). Qed.
Lemma lem1267233 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1267232 m) (@lem1267231 m)). Qed.
Lemma lem1267234 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem1267233 m n). Qed.
Lemma lem1267235 (n : nat) (m : nat) : (term65 m n) = (term18 n m).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1267236 (n : nat) (m : nat) : term18 n m.
Proof. exact (EQ_MP (@lem1267235 n m) (@lem1267234 m n)). Qed.
Lemma lem1267237 (n : nat) (m : nat) (p : nat) : term66 n m p.
Proof. exact (@lem1267236 n m p). Qed.
Lemma lem1267238 (n : nat) (m : nat) (p : nat) : (term66 n m p) = ((term14 m n p) = (term15 n m p)).
Proof. exact (eq_refl (term66 n m p)). Qed.
Lemma lem1267240 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem1267241 (m : nat) (h1 : term67) : term68 m.
Proof. exact (@lem1267240 h1 m). Qed.
Lemma lem1267242 (m : nat) : (term68 m) = (term69 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem1267243 (m : nat) (h1 : term67) : term69 m.
Proof. exact (EQ_MP (@lem1267242 m) (@lem1267241 m h1)). Qed.
Lemma lem1267244 (m : nat) (n : nat) (h1 : term67) : term70 m n.
Proof. exact (@lem1267243 m h1 n). Qed.
Lemma lem1267245 (n : nat) (m : nat) : (term70 m n) = (term71 n m).
Proof. exact (eq_refl (term70 m n)). Qed.
Lemma lem1267246 (n : nat) (m : nat) (h1 : term67) : term71 n m.
Proof. exact (EQ_MP (@lem1267245 n m) (@lem1267244 m n h1)). Qed.
Lemma lem1267247 (n : nat) (m : nat) (p : nat) (h1 : term67) : term72 n m p.
Proof. exact (@lem1267246 n m h1 p). Qed.
Lemma lem1267248 (n : nat) (m : nat) (p : nat) : (term72 n m p) = (term73 n m p).
Proof. exact (eq_refl (term72 n m p)). Qed.
Lemma lem1267249 (n : nat) (m : nat) (p : nat) (h1 : term67) : term73 n m p.
Proof. exact (EQ_MP (@lem1267248 n m p) (@lem1267247 n m p h1)). Qed.
Lemma lem1267250 (m : nat) (n : nat) (p : nat) (h1 : term74 m n p) : term74 m n p.
Proof. exact (h1). Qed.
Lemma lem1267251 (m : nat) (n : nat) (p : nat) (h1 : term67) (h2 : term74 m n p) : Peano.le m p.
Proof. exact (@lem1267249 n m p h1 (@lem1267250 m n p h2)). Qed.
Lemma lem1267252 (m : nat) (n : nat) (p : nat) (h1 : term74 m n p) : term75 m p.
Proof. exact (fun h0 : term67 => @lem1267251 m n p h0 h1). Qed.
Lemma lem1267253 (m : nat) (p : nat) (h1 : term76 m p) : term76 m p.
Proof. exact (h1). Qed.
Lemma lem1267254 (m : nat) (p : nat) (h1 : term76 m p) : term75 m p.
Proof. exact (ex_elim (@lem1267253 m p h1) (fun n : nat => fun h0 : term77 m p n => @lem1267252 m n p h0)). Qed.
Lemma lem1267255 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem1267256 (m : nat) (p : nat) (h1 : term67) (h2 : term76 m p) : Peano.le m p.
Proof. exact (@lem1267254 m p h2 (@lem1267255 h1)). Qed.
Lemma lem1267257 (m : nat) (p : nat) (h1 : term67) : term78 m p.
Proof. exact (fun h0 : term76 m p => @lem1267256 m p h1 h0). Qed.
Lemma lem1267258 (m : nat) (h1 : term67) : term79 m.
Proof. exact (fun p : nat => @lem1267257 m p h1). Qed.
Lemma lem1267259 (h1 : term67) : term80.
Proof. exact (fun m : nat => @lem1267258 m h1). Qed.
Lemma lem1267260 : term81.
Proof. exact (fun h0 : term67 => @lem1267259 h0). Qed.
Lemma lem1267261 : term80.
Proof. exact (@lem1267260 (@lem93743)). Qed.
Lemma lem1267262 (m : nat) : term82 m.
Proof. exact (@lem1267261 m). Qed.
Lemma lem1267263 (m : nat) : (term82 m) = (term79 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1267264 (m : nat) : term79 m.
Proof. exact (EQ_MP (@lem1267263 m) (@lem1267262 m)). Qed.
Lemma lem1267265 (m : nat) (p : nat) : term83 m p.
Proof. exact (@lem1267264 m p). Qed.
Lemma lem1267266 (m : nat) (p : nat) : (term83 m p) = (term78 m p).
Proof. exact (eq_refl (term83 m p)). Qed.
Lemma lem1267268 (m : nat) : term84 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1267269 (m : nat) : (term84 m) = (term85 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem1267270 (m : nat) : term85 m.
Proof. exact (EQ_MP (@lem1267269 m) (@lem1267268 m)). Qed.
Lemma lem1267271 (m : nat) (n : nat) : term86 m n.
Proof. exact (@lem1267270 m n). Qed.
Lemma lem1267272 (n : nat) (m : nat) : (term86 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem1267274 (y : nadd) : term87 y.
Proof. exact (@lem1263160 y). Qed.
Lemma lem1267275 (y : nadd) : (term87 y) = (term88 y).
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1267276 (y : nadd) : term88 y.
Proof. exact (EQ_MP (@lem1267275 y) (@lem1267274 y)). Qed.
Lemma lem1267277 (x : nadd) : term89 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1267278 (x : nadd) : (term89 x) = (term90 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1267279 (x : nadd) : term90 x.
Proof. exact (EQ_MP (@lem1267278 x) (@lem1267277 x)). Qed.
Lemma lem1267280 (x : nadd) (B : nat) (h1 : term91 x B) : term91 x B.
Proof. exact (h1). Qed.
Lemma lem1267281 (y : nadd) (h1 : term88 y) : term88 y.
Proof. exact (h1). Qed.
Lemma lem1267282 (y : nadd) (M : nat) (h1 : term92 y M) : term92 y M.
Proof. exact (h1). Qed.
Lemma lem1267283 (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : term93 y M L.
Proof. exact (h1). Qed.
Lemma lem1267285 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1267272 n m) (@lem1267271 m n)). Qed.
Lemma lem1267286 (y : nadd) (x : nadd) (n : nat) : (term94 x y n) = (term94 y x n).
Proof. exact (@lem1267285 (dest_nadd y n) (dest_nadd x n)). Qed.
Lemma lem1267287 (x : nadd) (y : nadd) (n : nat) : (term95 x y n) = (term95 x y n).
Proof. exact (eq_refl (term95 x y n)). Qed.
Lemma lem1267288 (y : nadd) (x : nadd) (n : nat) : (term96 x y n) = (term97 y x n).
Proof. exact (MK_COMB (@lem1267287 x y n) (@lem1267286 y x n)). Qed.
Lemma lem1267289 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1267290 (y : nadd) (x : nadd) (n : nat) : (term98 x y n) = (term99 y x n).
Proof. exact (MK_COMB (@lem1267289) (@lem1267288 y x n)). Qed.
Lemma lem1267291 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1267292 (y : nadd) (x : nadd) (n : nat) : (term100 x y n) = (term101 y x n).
Proof. exact (MK_COMB (@lem1267291) (@lem1267290 y x n)). Qed.
Lemma lem1267293 (M : nat) (n : nat) (B : nat) (L : nat) : (term102 M n B L) = (term102 M n B L).
Proof. exact (eq_refl (term102 M n B L)). Qed.
Lemma lem1267294 (y : nadd) (x : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term103 x y M n B L) = (term104 y x M n B L).
Proof. exact (MK_COMB (@lem1267292 y x n) (@lem1267293 M n B L)). Qed.
Lemma lem1267295 (x : nadd) (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term104 y x M n B L) = (term103 x y M n B L).
Proof. exact (SYM (@lem1267294 y x M n B L)). Qed.
Lemma lem1267297 (m : nat) (p : nat) : term78 m p.
Proof. exact (EQ_MP (@lem1267266 m p) (@lem1267265 m p)). Qed.
Lemma lem1267298 (y : nadd) (x : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : term105 y x M n B L.
Proof. exact (@lem1267297 (term99 y x n) (term102 M n B L)). Qed.
Lemma lem1267299 (m : nat) (x : nadd) (B : nat) (h1 : term91 x B) : term106 x B m.
Proof. exact (@lem1267280 x B h1 m). Qed.
Lemma lem1267300 (x : nadd) (B : nat) (m : nat) : (term106 x B m) = (term107 x B m).
Proof. exact (eq_refl (term106 x B m)). Qed.
Lemma lem1267301 (m : nat) (x : nadd) (B : nat) (h1 : term91 x B) : term107 x B m.
Proof. exact (EQ_MP (@lem1267300 x B m) (@lem1267299 m x B h1)). Qed.
Lemma lem1267302 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term91 x B) : term108 x B m n.
Proof. exact (@lem1267301 m x B h1 n). Qed.
Lemma lem1267303 (x : nadd) (B : nat) (m : nat) (n : nat) : (term108 x B m n) = (term109 x B m n).
Proof. exact (eq_refl (term108 x B m n)). Qed.
Lemma lem1267304 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term91 x B) : term109 x B m n.
Proof. exact (EQ_MP (@lem1267303 x B m n) (@lem1267302 m n x B h1)). Qed.
Lemma lem1267305 (x : nadd) (B : nat) (m : nat) (n : nat) : (term109 x B m n) = ((term109 x B m n) = True).
Proof. exact (@lem7 (term109 x B m n)). Qed.
Lemma lem1267315 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term91 x B) : (term109 x B m n) = True.
Proof. exact (EQ_MP (@lem1267305 x B m n) (@lem1267304 m n x B h1)). Qed.
Lemma lem1267316 (y : nadd) (n : nat) (x : nadd) (B : nat) (h1 : term91 x B) : (term110 x B y n) = True.
Proof. exact (@lem1267315 n (dest_nadd y n) x B h1). Qed.
Lemma lem1267317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1267318 (y : nadd) (n : nat) (x : nadd) (B : nat) (h1 : term91 x B) : (term111 x B y n) = (and True).
Proof. exact (MK_COMB (@lem1267317) (@lem1267316 y n x B h1)). Qed.
Lemma lem1267319 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term112 y M n B L) = (term112 y M n B L).
Proof. exact (eq_refl (term112 y M n B L)). Qed.
Lemma lem1267320 (y : nadd) (M : nat) (n : nat) (L : nat) (x : nadd) (B : nat) (h1 : term91 x B) : (term113 x y M n B L) = (term114 y M n B L).
Proof. exact (MK_COMB (@lem1267318 y n x B h1) (@lem1267319 y M n B L)). Qed.
Lemma lem1267322 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1267323 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term114 y M n B L) = (term112 y M n B L).
Proof. exact (@lem1267322 (term112 y M n B L)). Qed.
Lemma lem1267324 (y : nadd) (M : nat) (n : nat) (L : nat) (x : nadd) (B : nat) (h1 : term91 x B) : (term113 x y M n B L) = (term112 y M n B L).
Proof. exact (TRANS (@lem1267320 y M n L x B h1) (@lem1267323 y M n B L)). Qed.
Lemma lem1267325 (y : nadd) (M : nat) (n : nat) (L : nat) (x : nadd) (B : nat) (h1 : term91 x B) : (term112 y M n B L) = (term113 x y M n B L).
Proof. exact (SYM (@lem1267324 y M n L x B h1)). Qed.
Lemma lem1267327 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term15 n m p).
Proof. exact (EQ_MP (@lem1267238 n m p) (@lem1267237 n m p)). Qed.
Lemma lem1267328 (B : nat) (y : nadd) (n : nat) : (term115 B y n) = (term116 B y n).
Proof. exact (@lem1267327 n B (dest_nadd y n)). Qed.
Lemma lem1267329 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1267330 (B : nat) (y : nadd) (n : nat) : (term117 B y n) = (term118 B y n).
Proof. exact (MK_COMB (@lem1267329) (@lem1267328 B y n)). Qed.
Lemma lem1267332 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term15 n m p).
Proof. exact (EQ_MP (@lem1267238 n m p) (@lem1267237 n m p)). Qed.
Lemma lem1267333 (B : nat) (M : nat) : (term119 B M) = (term120 B M).
Proof. exact (@lem1267332 term121 B M). Qed.
Lemma lem1267334 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1267335 (B : nat) (M : nat) : (term122 B M) = (term123 B M).
Proof. exact (MK_COMB (@lem1267334) (@lem1267333 B M)). Qed.
Lemma lem1267336 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1267337 (B : nat) (M : nat) (n : nat) : (term124 B M n) = (term125 B M n).
Proof. exact (MK_COMB (@lem1267335 B M) (@lem1267336 n)). Qed.
Lemma lem1267339 (m : nat) (n : nat) (p : nat) : (term62 m n p) = (term63 m n p).
Proof. exact (EQ_MP (@lem1267229 m n p) (@lem1267228 m n p)). Qed.
Lemma lem1267340 (B : nat) (M : nat) (n : nat) : (term125 B M n) = (term126 B M n).
Proof. exact (@lem1267339 (term56 B) (Nat.mul B M) n). Qed.
Lemma lem1267341 (B : nat) (M : nat) (n : nat) : (term124 B M n) = (term126 B M n).
Proof. exact (TRANS (@lem1267337 B M n) (@lem1267340 B M n)). Qed.
Lemma lem1267342 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1267343 (B : nat) (M : nat) (n : nat) : (term127 B M n) = (term128 B M n).
Proof. exact (MK_COMB (@lem1267342) (@lem1267341 B M n)). Qed.
Lemma lem1267344 (B : nat) (L : nat) : (Nat.mul B L) = (Nat.mul B L).
Proof. exact (eq_refl (Nat.mul B L)). Qed.
Lemma lem1267345 (M : nat) (n : nat) (B : nat) (L : nat) : (term102 M n B L) = (term129 M n B L).
Proof. exact (MK_COMB (@lem1267343 B M n) (@lem1267344 B L)). Qed.
Lemma lem1267346 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term112 y M n B L) = (term130 y M n B L).
Proof. exact (MK_COMB (@lem1267330 B y n) (@lem1267345 M n B L)). Qed.
Lemma lem1267347 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term130 y M n B L) = (term112 y M n B L).
Proof. exact (SYM (@lem1267346 y M n B L)). Qed.
Lemma lem1267351 (m : nat) (n : nat) (p : nat) : (term29 m n p) = (term28 m n p).
Proof. exact (EQ_MP (@lem1267186 m n p) (@lem1267185 m n p)). Qed.
Lemma lem1267352 (M : nat) (n : nat) (B : nat) (L : nat) : (term129 M n B L) = (term131 M n B L).
Proof. exact (@lem1267351 (term132 B n) (term1 B M n) (Nat.mul B L)). Qed.
Lemma lem1267354 (m : nat) : (term56 m) = m.
Proof. exact (EQ_MP (@lem1267208 m) (@lem1267207 m)). Qed.
Lemma lem1267355 (B : nat) : (term56 B) = B.
Proof. exact (@lem1267354 B). Qed.
Lemma lem1267356 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1267357 (B : nat) : (term133 B) = (Nat.mul B).
Proof. exact (MK_COMB (@lem1267356) (@lem1267355 B)). Qed.
Lemma lem1267358 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1267359 (B : nat) (n : nat) : (term132 B n) = (Nat.mul B n).
Proof. exact (MK_COMB (@lem1267357 B) (@lem1267358 n)). Qed.
Lemma lem1267360 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1267361 (B : nat) (n : nat) : (term134 B n) = (term135 B n).
Proof. exact (MK_COMB (@lem1267360) (@lem1267359 B n)). Qed.
Lemma lem1267362 (M : nat) (n : nat) (B : nat) (L : nat) : (term136 M n B L) = (term136 M n B L).
Proof. exact (eq_refl (term136 M n B L)). Qed.
Lemma lem1267363 (M : nat) (n : nat) (B : nat) (L : nat) : (term131 M n B L) = (term137 M n B L).
Proof. exact (MK_COMB (@lem1267361 B n) (@lem1267362 M n B L)). Qed.
Lemma lem1267364 (M : nat) (n : nat) (B : nat) (L : nat) : (term129 M n B L) = (term137 M n B L).
Proof. exact (TRANS (@lem1267352 M n B L) (@lem1267363 M n B L)). Qed.
Lemma lem1267365 (B : nat) (y : nadd) (n : nat) : (term118 B y n) = (term118 B y n).
Proof. exact (eq_refl (term118 B y n)). Qed.
Lemma lem1267366 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term130 y M n B L) = (term138 y M n B L).
Proof. exact (MK_COMB (@lem1267365 B y n) (@lem1267364 M n B L)). Qed.
Lemma lem1267368 (m : nat) (n : nat) (p : nat) : (term47 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1267177 m n p) (@lem1267176 m n p)). Qed.
Lemma lem1267369 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term138 y M n B L) = (term139 y M n B L).
Proof. exact (@lem1267368 (Nat.mul B n) (term140 B y n) (term136 M n B L)). Qed.
Lemma lem1267370 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term130 y M n B L) = (term139 y M n B L).
Proof. exact (TRANS (@lem1267366 y M n B L) (@lem1267369 y M n B L)). Qed.
Lemma lem1267371 (y : nadd) (M : nat) (n : nat) (B : nat) (L : nat) : (term139 y M n B L) = (term130 y M n B L).
Proof. exact (SYM (@lem1267370 y M n B L)). Qed.
Lemma lem1267372 (m : nat) : term141 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1267373 (m : nat) : (term141 m) = (term142 m).
Proof. exact (eq_refl (term141 m)). Qed.
Lemma lem1267374 (m : nat) : term142 m.
Proof. exact (EQ_MP (@lem1267373 m) (@lem1267372 m)). Qed.
Lemma lem1267375 (m : nat) (n : nat) : term143 m n.
Proof. exact (@lem1267374 m n). Qed.
Lemma lem1267376 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (eq_refl (term143 m n)). Qed.
Lemma lem1267377 (m : nat) (n : nat) : term144 m n.
Proof. exact (EQ_MP (@lem1267376 m n) (@lem1267375 m n)). Qed.
Lemma lem1267378 (m : nat) (n : nat) (p : nat) : term145 m n p.
Proof. exact (@lem1267377 m n p). Qed.
Lemma lem1267379 (m : nat) (n : nat) (p : nat) : (term145 m n p) = ((term146 n m p) = (term147 m n p)).
Proof. exact (eq_refl (term145 m n p)). Qed.
Lemma lem1267381 (m : nat) : term148 m.
Proof. exact (@lem1267133 m). Qed.
Lemma lem1267382 (m : nat) : (term148 m) = (term9 m).
Proof. exact (eq_refl (term148 m)). Qed.
Lemma lem1267383 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1267382 m) (@lem1267381 m)). Qed.
Lemma lem1267384 (m : nat) (n : nat) : term149 m n.
Proof. exact (@lem1267383 m n). Qed.
Lemma lem1267385 (m : nat) (n : nat) : (term149 m n) = (term5 m n).
Proof. exact (eq_refl (term149 m n)). Qed.
Lemma lem1267386 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1267385 m n) (@lem1267384 m n)). Qed.
Lemma lem1267387 (m : nat) (n : nat) (p : nat) : term150 m n p.
Proof. exact (@lem1267386 m n p). Qed.
Lemma lem1267388 (m : nat) (n : nat) (p : nat) : (term150 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term150 m n p)). Qed.
Lemma lem1267390 (m : nat) : term151 m.
Proof. exact (@lem1267151 m). Qed.
Lemma lem1267391 (m : nat) : (term151 m) = (term23 m).
Proof. exact (eq_refl (term151 m)). Qed.
Lemma lem1267392 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem1267391 m) (@lem1267390 m)). Qed.
Lemma lem1267393 (m : nat) (n : nat) : term152 m n.
Proof. exact (@lem1267392 m n). Qed.
Lemma lem1267394 (m : nat) (n : nat) : (term152 m n) = (term19 m n).
Proof. exact (eq_refl (term152 m n)). Qed.
Lemma lem1267395 (m : nat) (n : nat) : term19 m n.
Proof. exact (EQ_MP (@lem1267394 m n) (@lem1267393 m n)). Qed.
Lemma lem1267396 (m : nat) (n : nat) (p : nat) : term153 m n p.
Proof. exact (@lem1267395 m n p). Qed.
Lemma lem1267397 (m : nat) (n : nat) (p : nat) : (term153 m n p) = ((term15 n m p) = (term14 m n p)).
Proof. exact (eq_refl (term153 m n p)). Qed.
Lemma lem1267407 (n : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : term154 y M L n.
Proof. exact (@lem1267283 y M L h1 n). Qed.
Lemma lem1267408 (y : nadd) (M : nat) (n : nat) (L : nat) : (term154 y M L n) = (term155 y M n L).
Proof. exact (eq_refl (term154 y M L n)). Qed.
Lemma lem1267409 (n : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : term155 y M n L.
Proof. exact (EQ_MP (@lem1267408 y M n L) (@lem1267407 n y M L h1)). Qed.
Lemma lem1267410 (y : nadd) (M : nat) (n : nat) (L : nat) : (term155 y M n L) = ((term155 y M n L) = True).
Proof. exact (@lem7 (term155 y M n L)). Qed.
Lemma lem1267415 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1267388 m n p) (@lem1267387 m n p)). Qed.
Lemma lem1267416 (B : nat) (M : nat) (n : nat) : (term1 B M n) = (term0 B M n).
Proof. exact (@lem1267415 B M n). Qed.
Lemma lem1267417 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1267418 (B : nat) (M : nat) (n : nat) : (term156 B M n) = (term157 B M n).
Proof. exact (MK_COMB (@lem1267417) (@lem1267416 B M n)). Qed.
Lemma lem1267419 (B : nat) (L : nat) : (Nat.mul B L) = (Nat.mul B L).
Proof. exact (eq_refl (Nat.mul B L)). Qed.
Lemma lem1267420 (M : nat) (n : nat) (B : nat) (L : nat) : (term136 M n B L) = (term158 M n B L).
Proof. exact (MK_COMB (@lem1267418 B M n) (@lem1267419 B L)). Qed.
Lemma lem1267422 (m : nat) (n : nat) (p : nat) : (term15 n m p) = (term14 m n p).
Proof. exact (EQ_MP (@lem1267397 m n p) (@lem1267396 m n p)). Qed.
Lemma lem1267423 (B : nat) (M : nat) (n : nat) (L : nat) : (term158 M n B L) = (term159 B M n L).
Proof. exact (@lem1267422 B (Nat.mul M n) L). Qed.
Lemma lem1267424 (B : nat) (M : nat) (n : nat) (L : nat) : (term136 M n B L) = (term159 B M n L).
Proof. exact (TRANS (@lem1267420 M n B L) (@lem1267423 B M n L)). Qed.
Lemma lem1267425 (B : nat) (y : nadd) (n : nat) : (term160 B y n) = (term160 B y n).
Proof. exact (eq_refl (term160 B y n)). Qed.
Lemma lem1267426 (y : nadd) (B : nat) (M : nat) (n : nat) (L : nat) : (term139 y M n B L) = (term161 y B M n L).
Proof. exact (MK_COMB (@lem1267425 B y n) (@lem1267424 B M n L)). Qed.
Lemma lem1267428 (m : nat) (n : nat) (p : nat) : (term146 n m p) = (term147 m n p).
Proof. exact (EQ_MP (@lem1267379 m n p) (@lem1267378 m n p)). Qed.
Lemma lem1267429 (B : nat) (y : nadd) (M : nat) (n : nat) (L : nat) : (term161 y B M n L) = (term162 B y M n L).
Proof. exact (@lem1267428 B (dest_nadd y n) (term163 M n L)). Qed.
Lemma lem1267435 (n : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : (term155 y M n L) = True.
Proof. exact (EQ_MP (@lem1267410 y M n L) (@lem1267409 n y M L h1)). Qed.
Lemma lem1267436 (B : nat) : (term164 B) = (term164 B).
Proof. exact (eq_refl (term164 B)). Qed.
Lemma lem1267437 (n : nat) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : (term162 B y M n L) = (term165 B).
Proof. exact (MK_COMB (@lem1267436 B) (@lem1267435 n y M L h1)). Qed.
Lemma lem1267439 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1267440 (B : nat) : (term165 B) = True.
Proof. exact (@lem1267439 (B = (NUMERAL 0))). Qed.
Lemma lem1267441 (B : nat) (n : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : (term162 B y M n L) = True.
Proof. exact (TRANS (@lem1267437 n B y M L h1) (@lem1267440 B)). Qed.
Lemma lem1267442 (B : nat) (n : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : (term161 y B M n L) = True.
Proof. exact (TRANS (@lem1267429 B y M n L) (@lem1267441 B n y M L h1)). Qed.
Lemma lem1267443 (n : nat) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : (term139 y M n B L) = True.
Proof. exact (TRANS (@lem1267426 y B M n L) (@lem1267442 B n y M L h1)). Qed.
Lemma lem1267444 (n : nat) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : True = (term139 y M n B L).
Proof. exact (SYM (@lem1267443 n B y M L h1)). Qed.
Lemma lem1267445 (n : nat) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : term139 y M n B L.
Proof. exact (EQ_MP (@lem1267444 n B y M L h1) (@lem0)). Qed.
Lemma lem1267446 (n : nat) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : term130 y M n B L.
Proof. exact (EQ_MP (@lem1267371 y M n B L) (@lem1267445 n B y M L h1)). Qed.
Lemma lem1267447 (n : nat) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term93 y M L) : term112 y M n B L.
Proof. exact (EQ_MP (@lem1267347 y M n B L) (@lem1267446 n B y M L h1)). Qed.
Lemma lem1267448 (n : nat) (x : nadd) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term91 x B) (h2 : term93 y M L) : term113 x y M n B L.
Proof. exact (EQ_MP (@lem1267325 y M n L x B h1) (@lem1267447 n B y M L h2)). Qed.
Lemma lem1267449 (n : nat) (x : nadd) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term91 x B) (h2 : term93 y M L) : term166 y x M n B L.
Proof. exact (ex_intro (term167 y x M n B L) (term115 B y n) (@lem1267448 n x B y M L h1 h2)). Qed.
Lemma lem1267450 (n : nat) (x : nadd) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term91 x B) (h2 : term93 y M L) : term104 y x M n B L.
Proof. exact (@lem1267298 y x M n B L (@lem1267449 n x B y M L h1 h2)). Qed.
Lemma lem1267451 (n : nat) (x : nadd) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term91 x B) (h2 : term93 y M L) : term103 x y M n B L.
Proof. exact (EQ_MP (@lem1267295 x y M n B L) (@lem1267450 n x B y M L h1 h2)). Qed.
Lemma lem1267456 (x : nadd) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term91 x B) (h2 : term93 y M L) : term168 x y M B L.
Proof. exact (fun n : nat => @lem1267451 n x B y M L h1 h2). Qed.
Lemma lem1267457 (x : nadd) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term91 x B) (h2 : term93 y M L) : term169 x y B M.
Proof. exact (ex_intro (term170 x y B M) (Nat.mul B L) (@lem1267456 x B y M L h1 h2)). Qed.
Lemma lem1267458 (x : nadd) (B : nat) (y : nadd) (M : nat) (L : nat) (h1 : term91 x B) (h2 : term93 y M L) : term171 x y.
Proof. exact (ex_intro (term172 x y) (term119 B M) (@lem1267457 x B y M L h1 h2)). Qed.
Lemma lem1267459 (x : nadd) (B : nat) (y : nadd) (M : nat) (h1 : term91 x B) (h2 : term92 y M) : term171 x y.
Proof. exact (ex_elim (@lem1267282 y M h2) (fun L : nat => fun h0 : term173 y M L => @lem1267458 x B y M L h1 h0)). Qed.
Lemma lem1267460 (x : nadd) (B : nat) (y : nadd) (h1 : term91 x B) (h2 : term88 y) : term171 x y.
Proof. exact (ex_elim (@lem1267281 y h2) (fun M : nat => fun h0 : term174 y M => @lem1267459 x B y M h1 h0)). Qed.
Lemma lem1267461 (y : nadd) (x : nadd) (B : nat) (h1 : term91 x B) : term175 x y.
Proof. exact (fun h0 : term88 y => @lem1267460 x B y h1 h0). Qed.
Lemma lem1267462 (y : nadd) (x : nadd) (B : nat) (h1 : term91 x B) : term171 x y.
Proof. exact (@lem1267461 y x B h1 (@lem1267276 y)). Qed.
Lemma lem1267463 (x : nadd) (y : nadd) : term171 x y.
Proof. exact (ex_elim (@lem1267279 x) (fun B : nat => fun h0 : term176 x B => @lem1267462 y x B h0)). Qed.
Lemma lem1267468 (x : nadd) : term177 x.
Proof. exact (fun y : nadd => @lem1267463 x y). Qed.
Lemma lem1267473 : term178.
Proof. exact (fun x : nadd => @lem1267468 x). Qed.
