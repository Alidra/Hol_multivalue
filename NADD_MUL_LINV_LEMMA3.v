Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA3_term_abbrevs.
Require Import DIST_LMUL_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import MULT_ASSOC_spec.
Require Import NADD_MUL_LINV_LEMMA2_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem1302160 (m : nat) : term0 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1302161 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1302162 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1302161 m) (@lem1302160 m)). Qed.
Lemma lem1302163 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1302162 m n). Qed.
Lemma lem1302164 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1302165 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1302164 m n) (@lem1302163 m n)). Qed.
Lemma lem1302166 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1302165 m n p). Qed.
Lemma lem1302167 (m : nat) (n : nat) (p : nat) : (term4 m n p) = ((term5 n m p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1302172 (n : nat) (m : nat) (p : nat) (h1 : (term7 m n p) = (term8 n m p)) : (term7 m n p) = (term8 n m p).
Proof. exact (h1). Qed.
Lemma lem1302173 (n : nat) (m : nat) (p : nat) (h1 : (term7 m n p) = (term8 n m p)) : (term8 n m p) = (term7 m n p).
Proof. exact (SYM (@lem1302172 n m p h1)). Qed.
Lemma lem1302174 (m : nat) (n : nat) (p : nat) (h1 : (term8 n m p) = (term7 m n p)) : (term8 n m p) = (term7 m n p).
Proof. exact (h1). Qed.
Lemma lem1302175 (m : nat) (n : nat) (p : nat) (h1 : (term8 n m p) = (term7 m n p)) : (term7 m n p) = (term8 n m p).
Proof. exact (SYM (@lem1302174 m n p h1)). Qed.
Lemma lem1302176 (m : nat) (n : nat) (p : nat) : ((term7 m n p) = (term8 n m p)) = ((term8 n m p) = (term7 m n p)).
Proof. exact (prop_ext (fun h1 : (term7 m n p) = (term8 n m p) => @lem1302173 n m p h1) (fun h1 : (term8 n m p) = (term7 m n p) => @lem1302175 m n p h1)). Qed.
Lemma lem1302177 (m : nat) (n : nat) : (term9 n m) = (term10 m n).
Proof. exact (fun_ext (fun p : nat => @lem1302176 m n p)). Qed.
Lemma lem1302178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1302179 (m : nat) (n : nat) : (term11 n m) = (term12 m n).
Proof. exact (MK_COMB (@lem1302178) (@lem1302177 m n)). Qed.
Lemma lem1302180 (m : nat) : (term13 m) = (term14 m).
Proof. exact (fun_ext (fun n : nat => @lem1302179 m n)). Qed.
Lemma lem1302181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1302182 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem1302181) (@lem1302180 m)). Qed.
Lemma lem1302183 : term17 = term18.
Proof. exact (fun_ext (fun m : nat => @lem1302182 m)). Qed.
Lemma lem1302184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1302185 : term19 = term20.
Proof. exact (MK_COMB (@lem1302184) (@lem1302183)). Qed.
Lemma lem1302186 : term20.
Proof. exact (EQ_MP (@lem1302185) (@lem1245388)). Qed.
Lemma lem1302187 (m : nat) : term21 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem1302188 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1302189 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1302188 m) (@lem1302187 m)). Qed.
Lemma lem1302190 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1302189 m n). Qed.
Lemma lem1302191 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1302192 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1302191 m n) (@lem1302190 m n)). Qed.
Lemma lem1302193 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1302192 m n p). Qed.
Lemma lem1302194 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1302196 (m : nat) : term28 m.
Proof. exact (@lem1302186 m). Qed.
Lemma lem1302197 (m : nat) : (term28 m) = (term16 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1302198 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1302197 m) (@lem1302196 m)). Qed.
Lemma lem1302199 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1302198 m n). Qed.
Lemma lem1302200 (m : nat) (n : nat) : (term29 m n) = (term12 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1302201 (m : nat) (n : nat) : term12 m n.
Proof. exact (EQ_MP (@lem1302200 m n) (@lem1302199 m n)). Qed.
Lemma lem1302202 (m : nat) (n : nat) (p : nat) : term30 m n p.
Proof. exact (@lem1302201 m n p). Qed.
Lemma lem1302203 (m : nat) (n : nat) (p : nat) : (term30 m n p) = ((term8 n m p) = (term7 m n p)).
Proof. exact (eq_refl (term30 m n p)). Qed.
Lemma lem1302205 (x : nadd) : term31 x.
Proof. exact (@lem1302159 x). Qed.
Lemma lem1302206 (x : nadd) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1302208 (x : nadd) (h1 : term33 x) : term33 x.
Proof. exact (h1). Qed.
Lemma lem1302210 (x : nadd) : term32 x.
Proof. exact (EQ_MP (@lem1302206 x) (@lem1302205 x)). Qed.
Lemma lem1302211 (x : nadd) (h1 : term33 x) : term34 x.
Proof. exact (@lem1302210 x (@lem1302208 x h1)). Qed.
Lemma lem1302212 (x : nadd) (h1 : term34 x) : term34 x.
Proof. exact (h1). Qed.
Lemma lem1302213 (N : nat) (x : nadd) (h1 : term35 N x) : term35 N x.
Proof. exact (h1). Qed.
Lemma lem1302214 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302216 (m : nat) (n : nat) (p : nat) : (term8 n m p) = (term7 m n p).
Proof. exact (EQ_MP (@lem1302203 m n p) (@lem1302202 m n p)). Qed.
Lemma lem1302217 (x : nadd) (m : nat) (n : nat) : (term36 x m n) = (term37 x m n).
Proof. exact (@lem1302216 m (term38 m x n) (term39 x m n)). Qed.
Lemma lem1302219 (m : nat) (n : nat) (p : nat) : (term8 n m p) = (term7 m n p).
Proof. exact (EQ_MP (@lem1302203 m n p) (@lem1302202 m n p)). Qed.
Lemma lem1302220 (m : nat) (x : nadd) (n : nat) : (term40 x m n) = (term41 m x n).
Proof. exact (@lem1302219 (dest_nadd x m) (term42 x n) (Nat.mul n n)). Qed.
Lemma lem1302223 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1302224 (m : nat) (x : nadd) (n : nat) : (term37 x m n) = (term43 m x n).
Proof. exact (MK_COMB (@lem1302223 m) (@lem1302220 m x n)). Qed.
Lemma lem1302226 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1302194 m n p) (@lem1302193 m n p)). Qed.
Lemma lem1302227 (m : nat) (x : nadd) (n : nat) : (term43 m x n) = (term44 m x n).
Proof. exact (@lem1302226 m (dest_nadd x m) (term45 x n)). Qed.
Lemma lem1302230 (m : nat) (x : nadd) (n : nat) : (term37 x m n) = (term44 m x n).
Proof. exact (TRANS (@lem1302224 m x n) (@lem1302227 m x n)). Qed.
Lemma lem1302231 (m : nat) (x : nadd) (n : nat) : (term36 x m n) = (term44 m x n).
Proof. exact (TRANS (@lem1302217 x m n) (@lem1302230 m x n)). Qed.
Lemma lem1302232 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302233 (m : nat) (x : nadd) (n : nat) : (term46 x m n) = (term47 m x n).
Proof. exact (MK_COMB (@lem1302232) (@lem1302231 m x n)). Qed.
Lemma lem1302235 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1302194 m n p) (@lem1302193 m n p)). Qed.
Lemma lem1302236 (m : nat) (x : nadd) (n : nat) : (term48 m x n) = (term49 m x n).
Proof. exact (@lem1302235 m (dest_nadd x m) (dest_nadd x n)). Qed.
Lemma lem1302237 (m : nat) (x : nadd) (n : nat) : (term50 m x n) = (term51 m x n).
Proof. exact (MK_COMB (@lem1302233 m x n) (@lem1302236 m x n)). Qed.
Lemma lem1302238 (m : nat) (x : nadd) (n : nat) : (term51 m x n) = (term50 m x n).
Proof. exact (SYM (@lem1302237 m x n)). Qed.
Lemma lem1302240 (m : nat) (n : nat) (p : nat) : (term5 n m p) = (term6 m n p).
Proof. exact (EQ_MP (@lem1302167 m n p) (@lem1302166 m n p)). Qed.
Lemma lem1302241 (m : nat) (x : nadd) (n : nat) : (term51 m x n) = (term52 m x n).
Proof. exact (@lem1302240 (term53 x m) (term45 x n) (dest_nadd x n)). Qed.
Lemma lem1302246 (m : nat) (x : nadd) (n : nat) : (term52 m x n) = (term51 m x n).
Proof. exact (SYM (@lem1302241 m x n)). Qed.
Lemma lem1302247 (N : nat) (x : nadd) (h1 : term35 N x) : term35 N x.
Proof. exact (h1). Qed.
Lemma lem1302248 (n : nat) (N : nat) (x : nadd) (h1 : term35 N x) : term54 N x n.
Proof. exact (@lem1302247 N x h1 n). Qed.
Lemma lem1302249 (N : nat) (x : nadd) (n : nat) : (term54 N x n) = (term55 N x n).
Proof. exact (eq_refl (term54 N x n)). Qed.
Lemma lem1302250 (n : nat) (N : nat) (x : nadd) (h1 : term35 N x) : term55 N x n.
Proof. exact (EQ_MP (@lem1302249 N x n) (@lem1302248 n N x h1)). Qed.
Lemma lem1302251 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302252 (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : term56 x n.
Proof. exact (@lem1302250 n N x h1 (@lem1302251 N n h2)). Qed.
Lemma lem1302253 (x : nadd) (N : nat) (n : nat) (h1 : Peano.le N n) : term57 N x n.
Proof. exact (fun h0 : term35 N x => @lem1302252 x N n h0 h1). Qed.
Lemma lem1302254 (N : nat) (x : nadd) (h1 : term35 N x) : term35 N x.
Proof. exact (h1). Qed.
Lemma lem1302255 (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : term56 x n.
Proof. exact (@lem1302253 x N n h2 (@lem1302254 N x h1)). Qed.
Lemma lem1302256 (n : nat) (N : nat) (x : nadd) (h1 : term35 N x) : term55 N x n.
Proof. exact (fun h0 : Peano.le N n => @lem1302255 x N n h1 h0). Qed.
Lemma lem1302257 (N : nat) (x : nadd) (h1 : term35 N x) : term35 N x.
Proof. exact (fun n : nat => @lem1302256 n N x h1). Qed.
Lemma lem1302258 (N : nat) (x : nadd) : term58 N x.
Proof. exact (fun h0 : term35 N x => @lem1302257 N x h0). Qed.
Lemma lem1302259 (N : nat) (x : nadd) (h1 : term35 N x) : term35 N x.
Proof. exact (@lem1302258 N x (@lem1302213 N x h1)). Qed.
Lemma lem1302260 (n : nat) (N : nat) (x : nadd) (h1 : term35 N x) : term54 N x n.
Proof. exact (@lem1302259 N x h1 n). Qed.
Lemma lem1302261 (N : nat) (x : nadd) (n : nat) : (term54 N x n) = (term55 N x n).
Proof. exact (eq_refl (term54 N x n)). Qed.
Lemma lem1302264 (n : nat) (N : nat) (x : nadd) (h1 : term35 N x) : term55 N x n.
Proof. exact (EQ_MP (@lem1302261 N x n) (@lem1302260 n N x h1)). Qed.
Lemma lem1302270 (N : nat) (n : nat) : (Peano.le N n) = ((Peano.le N n) = True).
Proof. exact (@lem7 (Peano.le N n)). Qed.
Lemma lem1302273 (N : nat) (n : nat) (h1 : Peano.le N n) : (Peano.le N n) = True.
Proof. exact (EQ_MP (@lem1302270 N n) (@lem1302214 N n h1)). Qed.
Lemma lem1302274 (N : nat) (n : nat) (h1 : Peano.le N n) : True = (Peano.le N n).
Proof. exact (SYM (@lem1302273 N n h1)). Qed.
Lemma lem1302275 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (EQ_MP (@lem1302274 N n h1) (@lem0)). Qed.
Lemma lem1302276 (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : term56 x n.
Proof. exact (@lem1302264 n N x h1 (@lem1302275 N n h2)). Qed.
Lemma lem1302277 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : term52 m x n.
Proof. exact (or_intro2 ((term53 x m) = (NUMERAL 0)) (@lem1302276 x N n h1 h2)). Qed.
Lemma lem1302278 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : term51 m x n.
Proof. exact (EQ_MP (@lem1302246 m x n) (@lem1302277 m x N n h1 h2)). Qed.
Lemma lem1302279 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : term50 m x n.
Proof. exact (EQ_MP (@lem1302238 m x n) (@lem1302278 m x N n h1 h2)). Qed.
Lemma lem1302280 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : (Peano.le N n) = (term50 m x n).
Proof. exact (prop_ext (fun h3 : Peano.le N n => @lem1302279 m x N n h1 h2) (fun h3 : term50 m x n => @lem1302214 N n h2)). Qed.
Lemma lem1302281 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term35 N x) (h2 : Peano.le N n) : term50 m x n.
Proof. exact (EQ_MP (@lem1302280 m x N n h1 h2) (@lem1302214 N n h2)). Qed.
Lemma lem1302282 (m : nat) (n : nat) (N : nat) (x : nadd) (h1 : term35 N x) : term59 N m x n.
Proof. exact (fun h0 : Peano.le N n => @lem1302281 m x N n h1 h0). Qed.
Lemma lem1302287 (m : nat) (N : nat) (x : nadd) (h1 : term35 N x) : term60 N m x.
Proof. exact (fun n : nat => @lem1302282 m n N x h1). Qed.
Lemma lem1302292 (N : nat) (x : nadd) (h1 : term35 N x) : term61 N x.
Proof. exact (fun m : nat => @lem1302287 m N x h1). Qed.
Lemma lem1302293 (N : nat) (x : nadd) (h1 : term35 N x) : term62 x.
Proof. exact (ex_intro (term63 x) N (@lem1302292 N x h1)). Qed.
Lemma lem1302294 (x : nadd) (h1 : term34 x) : term62 x.
Proof. exact (ex_elim (@lem1302212 x h1) (fun N : nat => fun h0 : term64 x N => @lem1302293 N x h0)). Qed.
Lemma lem1302295 (x : nadd) : term65 x.
Proof. exact (fun h0 : term34 x => @lem1302294 x h0). Qed.
Lemma lem1302296 (x : nadd) (h1 : term33 x) : term62 x.
Proof. exact (@lem1302295 x (@lem1302211 x h1)). Qed.
Lemma lem1302297 (x : nadd) : term66 x.
Proof. exact (fun h0 : term33 x => @lem1302296 x h0). Qed.
Lemma lem1302302 : term67.
Proof. exact (fun x : nadd => @lem1302297 x). Qed.
