Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_FORALL_POS_term_abbrevs.
Require Import INT_ADD_LID_spec.
Require Import INT_IMAGE_spec.
Require Import INT_LE_RNEG_spec.
Require Import INT_OF_NUM_LE_spec.
Require Import LE_0_spec.
Require Import REAL_NEG_0_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm2306330_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm89498_spec.
Lemma lem2315140 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem2315141 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2315142 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2315141 n) (@lem2315140 n)). Qed.
Lemma lem2315143 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem2315145 (m : nat) : term2 m.
Proof. exact (@lem2307222 m). Qed.
Lemma lem2315146 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem2315147 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem2315146 m) (@lem2315145 m)). Qed.
Lemma lem2315148 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem2315147 m n). Qed.
Lemma lem2315149 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem2315151 (i : int) : term6 i.
Proof. exact (@lem2295400 i). Qed.
Lemma lem2315152 (i : int) : (term6 i) = (term7 i).
Proof. exact (eq_refl (term6 i)). Qed.
Lemma lem2315153 (i : int) : term7 i.
Proof. exact (EQ_MP (@lem2315152 i) (@lem2315151 i)). Qed.
Lemma lem2315154 (i : int) (h1 : term8 i) : term8 i.
Proof. exact (h1). Qed.
Lemma lem2315155 (i : int) (h1 : term9 i) : term9 i.
Proof. exact (h1). Qed.
Lemma lem2315156 (P : int -> Prop) (h1 : term10 P) : term10 P.
Proof. exact (h1). Qed.
Lemma lem2315157 (P : int -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem2315158 (i : int) (n : nat) (h1 : i = (int_of_num n)) : i = (int_of_num n).
Proof. exact (h1). Qed.
Lemma lem2315159 (P : int -> Prop) : (term12 P) = (term12 P).
Proof. exact (eq_refl (term12 P)). Qed.
Lemma lem2315160 (P : int -> Prop) (i : int) (n : nat) (h1 : i = (int_of_num n)) : (term13 P i) = (term14 P n).
Proof. exact (MK_COMB (@lem2315159 P) (@lem2315158 i n h1)). Qed.
Lemma lem2315161 (P : int -> Prop) (n : nat) : (term14 P n) = (term15 P n).
Proof. exact (eq_refl (term14 P n)). Qed.
Lemma lem2315162 (P : int -> Prop) (i : int) : (term16 P i) = (term16 P i).
Proof. exact (eq_refl (term16 P i)). Qed.
Lemma lem2315163 (i : int) (P : int -> Prop) (n : nat) : ((term13 P i) = (term14 P n)) = ((term13 P i) = (term15 P n)).
Proof. exact (MK_COMB (@lem2315162 P i) (@lem2315161 P n)). Qed.
Lemma lem2315164 (P : int -> Prop) (i : int) : (term13 P i) = (term17 P i).
Proof. exact (eq_refl (term13 P i)). Qed.
Lemma lem2315165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315166 (P : int -> Prop) (i : int) : (term16 P i) = (term18 P i).
Proof. exact (MK_COMB (@lem2315165) (@lem2315164 P i)). Qed.
Lemma lem2315167 (P : int -> Prop) (n : nat) : (term15 P n) = (term15 P n).
Proof. exact (eq_refl (term15 P n)). Qed.
Lemma lem2315168 (i : int) (P : int -> Prop) (n : nat) : ((term13 P i) = (term15 P n)) = ((term17 P i) = (term15 P n)).
Proof. exact (MK_COMB (@lem2315166 P i) (@lem2315167 P n)). Qed.
Lemma lem2315169 (i : int) (P : int -> Prop) (n : nat) : ((term13 P i) = (term14 P n)) = ((term17 P i) = (term15 P n)).
Proof. exact (TRANS (@lem2315163 i P n) (@lem2315168 i P n)). Qed.
Lemma lem2315170 (P : int -> Prop) (i : int) (n : nat) (h1 : i = (int_of_num n)) : (term17 P i) = (term15 P n).
Proof. exact (EQ_MP (@lem2315169 i P n) (@lem2315160 P i n h1)). Qed.
Lemma lem2315171 (P : int -> Prop) (i : int) (n : nat) (h1 : i = (int_of_num n)) : (term15 P n) = (term17 P i).
Proof. exact (SYM (@lem2315170 P i n h1)). Qed.
Lemma lem2315172 (i : int) (n : nat) (h1 : i = (term19 n)) : i = (term19 n).
Proof. exact (h1). Qed.
Lemma lem2315173 (P : int -> Prop) : (term12 P) = (term12 P).
Proof. exact (eq_refl (term12 P)). Qed.
Lemma lem2315174 (P : int -> Prop) (i : int) (n : nat) (h1 : i = (term19 n)) : (term13 P i) = (term20 P n).
Proof. exact (MK_COMB (@lem2315173 P) (@lem2315172 i n h1)). Qed.
Lemma lem2315175 (P : int -> Prop) (n : nat) : (term20 P n) = (term21 P n).
Proof. exact (eq_refl (term20 P n)). Qed.
Lemma lem2315176 (P : int -> Prop) (i : int) : (term16 P i) = (term16 P i).
Proof. exact (eq_refl (term16 P i)). Qed.
Lemma lem2315177 (i : int) (P : int -> Prop) (n : nat) : ((term13 P i) = (term20 P n)) = ((term13 P i) = (term21 P n)).
Proof. exact (MK_COMB (@lem2315176 P i) (@lem2315175 P n)). Qed.
Lemma lem2315178 (P : int -> Prop) (i : int) : (term13 P i) = (term17 P i).
Proof. exact (eq_refl (term13 P i)). Qed.
Lemma lem2315179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315180 (P : int -> Prop) (i : int) : (term16 P i) = (term18 P i).
Proof. exact (MK_COMB (@lem2315179) (@lem2315178 P i)). Qed.
Lemma lem2315181 (P : int -> Prop) (n : nat) : (term21 P n) = (term21 P n).
Proof. exact (eq_refl (term21 P n)). Qed.
Lemma lem2315182 (i : int) (P : int -> Prop) (n : nat) : ((term13 P i) = (term21 P n)) = ((term17 P i) = (term21 P n)).
Proof. exact (MK_COMB (@lem2315180 P i) (@lem2315181 P n)). Qed.
Lemma lem2315183 (i : int) (P : int -> Prop) (n : nat) : ((term13 P i) = (term20 P n)) = ((term17 P i) = (term21 P n)).
Proof. exact (TRANS (@lem2315177 i P n) (@lem2315182 i P n)). Qed.
Lemma lem2315184 (P : int -> Prop) (i : int) (n : nat) (h1 : i = (term19 n)) : (term17 P i) = (term21 P n).
Proof. exact (EQ_MP (@lem2315183 i P n) (@lem2315174 P i n h1)). Qed.
Lemma lem2315185 (P : int -> Prop) (i : int) (n : nat) (h1 : i = (term19 n)) : (term21 P n) = (term17 P i).
Proof. exact (SYM (@lem2315184 P i n h1)). Qed.
Lemma lem2315197 (m : nat) : term2 m.
Proof. exact (@lem2307222 m). Qed.
Lemma lem2315198 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem2315199 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem2315198 m) (@lem2315197 m)). Qed.
Lemma lem2315200 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem2315199 m n). Qed.
Lemma lem2315201 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem2315212 (n : nat) (P : int -> Prop) (h1 : term10 P) : term22 P n.
Proof. exact (@lem2315156 P h1 n). Qed.
Lemma lem2315213 (P : int -> Prop) (n : nat) : (term22 P n) = (term23 P n).
Proof. exact (eq_refl (term22 P n)). Qed.
Lemma lem2315214 (n : nat) (P : int -> Prop) (h1 : term10 P) : term23 P n.
Proof. exact (EQ_MP (@lem2315213 P n) (@lem2315212 n P h1)). Qed.
Lemma lem2315215 (P : int -> Prop) (n : nat) : (term23 P n) = ((term23 P n) = True).
Proof. exact (@lem7 (term23 P n)). Qed.
Lemma lem2315220 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2315201 m n) (@lem2315200 m n)). Qed.
Lemma lem2315221 (n : nat) : (term24 n) = (term1 n).
Proof. exact (@lem2315220 (NUMERAL 0) n). Qed.
Lemma lem2315222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2315223 (n : nat) : (term25 n) = (term26 n).
Proof. exact (MK_COMB (@lem2315222) (@lem2315221 n)). Qed.
Lemma lem2315225 (n : nat) (P : int -> Prop) (h1 : term10 P) : (term23 P n) = True.
Proof. exact (EQ_MP (@lem2315215 P n) (@lem2315214 n P h1)). Qed.
Lemma lem2315226 (n : nat) (P : int -> Prop) (h1 : term10 P) : (term15 P n) = (term27 n).
Proof. exact (MK_COMB (@lem2315223 n) (@lem2315225 n P h1)). Qed.
Lemma lem2315228 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem2315229 (n : nat) : (term27 n) = True.
Proof. exact (@lem2315228 (term1 n)). Qed.
Lemma lem2315230 (n : nat) (P : int -> Prop) (h1 : term10 P) : (term15 P n) = True.
Proof. exact (TRANS (@lem2315226 n P h1) (@lem2315229 n)). Qed.
Lemma lem2315231 (n : nat) (P : int -> Prop) (h1 : term10 P) : True = (term15 P n).
Proof. exact (SYM (@lem2315230 n P h1)). Qed.
Lemma lem2315232 (n : nat) (P : int -> Prop) (h1 : term10 P) : term15 P n.
Proof. exact (EQ_MP (@lem2315231 n P h1) (@lem0)). Qed.
Lemma lem2315240 : term28.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem2315241 (m : nat) : term29 m.
Proof. exact (@lem2315240 m). Qed.
Lemma lem2315242 (m : nat) : (term29 m) = ((term30 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem2315244 (m : nat) : term2 m.
Proof. exact (@lem2307222 m). Qed.
Lemma lem2315245 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem2315246 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem2315245 m) (@lem2315244 m)). Qed.
Lemma lem2315247 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem2315246 m n). Qed.
Lemma lem2315248 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem2315250 (x : int) : term31 x.
Proof. exact (@lem2301132 x). Qed.
Lemma lem2315251 (x : int) : (term31 x) = ((term32 x) = x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem2315253 (x : int) : term33 x.
Proof. exact (@lem2303280 x). Qed.
Lemma lem2315254 (x : int) : (term33 x) = (term34 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem2315255 (x : int) : term34 x.
Proof. exact (EQ_MP (@lem2315254 x) (@lem2315253 x)). Qed.
Lemma lem2315256 (x : int) (y : int) : term35 x y.
Proof. exact (@lem2315255 x y). Qed.
Lemma lem2315257 (x : int) (y : int) : (term35 x y) = ((term36 x y) = (term37 x y)).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem2315267 (x : int) (y : int) : (term36 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2315257 x y) (@lem2315256 x y)). Qed.
Lemma lem2315268 (n : nat) : (term38 n) = (term39 n).
Proof. exact (@lem2315267 term40 (int_of_num n)). Qed.
Lemma lem2315270 (x : int) : (term32 x) = x.
Proof. exact (EQ_MP (@lem2315251 x) (@lem2315250 x)). Qed.
Lemma lem2315271 (n : nat) : (term41 n) = (int_of_num n).
Proof. exact (@lem2315270 (int_of_num n)). Qed.
Lemma lem2315272 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem2315273 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem2315272) (@lem2315271 n)). Qed.
Lemma lem2315274 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem2315275 (n : nat) : (term39 n) = (term44 n).
Proof. exact (MK_COMB (@lem2315273 n) (@lem2315274)). Qed.
Lemma lem2315277 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2315248 m n) (@lem2315247 m n)). Qed.
Lemma lem2315278 (n : nat) : (term44 n) = (term30 n).
Proof. exact (@lem2315277 n (NUMERAL 0)). Qed.
Lemma lem2315280 (m : nat) : (term30 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem2315242 m) (@lem2315241 m)). Qed.
Lemma lem2315281 (n : nat) : (term30 n) = (n = (NUMERAL 0)).
Proof. exact (@lem2315280 n). Qed.
Lemma lem2315284 (n : nat) : (term44 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem2315278 n) (@lem2315281 n)). Qed.
Lemma lem2315285 (n : nat) : (term39 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem2315275 n) (@lem2315284 n)). Qed.
Lemma lem2315286 (n : nat) : (term38 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem2315268 n) (@lem2315285 n)). Qed.
Lemma lem2315287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2315288 (n : nat) : (term45 n) = (term46 n).
Proof. exact (MK_COMB (@lem2315287) (@lem2315286 n)). Qed.
Lemma lem2315289 (P : int -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (eq_refl (term47 P n)). Qed.
Lemma lem2315290 (P : int -> Prop) (n : nat) : (term21 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem2315288 n) (@lem2315289 P n)). Qed.
Lemma lem2315295 (P : int -> Prop) (n : nat) : (term48 P n) = (term21 P n).
Proof. exact (SYM (@lem2315290 P n)). Qed.
Lemma lem2315296 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2315297 (P : int -> Prop) : (term49 P) = (term49 P).
Proof. exact (eq_refl (term49 P)). Qed.
Lemma lem2315298 (P : int -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term50 P n) = (term51 P).
Proof. exact (MK_COMB (@lem2315297 P) (@lem2315296 n h1)). Qed.
Lemma lem2315299 (P : int -> Prop) : (term51 P) = (term52 P).
Proof. exact (eq_refl (term51 P)). Qed.
Lemma lem2315300 (P : int -> Prop) (n : nat) : (term53 P n) = (term53 P n).
Proof. exact (eq_refl (term53 P n)). Qed.
Lemma lem2315301 (n : nat) (P : int -> Prop) : ((term50 P n) = (term51 P)) = ((term50 P n) = (term52 P)).
Proof. exact (MK_COMB (@lem2315300 P n) (@lem2315299 P)). Qed.
Lemma lem2315302 (P : int -> Prop) (n : nat) : (term50 P n) = (term47 P n).
Proof. exact (eq_refl (term50 P n)). Qed.
Lemma lem2315303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315304 (P : int -> Prop) (n : nat) : (term53 P n) = (term54 P n).
Proof. exact (MK_COMB (@lem2315303) (@lem2315302 P n)). Qed.
Lemma lem2315305 (P : int -> Prop) : (term52 P) = (term52 P).
Proof. exact (eq_refl (term52 P)). Qed.
Lemma lem2315306 (n : nat) (P : int -> Prop) : ((term50 P n) = (term52 P)) = ((term47 P n) = (term52 P)).
Proof. exact (MK_COMB (@lem2315304 P n) (@lem2315305 P)). Qed.
Lemma lem2315307 (n : nat) (P : int -> Prop) : ((term50 P n) = (term51 P)) = ((term47 P n) = (term52 P)).
Proof. exact (TRANS (@lem2315301 n P) (@lem2315306 n P)). Qed.
Lemma lem2315308 (P : int -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term47 P n) = (term52 P).
Proof. exact (EQ_MP (@lem2315307 n P) (@lem2315298 P n h1)). Qed.
Lemma lem2315309 (P : int -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term52 P) = (term47 P n).
Proof. exact (SYM (@lem2315308 P n h1)). Qed.
Lemma lem2315310 (n : nat) (P : int -> Prop) (h1 : term10 P) : term22 P n.
Proof. exact (@lem2315156 P h1 n). Qed.
Lemma lem2315311 (P : int -> Prop) (n : nat) : (term22 P n) = (term23 P n).
Proof. exact (eq_refl (term22 P n)). Qed.
Lemma lem2315312 (n : nat) (P : int -> Prop) (h1 : term10 P) : term23 P n.
Proof. exact (EQ_MP (@lem2315311 P n) (@lem2315310 n P h1)). Qed.
Lemma lem2315313 (P : int -> Prop) (n : nat) : (term23 P n) = ((term23 P n) = True).
Proof. exact (@lem7 (term23 P n)). Qed.
Lemma lem2315316 : term55 = term40.
Proof. exact (EQ_MP (@lem2306330) (@lem1362041)). Qed.
Lemma lem2315317 (P : int -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem2315318 (P : int -> Prop) : (term52 P) = (term56 P).
Proof. exact (MK_COMB (@lem2315317 P) (@lem2315316)). Qed.
Lemma lem2315320 (n : nat) (P : int -> Prop) (h1 : term10 P) : (term23 P n) = True.
Proof. exact (EQ_MP (@lem2315313 P n) (@lem2315312 n P h1)). Qed.
Lemma lem2315321 (P : int -> Prop) (h1 : term10 P) : (term56 P) = True.
Proof. exact (@lem2315320 (NUMERAL 0) P h1). Qed.
Lemma lem2315322 (P : int -> Prop) (h1 : term10 P) : (term52 P) = True.
Proof. exact (TRANS (@lem2315318 P) (@lem2315321 P h1)). Qed.
Lemma lem2315323 (P : int -> Prop) (h1 : term10 P) : True = (term52 P).
Proof. exact (SYM (@lem2315322 P h1)). Qed.
Lemma lem2315324 (P : int -> Prop) (h1 : term10 P) : term52 P.
Proof. exact (EQ_MP (@lem2315323 P h1) (@lem0)). Qed.
Lemma lem2315325 (P : int -> Prop) (n : nat) (h1 : term10 P) (h2 : n = (NUMERAL 0)) : term47 P n.
Proof. exact (EQ_MP (@lem2315309 P n h2) (@lem2315324 P h1)). Qed.
Lemma lem2315326 (n : nat) (P : int -> Prop) (h1 : term10 P) : term48 P n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem2315325 P n h1 h0). Qed.
Lemma lem2315327 (n : nat) (P : int -> Prop) (h1 : term10 P) : term21 P n.
Proof. exact (EQ_MP (@lem2315295 P n) (@lem2315326 n P h1)). Qed.
Lemma lem2315328 (P : int -> Prop) (i : int) (n : nat) (h1 : term10 P) (h2 : i = (term19 n)) : term17 P i.
Proof. exact (EQ_MP (@lem2315185 P i n h2) (@lem2315327 n P h1)). Qed.
Lemma lem2315329 (P : int -> Prop) (i : int) (h1 : term10 P) (h2 : term9 i) : term17 P i.
Proof. exact (ex_elim (@lem2315155 i h2) (fun n : nat => fun h0 : term57 i n => @lem2315328 P i n h1 h0)). Qed.
Lemma lem2315330 (P : int -> Prop) (i : int) (n : nat) (h1 : term10 P) (h2 : i = (int_of_num n)) : term17 P i.
Proof. exact (EQ_MP (@lem2315171 P i n h2) (@lem2315232 n P h1)). Qed.
Lemma lem2315331 (P : int -> Prop) (i : int) (h1 : term10 P) (h2 : term8 i) : term17 P i.
Proof. exact (ex_elim (@lem2315154 i h2) (fun n : nat => fun h0 : term58 i n => @lem2315330 P i n h1 h0)). Qed.
Lemma lem2315332 (i : int) (P : int -> Prop) (h1 : term10 P) : term17 P i.
Proof. exact (or_elim (@lem2315153 i) (fun h0 : term8 i => @lem2315331 P i h1 h0) (fun h0 : term9 i => @lem2315329 P i h1 h0)). Qed.
Lemma lem2315333 (P : int -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem2315334 (i : int) (P : int -> Prop) (h1 : term11 P) : term13 P i.
Proof. exact (@lem2315333 P h1 i). Qed.
Lemma lem2315335 (P : int -> Prop) (i : int) : (term13 P i) = (term17 P i).
Proof. exact (eq_refl (term13 P i)). Qed.
Lemma lem2315336 (i : int) (P : int -> Prop) (h1 : term11 P) : term17 P i.
Proof. exact (EQ_MP (@lem2315335 P i) (@lem2315334 i P h1)). Qed.
Lemma lem2315337 (i : int) (h1 : term59 i) : term59 i.
Proof. exact (h1). Qed.
Lemma lem2315338 (P : int -> Prop) (i : int) (h1 : term11 P) (h2 : term59 i) : P i.
Proof. exact (@lem2315336 i P h1 (@lem2315337 i h2)). Qed.
Lemma lem2315339 (P : int -> Prop) (i : int) (h1 : term59 i) : term60 P i.
Proof. exact (fun h0 : term11 P => @lem2315338 P i h0 h1). Qed.
Lemma lem2315340 (P : int -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem2315341 (P : int -> Prop) (i : int) (h1 : term11 P) (h2 : term59 i) : P i.
Proof. exact (@lem2315339 P i h2 (@lem2315340 P h1)). Qed.
Lemma lem2315342 (i : int) (P : int -> Prop) (h1 : term11 P) : term17 P i.
Proof. exact (fun h0 : term59 i => @lem2315341 P i h1 h0). Qed.
Lemma lem2315343 (P : int -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (fun i : int => @lem2315342 i P h1). Qed.
Lemma lem2315344 (P : int -> Prop) : term61 P.
Proof. exact (fun h0 : term11 P => @lem2315343 P h0). Qed.
Lemma lem2315345 (P : int -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (@lem2315344 P (@lem2315157 P h1)). Qed.
Lemma lem2315346 (i : int) (P : int -> Prop) (h1 : term11 P) : term13 P i.
Proof. exact (@lem2315345 P h1 i). Qed.
Lemma lem2315347 (P : int -> Prop) (i : int) : (term13 P i) = (term17 P i).
Proof. exact (eq_refl (term13 P i)). Qed.
Lemma lem2315350 (i : int) (P : int -> Prop) (h1 : term11 P) : term17 P i.
Proof. exact (EQ_MP (@lem2315347 P i) (@lem2315346 i P h1)). Qed.
Lemma lem2315351 (n : nat) (P : int -> Prop) (h1 : term11 P) : term15 P n.
Proof. exact (@lem2315350 (int_of_num n) P h1). Qed.
Lemma lem2315353 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2315149 m n) (@lem2315148 m n)). Qed.
Lemma lem2315354 (n : nat) : (term24 n) = (term1 n).
Proof. exact (@lem2315353 (NUMERAL 0) n). Qed.
Lemma lem2315356 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem2315143 n) (@lem2315142 n)). Qed.
Lemma lem2315357 (n : nat) : (term24 n) = True.
Proof. exact (TRANS (@lem2315354 n) (@lem2315356 n)). Qed.
Lemma lem2315358 (n : nat) : True = (term24 n).
Proof. exact (SYM (@lem2315357 n)). Qed.
Lemma lem2315359 (n : nat) : term24 n.
Proof. exact (EQ_MP (@lem2315358 n) (@lem0)). Qed.
Lemma lem2315360 (n : nat) (P : int -> Prop) (h1 : term11 P) : term23 P n.
Proof. exact (@lem2315351 n P h1 (@lem2315359 n)). Qed.
Lemma lem2315365 (P : int -> Prop) (h1 : term11 P) : term10 P.
Proof. exact (fun n : nat => @lem2315360 n P h1). Qed.
Lemma lem2315370 (P : int -> Prop) (h1 : term10 P) : term11 P.
Proof. exact (fun i : int => @lem2315332 i P h1). Qed.
Lemma lem2315371 (P : int -> Prop) : term62 P.
Proof. exact (fun h0 : term11 P => @lem2315365 P h0). Qed.
Lemma lem2315372 (P : int -> Prop) : term63 P.
Proof. exact (fun h0 : term10 P => @lem2315370 P h0). Qed.
Lemma lem2315373 (P : int -> Prop) : term64 P.
Proof. exact (conj (@lem2315372 P) (@lem2315371 P)). Qed.
Lemma lem2315374 (P : int -> Prop) : (term64 P) = ((term10 P) = (term11 P)).
Proof. exact (@lem32 (term10 P) (term11 P)). Qed.
Lemma lem2315375 (P : int -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem2315374 P) (@lem2315373 P)). Qed.
Lemma lem2315380 : term65.
Proof. exact (fun P : int -> Prop => @lem2315375 P). Qed.
