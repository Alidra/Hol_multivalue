Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_SUB_term_abbrevs.
Require Import ADD_SUB2_spec.
Require Import LE_EXISTS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_POW_ADD_spec.
Require Import REAL_POW_NZ_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338712_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1340174_spec.
Require Import thm82_spec.
Lemma lem1598145 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1598146 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1598145 h1 x). Qed.
Lemma lem1598147 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1598148 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1598147 x) (@lem1598146 x h1)). Qed.
Lemma lem1598149 (x : real) (n : nat) (h1 : term0) : term3 x n.
Proof. exact (@lem1598148 x h1 n). Qed.
Lemma lem1598150 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1598151 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (EQ_MP (@lem1598150 x n) (@lem1598149 x n h1)). Qed.
Lemma lem1598152 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1598153 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1598151 x n h1 (@lem1598152 x h2)). Qed.
Lemma lem1598154 (n : nat) (x : real) (h1 : term5 x) : term7 x n.
Proof. exact (fun h0 : term0 => @lem1598153 n x h0 h1). Qed.
Lemma lem1598155 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1598156 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1598154 n x h2 (@lem1598155 h1)). Qed.
Lemma lem1598157 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (fun h0 : term5 x => @lem1598156 n x h1 h0). Qed.
Lemma lem1598158 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun n : nat => @lem1598157 x n h1). Qed.
Lemma lem1598159 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1598158 x h1). Qed.
Lemma lem1598160 : term8.
Proof. exact (fun h0 : term0 => @lem1598159 h0). Qed.
Lemma lem1598161 : term0.
Proof. exact (@lem1598160 (@lem1598144)). Qed.
Lemma lem1598162 (x : real) : term1 x.
Proof. exact (@lem1598161 x). Qed.
Lemma lem1598163 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1598164 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1598163 x) (@lem1598162 x)). Qed.
Lemma lem1598165 (x : real) (n : nat) : term3 x n.
Proof. exact (@lem1598164 x n). Qed.
Lemma lem1598166 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1598168 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem1598169 (x : real) (h1 : term9) : term10 x.
Proof. exact (@lem1598168 h1 x). Qed.
Lemma lem1598170 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1598171 (x : real) (h1 : term9) : term11 x.
Proof. exact (EQ_MP (@lem1598170 x) (@lem1598169 x h1)). Qed.
Lemma lem1598172 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1598173 (x : real) (h1 : term9) (h2 : term5 x) : (term12 x) = term13.
Proof. exact (@lem1598171 x h1 (@lem1598172 x h2)). Qed.
Lemma lem1598174 (x : real) (h1 : term5 x) : term14 x.
Proof. exact (fun h0 : term9 => @lem1598173 x h0 h1). Qed.
Lemma lem1598175 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem1598176 (x : real) (h1 : term9) (h2 : term5 x) : (term12 x) = term13.
Proof. exact (@lem1598174 x h2 (@lem1598175 h1)). Qed.
Lemma lem1598177 (x : real) (h1 : term9) : term11 x.
Proof. exact (fun h0 : term5 x => @lem1598176 x h1 h0). Qed.
Lemma lem1598178 (h1 : term9) : term9.
Proof. exact (fun x : real => @lem1598177 x h1). Qed.
Lemma lem1598179 : term15.
Proof. exact (fun h0 : term9 => @lem1598178 h0). Qed.
Lemma lem1598180 : term9.
Proof. exact (@lem1598179 (@lem1340174)). Qed.
Lemma lem1598181 (x : real) : term10 x.
Proof. exact (@lem1598180 x). Qed.
Lemma lem1598182 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1598184 (x : real) : term16 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1598185 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1598186 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1598185 x) (@lem1598184 x)). Qed.
Lemma lem1598187 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1598186 x y). Qed.
Lemma lem1598188 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1598189 (x : real) (y : real) : term19 x y.
Proof. exact (EQ_MP (@lem1598188 x y) (@lem1598187 x y)). Qed.
Lemma lem1598190 (x : real) (y : real) (z : real) : term20 x y z.
Proof. exact (@lem1598189 x y z). Qed.
Lemma lem1598191 (x : real) (y : real) (z : real) : (term20 x y z) = ((term21 x y z) = (term22 x y z)).
Proof. exact (eq_refl (term20 x y z)). Qed.
Lemma lem1598194 (x : real) (h1 : (term23 x) = x) : (term23 x) = x.
Proof. exact (h1). Qed.
Lemma lem1598195 (x : real) (h1 : (term23 x) = x) : x = (term23 x).
Proof. exact (SYM (@lem1598194 x h1)). Qed.
Lemma lem1598196 (x : real) (h1 : x = (term23 x)) : x = (term23 x).
Proof. exact (h1). Qed.
Lemma lem1598197 (x : real) (h1 : x = (term23 x)) : (term23 x) = x.
Proof. exact (SYM (@lem1598196 x h1)). Qed.
Lemma lem1598198 (x : real) : ((term23 x) = x) = (x = (term23 x)).
Proof. exact (prop_ext (fun h1 : (term23 x) = x => @lem1598195 x h1) (fun h1 : x = (term23 x) => @lem1598197 x h1)). Qed.
Lemma lem1598199 : term24 = term25.
Proof. exact (fun_ext (fun x : real => @lem1598198 x)). Qed.
Lemma lem1598200 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1598201 : term26 = term27.
Proof. exact (MK_COMB (@lem1598200) (@lem1598199)). Qed.
Lemma lem1598202 : term27.
Proof. exact (EQ_MP (@lem1598201) (@lem1338986)). Qed.
Lemma lem1598203 (x : real) : term28 x.
Proof. exact (@lem1598202 x). Qed.
Lemma lem1598204 (x : real) : (term28 x) = (x = (term23 x)).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1598206 (x : real) : term29 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1598207 (x : real) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1598208 (x : real) : term30 x.
Proof. exact (EQ_MP (@lem1598207 x) (@lem1598206 x)). Qed.
Lemma lem1598209 (x : real) (y : real) : term31 x y.
Proof. exact (@lem1598208 x y). Qed.
Lemma lem1598210 (y : real) (x : real) : (term31 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1598212 (x : real) : term32 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1598213 (x : real) : (term32 x) = (term33 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1598214 (x : real) : term33 x.
Proof. exact (EQ_MP (@lem1598213 x) (@lem1598212 x)). Qed.
Lemma lem1598215 (x : real) (y : real) : term34 x y.
Proof. exact (@lem1598214 x y). Qed.
Lemma lem1598216 (x : real) (y : real) : (term34 x y) = ((real_div x y) = (term35 x y)).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1598218 (x : real) : term36 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem1598219 (x : real) : (term36 x) = (term37 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1598220 (x : real) : term37 x.
Proof. exact (EQ_MP (@lem1598219 x) (@lem1598218 x)). Qed.
Lemma lem1598221 (x : real) (m : nat) : term38 x m.
Proof. exact (@lem1598220 x m). Qed.
Lemma lem1598222 (m : nat) (x : real) : (term38 x m) = (term39 m x).
Proof. exact (eq_refl (term38 x m)). Qed.
Lemma lem1598223 (m : nat) (x : real) : term39 m x.
Proof. exact (EQ_MP (@lem1598222 m x) (@lem1598221 x m)). Qed.
Lemma lem1598224 (m : nat) (x : real) (n : nat) : term40 m x n.
Proof. exact (@lem1598223 m x n). Qed.
Lemma lem1598225 (m : nat) (x : real) (n : nat) : (term40 m x n) = ((term41 x m n) = (term42 m x n)).
Proof. exact (eq_refl (term40 m x n)). Qed.
Lemma lem1598227 (m : nat) : term43 m.
Proof. exact (@lem135939 m). Qed.
Lemma lem1598228 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem1598229 (m : nat) : term44 m.
Proof. exact (EQ_MP (@lem1598228 m) (@lem1598227 m)). Qed.
Lemma lem1598230 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem1598229 m n). Qed.
Lemma lem1598231 (m : nat) (n : nat) : (term45 m n) = ((term46 n m) = n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem1598233 (m : nat) : term47 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1598234 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1598235 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem1598234 m) (@lem1598233 m)). Qed.
Lemma lem1598236 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1598235 m n). Qed.
Lemma lem1598237 (n : nat) (m : nat) : (term49 m n) = ((Peano.le m n) = (term50 n m)).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1598239 (x : real) (m : nat) (n : nat) (h1 : term51 x m n) : term51 x m n.
Proof. exact (h1). Qed.
Lemma lem1598240 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1598241 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1598245 (n : nat) (m : nat) : (Peano.le m n) = (term50 n m).
Proof. exact (EQ_MP (@lem1598237 n m) (@lem1598236 m n)). Qed.
Lemma lem1598252 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1598253 (n : nat) (m : nat) : (term52 m n) = (term53 n m).
Proof. exact (MK_COMB (@lem1598252) (@lem1598245 n m)). Qed.
Lemma lem1598256 (n : nat) (x : real) (m : nat) : ((term54 x n m) = (term55 n x m)) = ((term54 x n m) = (term55 n x m)).
Proof. exact (eq_refl ((term54 x n m) = (term55 n x m))). Qed.
Lemma lem1598257 (n : nat) (x : real) (m : nat) : (term56 n x m) = (term57 n x m).
Proof. exact (MK_COMB (@lem1598253 n m) (@lem1598256 n x m)). Qed.
Lemma lem1598260 (n : nat) (x : real) (m : nat) : (term57 n x m) = (term56 n x m).
Proof. exact (SYM (@lem1598257 n x m)). Qed.
Lemma lem1598261 (n : nat) (m : nat) (h1 : term50 n m) : term50 n m.
Proof. exact (h1). Qed.
Lemma lem1598262 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1598263 (x : real) (m : nat) : (term58 x m) = (term58 x m).
Proof. exact (eq_refl (term58 x m)). Qed.
Lemma lem1598264 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term59 x m n) = (term60 x m d).
Proof. exact (MK_COMB (@lem1598263 x m) (@lem1598262 n m d h1)). Qed.
Lemma lem1598265 (d : nat) (x : real) (m : nat) : (term60 x m d) = ((term61 x d m) = (term62 d x m)).
Proof. exact (eq_refl (term60 x m d)). Qed.
Lemma lem1598266 (x : real) (m : nat) (n : nat) : (term63 x m n) = (term63 x m n).
Proof. exact (eq_refl (term63 x m n)). Qed.
Lemma lem1598267 (n : nat) (d : nat) (x : real) (m : nat) : ((term59 x m n) = (term60 x m d)) = ((term59 x m n) = ((term61 x d m) = (term62 d x m))).
Proof. exact (MK_COMB (@lem1598266 x m n) (@lem1598265 d x m)). Qed.
Lemma lem1598268 (n : nat) (x : real) (m : nat) : (term59 x m n) = ((term54 x n m) = (term55 n x m)).
Proof. exact (eq_refl (term59 x m n)). Qed.
Lemma lem1598269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1598270 (n : nat) (x : real) (m : nat) : (term63 x m n) = (term64 n x m).
Proof. exact (MK_COMB (@lem1598269) (@lem1598268 n x m)). Qed.
Lemma lem1598271 (d : nat) (x : real) (m : nat) : ((term61 x d m) = (term62 d x m)) = ((term61 x d m) = (term62 d x m)).
Proof. exact (eq_refl ((term61 x d m) = (term62 d x m))). Qed.
Lemma lem1598272 (n : nat) (d : nat) (x : real) (m : nat) : ((term59 x m n) = ((term61 x d m) = (term62 d x m))) = (((term54 x n m) = (term55 n x m)) = ((term61 x d m) = (term62 d x m))).
Proof. exact (MK_COMB (@lem1598270 n x m) (@lem1598271 d x m)). Qed.
Lemma lem1598273 (n : nat) (d : nat) (x : real) (m : nat) : ((term59 x m n) = (term60 x m d)) = (((term54 x n m) = (term55 n x m)) = ((term61 x d m) = (term62 d x m))).
Proof. exact (TRANS (@lem1598267 n d x m) (@lem1598272 n d x m)). Qed.
Lemma lem1598274 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((term54 x n m) = (term55 n x m)) = ((term61 x d m) = (term62 d x m)).
Proof. exact (EQ_MP (@lem1598273 n d x m) (@lem1598264 x n m d h1)). Qed.
Lemma lem1598275 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((term61 x d m) = (term62 d x m)) = ((term54 x n m) = (term55 n x m)).
Proof. exact (SYM (@lem1598274 x n m d h1)). Qed.
Lemma lem1598279 (m : nat) (n : nat) : (term46 n m) = n.
Proof. exact (EQ_MP (@lem1598231 m n) (@lem1598230 m n)). Qed.
Lemma lem1598280 (m : nat) (d : nat) : (term46 d m) = d.
Proof. exact (@lem1598279 m d). Qed.
Lemma lem1598281 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1598282 (m : nat) (x : real) (d : nat) : (term61 x d m) = (real_pow x d).
Proof. exact (MK_COMB (@lem1598281 x) (@lem1598280 m d)). Qed.
Lemma lem1598283 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1598284 (m : nat) (x : real) (d : nat) : (term65 x d m) = (term66 x d).
Proof. exact (MK_COMB (@lem1598283) (@lem1598282 m x d)). Qed.
Lemma lem1598285 (d : nat) (x : real) (m : nat) : (term62 d x m) = (term62 d x m).
Proof. exact (eq_refl (term62 d x m)). Qed.
Lemma lem1598286 (d : nat) (x : real) (m : nat) : ((term61 x d m) = (term62 d x m)) = ((real_pow x d) = (term62 d x m)).
Proof. exact (MK_COMB (@lem1598284 m x d) (@lem1598285 d x m)). Qed.
Lemma lem1598289 (d : nat) (x : real) (m : nat) : ((real_pow x d) = (term62 d x m)) = ((term61 x d m) = (term62 d x m)).
Proof. exact (SYM (@lem1598286 d x m)). Qed.
Lemma lem1598293 (m : nat) (x : real) (n : nat) : (term41 x m n) = (term42 m x n).
Proof. exact (EQ_MP (@lem1598225 m x n) (@lem1598224 m x n)). Qed.
Lemma lem1598294 (m : nat) (x : real) (d : nat) : (term41 x m d) = (term42 m x d).
Proof. exact (@lem1598293 m x d). Qed.
Lemma lem1598295 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1598296 (m : nat) (x : real) (d : nat) : (term67 x m d) = (term68 m x d).
Proof. exact (MK_COMB (@lem1598295) (@lem1598294 m x d)). Qed.
Lemma lem1598297 (x : real) (m : nat) : (real_pow x m) = (real_pow x m).
Proof. exact (eq_refl (real_pow x m)). Qed.
Lemma lem1598298 (d : nat) (x : real) (m : nat) : (term62 d x m) = (term69 d x m).
Proof. exact (MK_COMB (@lem1598296 m x d) (@lem1598297 x m)). Qed.
Lemma lem1598299 (x : real) (d : nat) : (term66 x d) = (term66 x d).
Proof. exact (eq_refl (term66 x d)). Qed.
Lemma lem1598300 (d : nat) (x : real) (m : nat) : ((real_pow x d) = (term62 d x m)) = ((real_pow x d) = (term69 d x m)).
Proof. exact (MK_COMB (@lem1598299 x d) (@lem1598298 d x m)). Qed.
Lemma lem1598303 (d : nat) (x : real) (m : nat) : ((real_pow x d) = (term69 d x m)) = ((real_pow x d) = (term62 d x m)).
Proof. exact (SYM (@lem1598300 d x m)). Qed.
Lemma lem1598307 (x : real) (y : real) : (real_div x y) = (term35 x y).
Proof. exact (EQ_MP (@lem1598216 x y) (@lem1598215 x y)). Qed.
Lemma lem1598308 (d : nat) (x : real) (m : nat) : (term69 d x m) = (term70 d x m).
Proof. exact (@lem1598307 (term42 m x d) (real_pow x m)). Qed.
Lemma lem1598309 (x : real) (d : nat) : (term66 x d) = (term66 x d).
Proof. exact (eq_refl (term66 x d)). Qed.
Lemma lem1598310 (d : nat) (x : real) (m : nat) : ((real_pow x d) = (term69 d x m)) = ((real_pow x d) = (term70 d x m)).
Proof. exact (MK_COMB (@lem1598309 x d) (@lem1598308 d x m)). Qed.
Lemma lem1598313 (d : nat) (x : real) (m : nat) : ((real_pow x d) = (term70 d x m)) = ((real_pow x d) = (term69 d x m)).
Proof. exact (SYM (@lem1598310 d x m)). Qed.
Lemma lem1598317 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1598210 y x) (@lem1598209 x y)). Qed.
Lemma lem1598318 (m : nat) (x : real) (d : nat) : (term70 d x m) = (term71 m x d).
Proof. exact (@lem1598317 (term72 x m) (term42 m x d)). Qed.
Lemma lem1598319 (x : real) (d : nat) : (term66 x d) = (term66 x d).
Proof. exact (eq_refl (term66 x d)). Qed.
Lemma lem1598320 (m : nat) (x : real) (d : nat) : ((real_pow x d) = (term70 d x m)) = ((real_pow x d) = (term71 m x d)).
Proof. exact (MK_COMB (@lem1598319 x d) (@lem1598318 m x d)). Qed.
Lemma lem1598321 (d : nat) (x : real) (m : nat) : ((real_pow x d) = (term71 m x d)) = ((real_pow x d) = (term70 d x m)).
Proof. exact (SYM (@lem1598320 m x d)). Qed.
Lemma lem1598323 (x : real) : x = (term23 x).
Proof. exact (EQ_MP (@lem1598204 x) (@lem1598203 x)). Qed.
Lemma lem1598324 (x : real) (d : nat) : (real_pow x d) = (term73 x d).
Proof. exact (@lem1598323 (real_pow x d)). Qed.
Lemma lem1598325 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1598326 (x : real) (d : nat) : (term66 x d) = (term74 x d).
Proof. exact (MK_COMB (@lem1598325) (@lem1598324 x d)). Qed.
Lemma lem1598327 (m : nat) (x : real) (d : nat) : (term71 m x d) = (term71 m x d).
Proof. exact (eq_refl (term71 m x d)). Qed.
Lemma lem1598328 (m : nat) (x : real) (d : nat) : ((real_pow x d) = (term71 m x d)) = ((term73 x d) = (term71 m x d)).
Proof. exact (MK_COMB (@lem1598326 x d) (@lem1598327 m x d)). Qed.
Lemma lem1598329 (m : nat) (x : real) (d : nat) : ((term73 x d) = (term71 m x d)) = ((real_pow x d) = (term71 m x d)).
Proof. exact (SYM (@lem1598328 m x d)). Qed.
Lemma lem1598333 (x : real) (y : real) (z : real) : (term21 x y z) = (term22 x y z).
Proof. exact (EQ_MP (@lem1598191 x y z) (@lem1598190 x y z)). Qed.
Lemma lem1598334 (m : nat) (x : real) (d : nat) : (term71 m x d) = (term75 m x d).
Proof. exact (@lem1598333 (term72 x m) (real_pow x m) (real_pow x d)). Qed.
Lemma lem1598335 (x : real) (d : nat) : (term74 x d) = (term74 x d).
Proof. exact (eq_refl (term74 x d)). Qed.
Lemma lem1598336 (m : nat) (x : real) (d : nat) : ((term73 x d) = (term71 m x d)) = ((term73 x d) = (term75 m x d)).
Proof. exact (MK_COMB (@lem1598335 x d) (@lem1598334 m x d)). Qed.
Lemma lem1598339 (m : nat) (x : real) (d : nat) : ((term73 x d) = (term75 m x d)) = ((term73 x d) = (term71 m x d)).
Proof. exact (SYM (@lem1598336 m x d)). Qed.
Lemma lem1598340 (x : real) (d : nat) : (real_pow x d) = (real_pow x d).
Proof. exact (eq_refl (real_pow x d)). Qed.
Lemma lem1598341 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1598342 (x : real) (m : nat) (h1 : term13 = (term76 x m)) : term13 = (term76 x m).
Proof. exact (h1). Qed.
Lemma lem1598343 (x : real) (m : nat) (h1 : term13 = (term76 x m)) : (term76 x m) = term13.
Proof. exact (SYM (@lem1598342 x m h1)). Qed.
Lemma lem1598344 (x : real) (m : nat) (h1 : (term76 x m) = term13) : (term76 x m) = term13.
Proof. exact (h1). Qed.
Lemma lem1598345 (x : real) (m : nat) (h1 : (term76 x m) = term13) : term13 = (term76 x m).
Proof. exact (SYM (@lem1598344 x m h1)). Qed.
Lemma lem1598346 (x : real) (m : nat) : (term13 = (term76 x m)) = ((term76 x m) = term13).
Proof. exact (prop_ext (fun h1 : term13 = (term76 x m) => @lem1598343 x m h1) (fun h1 : (term76 x m) = term13 => @lem1598345 x m h1)). Qed.
Lemma lem1598347 (x : real) (m : nat) : ((term76 x m) = term13) = (term13 = (term76 x m)).
Proof. exact (SYM (@lem1598346 x m)). Qed.
Lemma lem1598349 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1598182 x) (@lem1598181 x)). Qed.
Lemma lem1598350 (x : real) (m : nat) : term77 x m.
Proof. exact (@lem1598349 (real_pow x m)). Qed.
Lemma lem1598352 (x : real) (n : nat) : term4 x n.
Proof. exact (EQ_MP (@lem1598166 x n) (@lem1598165 x n)). Qed.
Lemma lem1598353 (x : real) (m : nat) : term4 x m.
Proof. exact (@lem1598352 x m). Qed.
Lemma lem1598354 (x : real) : term78 x.
Proof. exact (@lem82 (x = term79)). Qed.
Lemma lem1598368 (x : real) (h1 : term5 x) : (x = term79) = False.
Proof. exact (@lem1598354 x (@lem1598241 x h1)). Qed.
Lemma lem1598369 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1598370 (x : real) (h1 : term5 x) : (term5 x) = (~ False).
Proof. exact (MK_COMB (@lem1598369) (@lem1598368 x h1)). Qed.
Lemma lem1598372 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1598373 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (TRANS (@lem1598370 x h1) (@lem1598372)). Qed.
Lemma lem1598374 (x : real) (h1 : term5 x) : True = (term5 x).
Proof. exact (SYM (@lem1598373 x h1)). Qed.
Lemma lem1598375 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (EQ_MP (@lem1598374 x h1) (@lem0)). Qed.
Lemma lem1598376 (m : nat) (x : real) (h1 : term5 x) : term6 x m.
Proof. exact (@lem1598353 x m (@lem1598375 x h1)). Qed.
Lemma lem1598377 (m : nat) (x : real) (h1 : term5 x) : (term76 x m) = term13.
Proof. exact (@lem1598350 x m (@lem1598376 m x h1)). Qed.
Lemma lem1598378 (m : nat) (x : real) (h1 : term5 x) : term13 = (term76 x m).
Proof. exact (EQ_MP (@lem1598347 x m) (@lem1598377 m x h1)). Qed.
Lemma lem1598379 (m : nat) (x : real) (h1 : term5 x) : term80 = (term81 x m).
Proof. exact (MK_COMB (@lem1598341) (@lem1598378 m x h1)). Qed.
Lemma lem1598380 (m : nat) (d : nat) (x : real) (h1 : term5 x) : (term73 x d) = (term75 m x d).
Proof. exact (MK_COMB (@lem1598379 m x h1) (@lem1598340 x d)). Qed.
Lemma lem1598381 (m : nat) (d : nat) (x : real) (h1 : term5 x) : (term73 x d) = (term71 m x d).
Proof. exact (EQ_MP (@lem1598339 m x d) (@lem1598380 m d x h1)). Qed.
Lemma lem1598382 (m : nat) (d : nat) (x : real) (h1 : term5 x) : (real_pow x d) = (term71 m x d).
Proof. exact (EQ_MP (@lem1598329 m x d) (@lem1598381 m d x h1)). Qed.
Lemma lem1598383 (d : nat) (m : nat) (x : real) (h1 : term5 x) : (real_pow x d) = (term70 d x m).
Proof. exact (EQ_MP (@lem1598321 d x m) (@lem1598382 m d x h1)). Qed.
Lemma lem1598384 (d : nat) (m : nat) (x : real) (h1 : term5 x) : (real_pow x d) = (term69 d x m).
Proof. exact (EQ_MP (@lem1598313 d x m) (@lem1598383 d m x h1)). Qed.
Lemma lem1598385 (d : nat) (m : nat) (x : real) (h1 : term5 x) : (real_pow x d) = (term62 d x m).
Proof. exact (EQ_MP (@lem1598303 d x m) (@lem1598384 d m x h1)). Qed.
Lemma lem1598386 (d : nat) (m : nat) (x : real) (h1 : term5 x) : (term61 x d m) = (term62 d x m).
Proof. exact (EQ_MP (@lem1598289 d x m) (@lem1598385 d m x h1)). Qed.
Lemma lem1598387 (x : real) (n : nat) (m : nat) (d : nat) (h1 : term5 x) (h2 : n = (Nat.add m d)) : (term54 x n m) = (term55 n x m).
Proof. exact (EQ_MP (@lem1598275 x n m d h2) (@lem1598386 d m x h1)). Qed.
Lemma lem1598388 (n : nat) (m : nat) (x : real) (h1 : term50 n m) (h2 : term5 x) : (term54 x n m) = (term55 n x m).
Proof. exact (ex_elim (@lem1598261 n m h1) (fun d : nat => fun h0 : term82 n m d => @lem1598387 x n m d h2 h0)). Qed.
Lemma lem1598389 (n : nat) (m : nat) (x : real) (h1 : term5 x) : term57 n x m.
Proof. exact (fun h0 : term50 n m => @lem1598388 n m x h0 h1). Qed.
Lemma lem1598390 (n : nat) (m : nat) (x : real) (h1 : term5 x) : term56 n x m.
Proof. exact (EQ_MP (@lem1598260 n x m) (@lem1598389 n m x h1)). Qed.
Lemma lem1598391 (x : real) (m : nat) (n : nat) (h1 : term51 x m n) : Peano.le m n.
Proof. exact (proj2 (@lem1598239 x m n h1)). Qed.
Lemma lem1598392 (x : real) (m : nat) (n : nat) (h1 : term51 x m n) : term5 x.
Proof. exact (proj1 (@lem1598239 x m n h1)). Qed.
Lemma lem1598393 (x : real) (m : nat) (n : nat) (h1 : term5 x) (h2 : Peano.le m n) : (term54 x n m) = (term55 n x m).
Proof. exact (@lem1598390 n m x h1 (@lem1598240 m n h2)). Qed.
Lemma lem1598394 (x : real) (m : nat) (n : nat) (h1 : term5 x) (h2 : Peano.le m n) : (term5 x) = ((term54 x n m) = (term55 n x m)).
Proof. exact (prop_ext (fun h3 : term5 x => @lem1598393 x m n h1 h2) (fun h3 : (term54 x n m) = (term55 n x m) => @lem1598241 x h1)). Qed.
Lemma lem1598395 (x : real) (m : nat) (n : nat) (h1 : term5 x) (h2 : Peano.le m n) : (term54 x n m) = (term55 n x m).
Proof. exact (EQ_MP (@lem1598394 x m n h1 h2) (@lem1598241 x h1)). Qed.
Lemma lem1598396 (x : real) (m : nat) (n : nat) (h1 : term5 x) (h2 : term51 x m n) : (Peano.le m n) = ((term54 x n m) = (term55 n x m)).
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem1598395 x m n h1 h3) (fun h3 : (term54 x n m) = (term55 n x m) => @lem1598391 x m n h2)). Qed.
Lemma lem1598397 (x : real) (m : nat) (n : nat) (h1 : term5 x) (h2 : term51 x m n) : (term54 x n m) = (term55 n x m).
Proof. exact (EQ_MP (@lem1598396 x m n h1 h2) (@lem1598391 x m n h2)). Qed.
Lemma lem1598398 (x : real) (m : nat) (n : nat) (h1 : term51 x m n) : (term5 x) = ((term54 x n m) = (term55 n x m)).
Proof. exact (prop_ext (fun h2 : term5 x => @lem1598397 x m n h2 h1) (fun h2 : (term54 x n m) = (term55 n x m) => @lem1598392 x m n h1)). Qed.
Lemma lem1598399 (x : real) (m : nat) (n : nat) (h1 : term51 x m n) : (term54 x n m) = (term55 n x m).
Proof. exact (EQ_MP (@lem1598398 x m n h1) (@lem1598392 x m n h1)). Qed.
Lemma lem1598400 (n : nat) (x : real) (m : nat) : term83 n x m.
Proof. exact (fun h0 : term51 x m n => @lem1598399 x m n h0). Qed.
Lemma lem1598405 (x : real) (m : nat) : term84 x m.
Proof. exact (fun n : nat => @lem1598400 n x m). Qed.
Lemma lem1598410 (x : real) : term85 x.
Proof. exact (fun m : nat => @lem1598405 x m). Qed.
Lemma lem1598415 : term86.
Proof. exact (fun x : real => @lem1598410 x). Qed.
