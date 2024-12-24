Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ARCH_SIMPLE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_COMPLETE_spec.
Require Import REAL_LE_SUB_LADD_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339697_spec.
Require Import thm1340339_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1367247_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483486_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1694100 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1694101 (P : real -> Prop) : ((term1 P) = (term2 P)) = (term3 P).
Proof. exact (@lem1694100 ((term1 P) = (term2 P))). Qed.
Lemma lem1694102 (P : real -> Prop) : (term3 P) = ((term1 P) = (term2 P)).
Proof. exact (SYM (@lem1694101 P)). Qed.
Lemma lem1694103 (P : real -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem1694106 (P : real -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem1694107 (P : real -> Prop) : term5 P.
Proof. exact (fun h0 : term3 P => @lem1694106 P h0). Qed.
Lemma lem1694108 (P : real -> Prop) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem1694109 (P : real -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem1694110 (P : real -> Prop) (h1 : term3 P) (h2 : term5 P) : term3 P.
Proof. exact (@lem1694108 P h2 (@lem1694109 P h1)). Qed.
Lemma lem1694111 (P : real -> Prop) (h1 : term3 P) : term6 P.
Proof. exact (fun h0 : term5 P => @lem1694110 P h1 h0). Qed.
Lemma lem1694112 (P : real -> Prop) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem1694113 (P : real -> Prop) (h1 : term3 P) (h2 : term5 P) : term3 P.
Proof. exact (@lem1694111 P h1 (@lem1694112 P h2)). Qed.
Lemma lem1694114 (P : real -> Prop) (h1 : term5 P) : term5 P.
Proof. exact (fun h0 : term3 P => @lem1694113 P h0 h1). Qed.
Lemma lem1694115 (P : real -> Prop) : term7 P.
Proof. exact (fun h0 : term5 P => @lem1694114 P h0). Qed.
Lemma lem1694118 (P : real -> Prop) : term5 P.
Proof. exact (@lem1694115 P (@lem1694107 P)). Qed.
Lemma lem1694124 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1694125 (P : real -> Prop) : (term3 P) = (term8 P).
Proof. exact (@lem1694124 (term4 P)). Qed.
Lemma lem1694127 (t : Prop) : (term9 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1694128 (P : real -> Prop) : (term8 P) = ((term1 P) = (term2 P)).
Proof. exact (@lem1694127 ((term1 P) = (term2 P))). Qed.
Lemma lem1694129 (P : real -> Prop) : (term3 P) = ((term1 P) = (term2 P)).
Proof. exact (TRANS (@lem1694125 P) (@lem1694128 P)). Qed.
Lemma lem1694144 : term10 = term11.
Proof. exact (fun_ext (fun P : real -> Prop => @lem1694129 P)). Qed.
Lemma lem1694145 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem1694154 : term12 = term13.
Proof. exact (MK_COMB (@lem1694145) (@lem1694144)). Qed.
Lemma lem1694155 (P : real -> Prop) (n : nat) : (term14 P n) = (term14 P n).
Proof. exact (eq_refl (term14 P n)). Qed.
Lemma lem1694156 (P : real -> Prop) : (term15 P) = (term15 P).
Proof. exact (fun_ext (fun n : nat => @lem1694155 P n)). Qed.
Lemma lem1694157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694158 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (MK_COMB (@lem1694157) (@lem1694156 P)). Qed.
Lemma lem1694159 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1694160 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem1694161 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun n : nat => @lem1694160 x n)). Qed.
Lemma lem1694162 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694163 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1694162) (@lem1694161 x)). Qed.
Lemma lem1694164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1694165 (x : real) : (term18 x) = (term18 x).
Proof. exact (MK_COMB (@lem1694164) (@lem1694163 x)). Qed.
Lemma lem1694166 (P : real -> Prop) (x : real) : (term19 P x) = (term19 P x).
Proof. exact (MK_COMB (@lem1694165 x) (@lem1694159 P x)). Qed.
Lemma lem1694167 (P : real -> Prop) : (term20 P) = (term20 P).
Proof. exact (fun_ext (fun x : real => @lem1694166 P x)). Qed.
Lemma lem1694168 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1694169 (P : real -> Prop) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem1694168) (@lem1694167 P)). Qed.
Lemma lem1694170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694171 (P : real -> Prop) : (term21 P) = (term21 P).
Proof. exact (MK_COMB (@lem1694170) (@lem1694169 P)). Qed.
Lemma lem1694172 (P : real -> Prop) : ((term1 P) = (term2 P)) = ((term1 P) = (term2 P)).
Proof. exact (MK_COMB (@lem1694171 P) (@lem1694158 P)). Qed.
Lemma lem1694173 : term11 = term11.
Proof. exact (fun_ext (fun P : real -> Prop => @lem1694172 P)). Qed.
Lemma lem1694174 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem1694175 : term13 = term13.
Proof. exact (MK_COMB (@lem1694174) (@lem1694173)). Qed.
Lemma lem1694204 : term12 = term13.
Proof. exact (TRANS (@lem1694154) (@lem1694175)). Qed.
Lemma lem1694205 : term13 = term12.
Proof. exact (SYM (@lem1694204)). Qed.
Lemma lem1694207 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1694208 (P : real -> Prop) : ((term1 P) = (term2 P)) = (term3 P).
Proof. exact (@lem1694207 ((term1 P) = (term2 P))). Qed.
Lemma lem1694209 (P : real -> Prop) : (term3 P) = ((term1 P) = (term2 P)).
Proof. exact (SYM (@lem1694208 P)). Qed.
Lemma lem1694210 (P : real -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem1694212 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem1694213 (P : nat -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1694214 (x : real) : (term24 x) = (term25 x).
Proof. exact (@lem1694213 (term16 x)). Qed.
Lemma lem1694215 (x : real) (n : nat) : (term26 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem1694216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1694218 (x : real) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (MK_COMB (@lem1694216) (@lem1694215 x n)). Qed.
Lemma lem1694219 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun n : nat => @lem1694218 x n)). Qed.
Lemma lem1694220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694221 (x : real) : (term25 x) = (term31 x).
Proof. exact (MK_COMB (@lem1694220) (@lem1694219 x)). Qed.
Lemma lem1694222 (x : real) : (term24 x) = (term31 x).
Proof. exact (TRANS (@lem1694214 x) (@lem1694221 x)). Qed.
Lemma lem1694223 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun n : nat => @lem1694212 x n)). Qed.
Lemma lem1694224 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694225 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1694224) (@lem1694223 x)). Qed.
Lemma lem1694226 (P : real -> Prop) (x : real) : (term32 P x) = (term32 P x).
Proof. exact (eq_refl (term32 P x)). Qed.
Lemma lem1694227 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1694228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694229 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1694228) (@lem1694225 x)). Qed.
Lemma lem1694230 (P : real -> Prop) (x : real) : (term34 P x) = (term34 P x).
Proof. exact (MK_COMB (@lem1694229 x) (@lem1694226 P x)). Qed.
Lemma lem1694231 (P : real -> Prop) (x : real) : (term35 P x) = (term34 P x).
Proof. exact (@lem17362 (term17 x) (P x)). Qed.
Lemma lem1694232 (P : real -> Prop) (x : real) : (term35 P x) = (term34 P x).
Proof. exact (TRANS (@lem1694231 P x) (@lem1694230 P x)). Qed.
Lemma lem1694233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694234 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1694233) (@lem1694222 x)). Qed.
Lemma lem1694235 (P : real -> Prop) (x : real) : (term38 P x) = (term39 P x).
Proof. exact (MK_COMB (@lem1694234 x) (@lem1694227 P x)). Qed.
Lemma lem1694236 (P : real -> Prop) (x : real) : (term19 P x) = (term38 P x).
Proof. exact (@lem17265 (term17 x) (P x)). Qed.
Lemma lem1694237 (P : real -> Prop) (x : real) : (term19 P x) = (term39 P x).
Proof. exact (TRANS (@lem1694236 P x) (@lem1694235 P x)). Qed.
Lemma lem1694238 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1694239 (P : real -> Prop) : (term42 P) = (term43 P).
Proof. exact (@lem1694238 (term20 P)). Qed.
Lemma lem1694240 (P : real -> Prop) (x : real) : (term44 P x) = (term19 P x).
Proof. exact (eq_refl (term44 P x)). Qed.
Lemma lem1694241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1694242 (P : real -> Prop) (x : real) : (term45 P x) = (term35 P x).
Proof. exact (MK_COMB (@lem1694241) (@lem1694240 P x)). Qed.
Lemma lem1694243 (P : real -> Prop) (x : real) : (term45 P x) = (term34 P x).
Proof. exact (TRANS (@lem1694242 P x) (@lem1694232 P x)). Qed.
Lemma lem1694244 (P : real -> Prop) : (term46 P) = (term47 P).
Proof. exact (fun_ext (fun x : real => @lem1694243 P x)). Qed.
Lemma lem1694245 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694246 (P : real -> Prop) : (term43 P) = (term48 P).
Proof. exact (MK_COMB (@lem1694245) (@lem1694244 P)). Qed.
Lemma lem1694247 (P : real -> Prop) : (term42 P) = (term48 P).
Proof. exact (TRANS (@lem1694239 P) (@lem1694246 P)). Qed.
Lemma lem1694248 (P : real -> Prop) : (term20 P) = (term49 P).
Proof. exact (fun_ext (fun x : real => @lem1694237 P x)). Qed.
Lemma lem1694249 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1694250 (P : real -> Prop) : (term1 P) = (term50 P).
Proof. exact (MK_COMB (@lem1694249) (@lem1694248 P)). Qed.
Lemma lem1694252 (P : real -> Prop) (n : nat) : (term14 P n) = (term14 P n).
Proof. exact (eq_refl (term14 P n)). Qed.
Lemma lem1694253 (P : nat -> Prop) : (term51 P) = (term52 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1694254 (P : real -> Prop) : (term53 P) = (term54 P).
Proof. exact (@lem1694253 (term15 P)). Qed.
Lemma lem1694255 (P : real -> Prop) (n : nat) : (term55 P n) = (term14 P n).
Proof. exact (eq_refl (term55 P n)). Qed.
Lemma lem1694256 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1694258 (P : real -> Prop) (n : nat) : (term56 P n) = (term57 P n).
Proof. exact (MK_COMB (@lem1694256) (@lem1694255 P n)). Qed.
Lemma lem1694259 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (fun_ext (fun n : nat => @lem1694258 P n)). Qed.
Lemma lem1694260 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694261 (P : real -> Prop) : (term54 P) = (term60 P).
Proof. exact (MK_COMB (@lem1694260) (@lem1694259 P)). Qed.
Lemma lem1694262 (P : real -> Prop) : (term53 P) = (term60 P).
Proof. exact (TRANS (@lem1694254 P) (@lem1694261 P)). Qed.
Lemma lem1694263 (P : real -> Prop) : (term15 P) = (term15 P).
Proof. exact (fun_ext (fun n : nat => @lem1694252 P n)). Qed.
Lemma lem1694264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694265 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (MK_COMB (@lem1694264) (@lem1694263 P)). Qed.
Lemma lem1694266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694267 (P : real -> Prop) : (term61 P) = (term62 P).
Proof. exact (MK_COMB (@lem1694266) (@lem1694247 P)). Qed.
Lemma lem1694268 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (MK_COMB (@lem1694267 P) (@lem1694265 P)). Qed.
Lemma lem1694269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694270 (P : real -> Prop) : (term65 P) = (term66 P).
Proof. exact (MK_COMB (@lem1694269) (@lem1694250 P)). Qed.
Lemma lem1694271 (P : real -> Prop) : (term67 P) = (term68 P).
Proof. exact (MK_COMB (@lem1694270 P) (@lem1694262 P)). Qed.
Lemma lem1694272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694273 (P : real -> Prop) : (term69 P) = (term70 P).
Proof. exact (MK_COMB (@lem1694272) (@lem1694271 P)). Qed.
Lemma lem1694274 (P : real -> Prop) : (term71 P) = (term72 P).
Proof. exact (MK_COMB (@lem1694273 P) (@lem1694268 P)). Qed.
Lemma lem1694275 (P : real -> Prop) : (term4 P) = (term71 P).
Proof. exact (@lem17646 (term1 P) (term2 P)). Qed.
Lemma lem1694276 (P : real -> Prop) : (term4 P) = (term72 P).
Proof. exact (TRANS (@lem1694275 P) (@lem1694274 P)). Qed.
Lemma lem1694375 {A : Type'} (P : Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1694376 (P : Prop) (Q : nat -> Prop) : (term75 P Q) = (term76 P Q).
Proof. exact (@lem1694375 nat P Q). Qed.
Lemma lem1694377 (P : real -> Prop) : (term77 P) = (term78 P).
Proof. exact (@lem1694376 (term50 P) (term59 P)). Qed.
Lemma lem1694378 (P : real -> Prop) (n : nat) : (term79 P n) = (term57 P n).
Proof. exact (eq_refl (term79 P n)). Qed.
Lemma lem1694379 (P : real -> Prop) : (term80 P) = (term59 P).
Proof. exact (fun_ext (fun n : nat => @lem1694378 P n)). Qed.
Lemma lem1694380 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694381 (P : real -> Prop) : (term81 P) = (term60 P).
Proof. exact (MK_COMB (@lem1694380) (@lem1694379 P)). Qed.
Lemma lem1694382 (P : real -> Prop) : (term66 P) = (term66 P).
Proof. exact (eq_refl (term66 P)). Qed.
Lemma lem1694383 (P : real -> Prop) : (term77 P) = (term68 P).
Proof. exact (MK_COMB (@lem1694382 P) (@lem1694381 P)). Qed.
Lemma lem1694384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694385 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (MK_COMB (@lem1694384) (@lem1694383 P)). Qed.
Lemma lem1694386 (P : real -> Prop) (n : nat) : (term79 P n) = (term57 P n).
Proof. exact (eq_refl (term79 P n)). Qed.
Lemma lem1694387 (P : real -> Prop) : (term66 P) = (term66 P).
Proof. exact (eq_refl (term66 P)). Qed.
Lemma lem1694388 (P : real -> Prop) (n : nat) : (term84 P n) = (term85 P n).
Proof. exact (MK_COMB (@lem1694387 P) (@lem1694386 P n)). Qed.
Lemma lem1694389 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (fun_ext (fun n : nat => @lem1694388 P n)). Qed.
Lemma lem1694390 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694391 (P : real -> Prop) : (term78 P) = (term88 P).
Proof. exact (MK_COMB (@lem1694390) (@lem1694389 P)). Qed.
Lemma lem1694392 (P : real -> Prop) : ((term77 P) = (term78 P)) = ((term68 P) = (term88 P)).
Proof. exact (MK_COMB (@lem1694385 P) (@lem1694391 P)). Qed.
Lemma lem1694393 (P : real -> Prop) : (term68 P) = (term88 P).
Proof. exact (EQ_MP (@lem1694392 P) (@lem1694377 P)). Qed.
Lemma lem1694394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694395 (P : real -> Prop) : (term70 P) = (term89 P).
Proof. exact (MK_COMB (@lem1694394) (@lem1694393 P)). Qed.
Lemma lem1694397 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1694398 (P : nat -> Prop) (Q : Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1694397 nat P Q). Qed.
Lemma lem1694399 (P : real -> Prop) (x : real) : (term94 P x) = (term95 P x).
Proof. exact (@lem1694398 (term16 x) (term32 P x)). Qed.
Lemma lem1694400 (x : real) (n : nat) : (term26 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem1694401 (x : real) : (term96 x) = (term16 x).
Proof. exact (fun_ext (fun n : nat => @lem1694400 x n)). Qed.
Lemma lem1694402 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694403 (x : real) : (term97 x) = (term17 x).
Proof. exact (MK_COMB (@lem1694402) (@lem1694401 x)). Qed.
Lemma lem1694404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694405 (x : real) : (term98 x) = (term33 x).
Proof. exact (MK_COMB (@lem1694404) (@lem1694403 x)). Qed.
Lemma lem1694406 (P : real -> Prop) (x : real) : (term32 P x) = (term32 P x).
Proof. exact (eq_refl (term32 P x)). Qed.
Lemma lem1694407 (P : real -> Prop) (x : real) : (term94 P x) = (term34 P x).
Proof. exact (MK_COMB (@lem1694405 x) (@lem1694406 P x)). Qed.
Lemma lem1694408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694409 (P : real -> Prop) (x : real) : (term99 P x) = (term100 P x).
Proof. exact (MK_COMB (@lem1694408) (@lem1694407 P x)). Qed.
Lemma lem1694410 (x : real) (n : nat) : (term26 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem1694411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694412 (x : real) (n : nat) : (term101 x n) = (term102 x n).
Proof. exact (MK_COMB (@lem1694411) (@lem1694410 x n)). Qed.
Lemma lem1694413 (P : real -> Prop) (x : real) : (term32 P x) = (term32 P x).
Proof. exact (eq_refl (term32 P x)). Qed.
Lemma lem1694414 (n : nat) (P : real -> Prop) (x : real) : (term103 n P x) = (term104 n P x).
Proof. exact (MK_COMB (@lem1694412 x n) (@lem1694413 P x)). Qed.
Lemma lem1694415 (P : real -> Prop) (x : real) : (term105 P x) = (term106 P x).
Proof. exact (fun_ext (fun n : nat => @lem1694414 n P x)). Qed.
Lemma lem1694416 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694417 (P : real -> Prop) (x : real) : (term95 P x) = (term107 P x).
Proof. exact (MK_COMB (@lem1694416) (@lem1694415 P x)). Qed.
Lemma lem1694418 (P : real -> Prop) (x : real) : ((term94 P x) = (term95 P x)) = ((term34 P x) = (term107 P x)).
Proof. exact (MK_COMB (@lem1694409 P x) (@lem1694417 P x)). Qed.
Lemma lem1694419 (P : real -> Prop) (x : real) : (term34 P x) = (term107 P x).
Proof. exact (EQ_MP (@lem1694418 P x) (@lem1694399 P x)). Qed.
Lemma lem1694420 (P : real -> Prop) : (term47 P) = (term108 P).
Proof. exact (fun_ext (fun x : real => @lem1694419 P x)). Qed.
Lemma lem1694421 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694422 (P : real -> Prop) : (term48 P) = (term109 P).
Proof. exact (MK_COMB (@lem1694421) (@lem1694420 P)). Qed.
Lemma lem1694423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694424 (P : real -> Prop) : (term62 P) = (term110 P).
Proof. exact (MK_COMB (@lem1694423) (@lem1694422 P)). Qed.
Lemma lem1694425 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (eq_refl (term2 P)). Qed.
Lemma lem1694426 (P : real -> Prop) : (term64 P) = (term111 P).
Proof. exact (MK_COMB (@lem1694424 P) (@lem1694425 P)). Qed.
Lemma lem1694428 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1694429 (P : real -> Prop) (Q : Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem1694428 real P Q). Qed.
Lemma lem1694430 (P : real -> Prop) : (term114 P) = (term115 P).
Proof. exact (@lem1694429 (term108 P) (term2 P)). Qed.
Lemma lem1694431 (P : real -> Prop) (x : real) : (term116 P x) = (term107 P x).
Proof. exact (eq_refl (term116 P x)). Qed.
Lemma lem1694432 (P : real -> Prop) : (term117 P) = (term108 P).
Proof. exact (fun_ext (fun x : real => @lem1694431 P x)). Qed.
Lemma lem1694433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694434 (P : real -> Prop) : (term118 P) = (term109 P).
Proof. exact (MK_COMB (@lem1694433) (@lem1694432 P)). Qed.
Lemma lem1694435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694436 (P : real -> Prop) : (term119 P) = (term110 P).
Proof. exact (MK_COMB (@lem1694435) (@lem1694434 P)). Qed.
Lemma lem1694437 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (eq_refl (term2 P)). Qed.
Lemma lem1694438 (P : real -> Prop) : (term114 P) = (term111 P).
Proof. exact (MK_COMB (@lem1694436 P) (@lem1694437 P)). Qed.
Lemma lem1694439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694440 (P : real -> Prop) : (term120 P) = (term121 P).
Proof. exact (MK_COMB (@lem1694439) (@lem1694438 P)). Qed.
Lemma lem1694441 (P : real -> Prop) (x : real) : (term116 P x) = (term107 P x).
Proof. exact (eq_refl (term116 P x)). Qed.
Lemma lem1694442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694443 (P : real -> Prop) (x : real) : (term122 P x) = (term123 P x).
Proof. exact (MK_COMB (@lem1694442) (@lem1694441 P x)). Qed.
Lemma lem1694444 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (eq_refl (term2 P)). Qed.
Lemma lem1694445 (x : real) (P : real -> Prop) : (term124 x P) = (term125 x P).
Proof. exact (MK_COMB (@lem1694443 P x) (@lem1694444 P)). Qed.
Lemma lem1694446 (P : real -> Prop) : (term126 P) = (term127 P).
Proof. exact (fun_ext (fun x : real => @lem1694445 x P)). Qed.
Lemma lem1694447 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694448 (P : real -> Prop) : (term115 P) = (term128 P).
Proof. exact (MK_COMB (@lem1694447) (@lem1694446 P)). Qed.
Lemma lem1694449 (P : real -> Prop) : ((term114 P) = (term115 P)) = ((term111 P) = (term128 P)).
Proof. exact (MK_COMB (@lem1694440 P) (@lem1694448 P)). Qed.
Lemma lem1694450 (P : real -> Prop) : (term111 P) = (term128 P).
Proof. exact (EQ_MP (@lem1694449 P) (@lem1694430 P)). Qed.
Lemma lem1694452 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1694453 (P : nat -> Prop) (Q : Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1694452 nat P Q). Qed.
Lemma lem1694454 (x : real) (P : real -> Prop) : (term129 x P) = (term130 x P).
Proof. exact (@lem1694453 (term106 P x) (term2 P)). Qed.
Lemma lem1694455 (n : nat) (P : real -> Prop) (x : real) : (term131 P x n) = (term104 n P x).
Proof. exact (eq_refl (term131 P x n)). Qed.
Lemma lem1694456 (P : real -> Prop) (x : real) : (term132 P x) = (term106 P x).
Proof. exact (fun_ext (fun n : nat => @lem1694455 n P x)). Qed.
Lemma lem1694457 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694458 (P : real -> Prop) (x : real) : (term133 P x) = (term107 P x).
Proof. exact (MK_COMB (@lem1694457) (@lem1694456 P x)). Qed.
Lemma lem1694459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694460 (P : real -> Prop) (x : real) : (term134 P x) = (term123 P x).
Proof. exact (MK_COMB (@lem1694459) (@lem1694458 P x)). Qed.
Lemma lem1694461 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (eq_refl (term2 P)). Qed.
Lemma lem1694462 (x : real) (P : real -> Prop) : (term129 x P) = (term125 x P).
Proof. exact (MK_COMB (@lem1694460 P x) (@lem1694461 P)). Qed.
Lemma lem1694463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694464 (x : real) (P : real -> Prop) : (term135 x P) = (term136 x P).
Proof. exact (MK_COMB (@lem1694463) (@lem1694462 x P)). Qed.
Lemma lem1694465 (n : nat) (P : real -> Prop) (x : real) : (term131 P x n) = (term104 n P x).
Proof. exact (eq_refl (term131 P x n)). Qed.
Lemma lem1694466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694467 (n : nat) (P : real -> Prop) (x : real) : (term137 P x n) = (term138 n P x).
Proof. exact (MK_COMB (@lem1694466) (@lem1694465 n P x)). Qed.
Lemma lem1694468 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (eq_refl (term2 P)). Qed.
Lemma lem1694469 (n : nat) (x : real) (P : real -> Prop) : (term139 x n P) = (term140 n x P).
Proof. exact (MK_COMB (@lem1694467 n P x) (@lem1694468 P)). Qed.
Lemma lem1694470 (x : real) (P : real -> Prop) : (term141 x P) = (term142 x P).
Proof. exact (fun_ext (fun n : nat => @lem1694469 n x P)). Qed.
Lemma lem1694471 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694472 (x : real) (P : real -> Prop) : (term130 x P) = (term143 x P).
Proof. exact (MK_COMB (@lem1694471) (@lem1694470 x P)). Qed.
Lemma lem1694473 (x : real) (P : real -> Prop) : ((term129 x P) = (term130 x P)) = ((term125 x P) = (term143 x P)).
Proof. exact (MK_COMB (@lem1694464 x P) (@lem1694472 x P)). Qed.
Lemma lem1694474 (x : real) (P : real -> Prop) : (term125 x P) = (term143 x P).
Proof. exact (EQ_MP (@lem1694473 x P) (@lem1694454 x P)). Qed.
Lemma lem1694475 (P : real -> Prop) : (term127 P) = (term144 P).
Proof. exact (fun_ext (fun x : real => @lem1694474 x P)). Qed.
Lemma lem1694476 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694477 (P : real -> Prop) : (term128 P) = (term145 P).
Proof. exact (MK_COMB (@lem1694476) (@lem1694475 P)). Qed.
Lemma lem1694478 (P : real -> Prop) : (term111 P) = (term145 P).
Proof. exact (TRANS (@lem1694450 P) (@lem1694477 P)). Qed.
Lemma lem1694479 (P : real -> Prop) : (term64 P) = (term145 P).
Proof. exact (TRANS (@lem1694426 P) (@lem1694478 P)). Qed.
Lemma lem1694480 (P : real -> Prop) : (term72 P) = (term146 P).
Proof. exact (MK_COMB (@lem1694395 P) (@lem1694479 P)). Qed.
Lemma lem1694484 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1694485 (P : nat -> Prop) (Q : Prop) : (term149 P Q) = (term150 P Q).
Proof. exact (@lem1694484 nat P Q). Qed.
Lemma lem1694486 (P : real -> Prop) : (term151 P) = (term152 P).
Proof. exact (@lem1694485 (term87 P) (term145 P)). Qed.
Lemma lem1694487 (P : real -> Prop) (n : nat) : (term153 P n) = (term85 P n).
Proof. exact (eq_refl (term153 P n)). Qed.
Lemma lem1694488 (P : real -> Prop) : (term154 P) = (term87 P).
Proof. exact (fun_ext (fun n : nat => @lem1694487 P n)). Qed.
Lemma lem1694489 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694490 (P : real -> Prop) : (term155 P) = (term88 P).
Proof. exact (MK_COMB (@lem1694489) (@lem1694488 P)). Qed.
Lemma lem1694491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694492 (P : real -> Prop) : (term156 P) = (term89 P).
Proof. exact (MK_COMB (@lem1694491) (@lem1694490 P)). Qed.
Lemma lem1694493 (P : real -> Prop) : (term145 P) = (term145 P).
Proof. exact (eq_refl (term145 P)). Qed.
Lemma lem1694494 (P : real -> Prop) : (term151 P) = (term146 P).
Proof. exact (MK_COMB (@lem1694492 P) (@lem1694493 P)). Qed.
Lemma lem1694495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694496 (P : real -> Prop) : (term157 P) = (term158 P).
Proof. exact (MK_COMB (@lem1694495) (@lem1694494 P)). Qed.
Lemma lem1694497 (P : real -> Prop) (n : nat) : (term153 P n) = (term85 P n).
Proof. exact (eq_refl (term153 P n)). Qed.
Lemma lem1694498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694499 (P : real -> Prop) (n : nat) : (term159 P n) = (term160 P n).
Proof. exact (MK_COMB (@lem1694498) (@lem1694497 P n)). Qed.
Lemma lem1694500 (P : real -> Prop) : (term145 P) = (term145 P).
Proof. exact (eq_refl (term145 P)). Qed.
Lemma lem1694501 (n : nat) (P : real -> Prop) : (term161 n P) = (term162 n P).
Proof. exact (MK_COMB (@lem1694499 P n) (@lem1694500 P)). Qed.
Lemma lem1694502 (P : real -> Prop) : (term163 P) = (term164 P).
Proof. exact (fun_ext (fun n : nat => @lem1694501 n P)). Qed.
Lemma lem1694503 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694504 (P : real -> Prop) : (term152 P) = (term165 P).
Proof. exact (MK_COMB (@lem1694503) (@lem1694502 P)). Qed.
Lemma lem1694505 (P : real -> Prop) : ((term151 P) = (term152 P)) = ((term146 P) = (term165 P)).
Proof. exact (MK_COMB (@lem1694496 P) (@lem1694504 P)). Qed.
Lemma lem1694506 (P : real -> Prop) : (term146 P) = (term165 P).
Proof. exact (EQ_MP (@lem1694505 P) (@lem1694486 P)). Qed.
Lemma lem1694508 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1694509 (P : Prop) (Q : real -> Prop) : (term168 P Q) = (term169 P Q).
Proof. exact (@lem1694508 real P Q). Qed.
Lemma lem1694510 (n : nat) (P : real -> Prop) : (term170 n P) = (term171 n P).
Proof. exact (@lem1694509 (term85 P n) (term144 P)). Qed.
Lemma lem1694511 (x : real) (P : real -> Prop) : (term172 P x) = (term143 x P).
Proof. exact (eq_refl (term172 P x)). Qed.
Lemma lem1694512 (P : real -> Prop) : (term173 P) = (term144 P).
Proof. exact (fun_ext (fun x : real => @lem1694511 x P)). Qed.
Lemma lem1694513 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694514 (P : real -> Prop) : (term174 P) = (term145 P).
Proof. exact (MK_COMB (@lem1694513) (@lem1694512 P)). Qed.
Lemma lem1694515 (P : real -> Prop) (n : nat) : (term160 P n) = (term160 P n).
Proof. exact (eq_refl (term160 P n)). Qed.
Lemma lem1694516 (n : nat) (P : real -> Prop) : (term170 n P) = (term162 n P).
Proof. exact (MK_COMB (@lem1694515 P n) (@lem1694514 P)). Qed.
Lemma lem1694517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694518 (n : nat) (P : real -> Prop) : (term175 n P) = (term176 n P).
Proof. exact (MK_COMB (@lem1694517) (@lem1694516 n P)). Qed.
Lemma lem1694519 (x : real) (P : real -> Prop) : (term172 P x) = (term143 x P).
Proof. exact (eq_refl (term172 P x)). Qed.
Lemma lem1694520 (P : real -> Prop) (n : nat) : (term160 P n) = (term160 P n).
Proof. exact (eq_refl (term160 P n)). Qed.
Lemma lem1694521 (n : nat) (x : real) (P : real -> Prop) : (term177 n P x) = (term178 n x P).
Proof. exact (MK_COMB (@lem1694520 P n) (@lem1694519 x P)). Qed.
Lemma lem1694522 (n : nat) (P : real -> Prop) : (term179 n P) = (term180 n P).
Proof. exact (fun_ext (fun x : real => @lem1694521 n x P)). Qed.
Lemma lem1694523 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694524 (n : nat) (P : real -> Prop) : (term171 n P) = (term181 n P).
Proof. exact (MK_COMB (@lem1694523) (@lem1694522 n P)). Qed.
Lemma lem1694525 (n : nat) (P : real -> Prop) : ((term170 n P) = (term171 n P)) = ((term162 n P) = (term181 n P)).
Proof. exact (MK_COMB (@lem1694518 n P) (@lem1694524 n P)). Qed.
Lemma lem1694526 (n : nat) (P : real -> Prop) : (term162 n P) = (term181 n P).
Proof. exact (EQ_MP (@lem1694525 n P) (@lem1694510 n P)). Qed.
Lemma lem1694528 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1694529 (P : Prop) (Q : nat -> Prop) : (term182 P Q) = (term183 P Q).
Proof. exact (@lem1694528 nat P Q). Qed.
Lemma lem1694530 (n : nat) (x : real) (P : real -> Prop) : (term184 n x P) = (term185 n x P).
Proof. exact (@lem1694529 (term85 P n) (term142 x P)). Qed.
Lemma lem1694531 (n : nat) (x : real) (P : real -> Prop) : (term186 x P n) = (term140 n x P).
Proof. exact (eq_refl (term186 x P n)). Qed.
Lemma lem1694532 (x : real) (P : real -> Prop) : (term187 x P) = (term142 x P).
Proof. exact (fun_ext (fun n : nat => @lem1694531 n x P)). Qed.
Lemma lem1694533 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694534 (x : real) (P : real -> Prop) : (term188 x P) = (term143 x P).
Proof. exact (MK_COMB (@lem1694533) (@lem1694532 x P)). Qed.
Lemma lem1694535 (P : real -> Prop) (n : nat) : (term160 P n) = (term160 P n).
Proof. exact (eq_refl (term160 P n)). Qed.
Lemma lem1694536 (n : nat) (x : real) (P : real -> Prop) : (term184 n x P) = (term178 n x P).
Proof. exact (MK_COMB (@lem1694535 P n) (@lem1694534 x P)). Qed.
Lemma lem1694537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694538 (n : nat) (x : real) (P : real -> Prop) : (term189 n x P) = (term190 n x P).
Proof. exact (MK_COMB (@lem1694537) (@lem1694536 n x P)). Qed.
Lemma lem1694539 (n' : nat) (x : real) (P : real -> Prop) : (term186 x P n') = (term140 n' x P).
Proof. exact (eq_refl (term186 x P n')). Qed.
Lemma lem1694540 (P : real -> Prop) (n : nat) : (term160 P n) = (term160 P n).
Proof. exact (eq_refl (term160 P n)). Qed.
Lemma lem1694541 (n : nat) (n' : nat) (x : real) (P : real -> Prop) : (term191 n x P n') = (term192 n n' x P).
Proof. exact (MK_COMB (@lem1694540 P n) (@lem1694539 n' x P)). Qed.
Lemma lem1694542 (n : nat) (x : real) (P : real -> Prop) : (term193 n x P) = (term194 n x P).
Proof. exact (fun_ext (fun n' : nat => @lem1694541 n n' x P)). Qed.
Lemma lem1694543 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694544 (n : nat) (x : real) (P : real -> Prop) : (term185 n x P) = (term195 n x P).
Proof. exact (MK_COMB (@lem1694543) (@lem1694542 n x P)). Qed.
Lemma lem1694545 (n : nat) (x : real) (P : real -> Prop) : ((term184 n x P) = (term185 n x P)) = ((term178 n x P) = (term195 n x P)).
Proof. exact (MK_COMB (@lem1694538 n x P) (@lem1694544 n x P)). Qed.
Lemma lem1694546 (n : nat) (x : real) (P : real -> Prop) : (term178 n x P) = (term195 n x P).
Proof. exact (EQ_MP (@lem1694545 n x P) (@lem1694530 n x P)). Qed.
Lemma lem1694547 (n : nat) (P : real -> Prop) : (term180 n P) = (term196 n P).
Proof. exact (fun_ext (fun x : real => @lem1694546 n x P)). Qed.
Lemma lem1694548 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1694549 (n : nat) (P : real -> Prop) : (term181 n P) = (term197 n P).
Proof. exact (MK_COMB (@lem1694548) (@lem1694547 n P)). Qed.
Lemma lem1694550 (n : nat) (P : real -> Prop) : (term162 n P) = (term197 n P).
Proof. exact (TRANS (@lem1694526 n P) (@lem1694549 n P)). Qed.
Lemma lem1694551 (P : real -> Prop) : (term164 P) = (term198 P).
Proof. exact (fun_ext (fun n : nat => @lem1694550 n P)). Qed.
Lemma lem1694552 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1694553 (P : real -> Prop) : (term165 P) = (term199 P).
Proof. exact (MK_COMB (@lem1694552) (@lem1694551 P)). Qed.
Lemma lem1694554 (P : real -> Prop) : (term146 P) = (term199 P).
Proof. exact (TRANS (@lem1694506 P) (@lem1694553 P)). Qed.
Lemma lem1694556 (P : real -> Prop) : (term72 P) = (term199 P).
Proof. exact (TRANS (@lem1694480 P) (@lem1694554 P)). Qed.
Lemma lem1694557 (P : real -> Prop) : (term4 P) = (term199 P).
Proof. exact (TRANS (@lem1694276 P) (@lem1694556 P)). Qed.
Lemma lem1694558 (P : real -> Prop) (h1 : term4 P) : term199 P.
Proof. exact (EQ_MP (@lem1694557 P) (@lem1694210 P h1)). Qed.
Lemma lem1694559 (n : nat) (P : real -> Prop) (h1 : term197 n P) : term197 n P.
Proof. exact (h1). Qed.
Lemma lem1694560 (n : nat) (x : real) (P : real -> Prop) (h1 : term195 n x P) : term195 n x P.
Proof. exact (h1). Qed.
Lemma lem1694561 (n : nat) (n' : nat) (x : real) (P : real -> Prop) (h1 : term192 n n' x P) : term192 n n' x P.
Proof. exact (h1). Qed.
Lemma lem1694566 (P : real -> Prop) (n : nat) : (term14 P n) = (term14 P n).
Proof. exact (eq_refl (term14 P n)). Qed.
Lemma lem1694567 (P : real -> Prop) : (term15 P) = (term15 P).
Proof. exact (fun_ext (fun n : nat => @lem1694566 P n)). Qed.
Lemma lem1694568 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694569 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (MK_COMB (@lem1694568) (@lem1694567 P)). Qed.
Lemma lem1694586 (n' : nat) (P : real -> Prop) (x : real) : (term138 n' P x) = (term138 n' P x).
Proof. exact (eq_refl (term138 n' P x)). Qed.
Lemma lem1694587 (n' : nat) (x : real) (P : real -> Prop) : (term140 n' x P) = (term140 n' x P).
Proof. exact (MK_COMB (@lem1694586 n' P x) (@lem1694569 P)). Qed.
Lemma lem1694594 (P : real -> Prop) (n : nat) : (term57 P n) = (term57 P n).
Proof. exact (eq_refl (term57 P n)). Qed.
Lemma lem1694597 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1694606 (x : real) (n : nat) : (term28 x n) = (term28 x n).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem1694607 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun n : nat => @lem1694606 x n)). Qed.
Lemma lem1694608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694609 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1694608) (@lem1694607 x)). Qed.
Lemma lem1694610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694611 (x : real) : (term37 x) = (term37 x).
Proof. exact (MK_COMB (@lem1694610) (@lem1694609 x)). Qed.
Lemma lem1694612 (P : real -> Prop) (x : real) : (term39 P x) = (term39 P x).
Proof. exact (MK_COMB (@lem1694611 x) (@lem1694597 P x)). Qed.
Lemma lem1694613 (P : real -> Prop) : (term49 P) = (term49 P).
Proof. exact (fun_ext (fun x : real => @lem1694612 P x)). Qed.
Lemma lem1694614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1694615 (P : real -> Prop) : (term50 P) = (term50 P).
Proof. exact (MK_COMB (@lem1694614) (@lem1694613 P)). Qed.
Lemma lem1694616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694617 (P : real -> Prop) : (term66 P) = (term66 P).
Proof. exact (MK_COMB (@lem1694616) (@lem1694615 P)). Qed.
Lemma lem1694618 (P : real -> Prop) (n : nat) : (term85 P n) = (term85 P n).
Proof. exact (MK_COMB (@lem1694617 P) (@lem1694594 P n)). Qed.
Lemma lem1694619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694620 (P : real -> Prop) (n : nat) : (term160 P n) = (term160 P n).
Proof. exact (MK_COMB (@lem1694619) (@lem1694618 P n)). Qed.
Lemma lem1694621 (n : nat) (n' : nat) (x : real) (P : real -> Prop) : (term192 n n' x P) = (term192 n n' x P).
Proof. exact (MK_COMB (@lem1694620 P n) (@lem1694587 n' x P)). Qed.
Lemma lem1694622 (n : nat) (n' : nat) (x : real) (P : real -> Prop) (h1 : term192 n n' x P) : term192 n n' x P.
Proof. exact (EQ_MP (@lem1694621 n n' x P) (@lem1694561 n n' x P h1)). Qed.
Lemma lem1694623 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term85 P n.
Proof. exact (h1). Qed.
Lemma lem1694624 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term140 n' x P.
Proof. exact (h1). Qed.
Lemma lem1694626 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term50 P.
Proof. exact (proj1 (@lem1694623 P n h1)). Qed.
Lemma lem1694627 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term2 P.
Proof. exact (proj2 (@lem1694624 n' x P h1)). Qed.
Lemma lem1694628 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term104 n' P x.
Proof. exact (proj1 (@lem1694624 n' x P h1)). Qed.
Lemma lem1694632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term200 A P Q) = (term201 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1694633 (P : nat -> Prop) (Q : Prop) : (term202 P Q) = (term203 P Q).
Proof. exact (@lem1694632 nat P Q). Qed.
Lemma lem1694634 (P : real -> Prop) (x : real) : (term204 P x) = (term205 P x).
Proof. exact (@lem1694633 (term30 x) (P x)). Qed.
Lemma lem1694635 (x : real) (n : nat) : (term206 x n) = (term28 x n).
Proof. exact (eq_refl (term206 x n)). Qed.
Lemma lem1694636 (x : real) : (term207 x) = (term30 x).
Proof. exact (fun_ext (fun n : nat => @lem1694635 x n)). Qed.
Lemma lem1694637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694638 (x : real) : (term208 x) = (term31 x).
Proof. exact (MK_COMB (@lem1694637) (@lem1694636 x)). Qed.
Lemma lem1694639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694640 (x : real) : (term209 x) = (term37 x).
Proof. exact (MK_COMB (@lem1694639) (@lem1694638 x)). Qed.
Lemma lem1694641 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1694642 (P : real -> Prop) (x : real) : (term204 P x) = (term39 P x).
Proof. exact (MK_COMB (@lem1694640 x) (@lem1694641 P x)). Qed.
Lemma lem1694643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694644 (P : real -> Prop) (x : real) : (term210 P x) = (term211 P x).
Proof. exact (MK_COMB (@lem1694643) (@lem1694642 P x)). Qed.
Lemma lem1694645 (x : real) (n : nat) : (term206 x n) = (term28 x n).
Proof. exact (eq_refl (term206 x n)). Qed.
Lemma lem1694646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1694647 (x : real) (n : nat) : (term212 x n) = (term213 x n).
Proof. exact (MK_COMB (@lem1694646) (@lem1694645 x n)). Qed.
Lemma lem1694648 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1694649 (n : nat) (P : real -> Prop) (x : real) : (term214 n P x) = (term215 n P x).
Proof. exact (MK_COMB (@lem1694647 x n) (@lem1694648 P x)). Qed.
Lemma lem1694650 (P : real -> Prop) (x : real) : (term216 P x) = (term217 P x).
Proof. exact (fun_ext (fun n : nat => @lem1694649 n P x)). Qed.
Lemma lem1694651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694652 (P : real -> Prop) (x : real) : (term205 P x) = (term218 P x).
Proof. exact (MK_COMB (@lem1694651) (@lem1694650 P x)). Qed.
Lemma lem1694653 (P : real -> Prop) (x : real) : ((term204 P x) = (term205 P x)) = ((term39 P x) = (term218 P x)).
Proof. exact (MK_COMB (@lem1694644 P x) (@lem1694652 P x)). Qed.
Lemma lem1694654 (P : real -> Prop) (x : real) : (term39 P x) = (term218 P x).
Proof. exact (EQ_MP (@lem1694653 P x) (@lem1694634 P x)). Qed.
Lemma lem1694655 (P : real -> Prop) : (term49 P) = (term219 P).
Proof. exact (fun_ext (fun x : real => @lem1694654 P x)). Qed.
Lemma lem1694656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1694657 (P : real -> Prop) : (term50 P) = (term220 P).
Proof. exact (MK_COMB (@lem1694656) (@lem1694655 P)). Qed.
Lemma lem1694664 (n : nat) (P : real -> Prop) (x : real) : (term215 n P x) = (term215 n P x).
Proof. exact (eq_refl (term215 n P x)). Qed.
Lemma lem1694665 (P : real -> Prop) (x : real) : (term217 P x) = (term217 P x).
Proof. exact (fun_ext (fun n : nat => @lem1694664 n P x)). Qed.
Lemma lem1694666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694667 (P : real -> Prop) (x : real) : (term218 P x) = (term218 P x).
Proof. exact (MK_COMB (@lem1694666) (@lem1694665 P x)). Qed.
Lemma lem1694668 (P : real -> Prop) : (term219 P) = (term219 P).
Proof. exact (fun_ext (fun x : real => @lem1694667 P x)). Qed.
Lemma lem1694669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1694670 (P : real -> Prop) : (term220 P) = (term220 P).
Proof. exact (MK_COMB (@lem1694669) (@lem1694668 P)). Qed.
Lemma lem1694671 (P : real -> Prop) : (term50 P) = (term220 P).
Proof. exact (TRANS (@lem1694657 P) (@lem1694670 P)). Qed.
Lemma lem1694672 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term220 P.
Proof. exact (EQ_MP (@lem1694671 P) (@lem1694626 P n h1)). Qed.
Lemma lem1694678 (P : real -> Prop) (n : nat) : (term14 P n) = (term14 P n).
Proof. exact (eq_refl (term14 P n)). Qed.
Lemma lem1694679 (P : real -> Prop) : (term15 P) = (term15 P).
Proof. exact (fun_ext (fun n : nat => @lem1694678 P n)). Qed.
Lemma lem1694680 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1694682 (P : real -> Prop) : (term2 P) = (term2 P).
Proof. exact (MK_COMB (@lem1694680) (@lem1694679 P)). Qed.
Lemma lem1694683 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term2 P.
Proof. exact (EQ_MP (@lem1694682 P) (@lem1694627 n' x P h1)). Qed.
Lemma lem1694692 (_26157 : real) (P : real -> Prop) (n : nat) (h1 : term85 P n) : term221 P _26157.
Proof. exact (@lem1694672 P n h1 _26157). Qed.
Lemma lem1694693 (P : real -> Prop) (_26157 : real) : (term221 P _26157) = (term218 P _26157).
Proof. exact (eq_refl (term221 P _26157)). Qed.
Lemma lem1694694 (_26157 : real) (P : real -> Prop) (n : nat) (h1 : term85 P n) : term218 P _26157.
Proof. exact (EQ_MP (@lem1694693 P _26157) (@lem1694692 _26157 P n h1)). Qed.
Lemma lem1694695 (_26157 : real) (_26158 : nat) (P : real -> Prop) (n : nat) (h1 : term85 P n) : term222 P _26157 _26158.
Proof. exact (@lem1694694 _26157 P n h1 _26158). Qed.
Lemma lem1694696 (_26158 : nat) (P : real -> Prop) (_26157 : real) : (term222 P _26157 _26158) = (term215 _26158 P _26157).
Proof. exact (eq_refl (term222 P _26157 _26158)). Qed.
Lemma lem1694698 (_26159 : nat) (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term55 P _26159.
Proof. exact (@lem1694683 n' x P h1 _26159). Qed.
Lemma lem1694699 (P : real -> Prop) (_26159 : nat) : (term55 P _26159) = (term14 P _26159).
Proof. exact (eq_refl (term55 P _26159)). Qed.
Lemma lem1694706 (_26158 : nat) (_26157 : real) (P : real -> Prop) (n : nat) (h1 : term85 P n) : term215 _26158 P _26157.
Proof. exact (EQ_MP (@lem1694696 _26158 P _26157) (@lem1694695 _26157 _26158 P n h1)). Qed.
Lemma lem1694708 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term57 P n.
Proof. exact (proj2 (@lem1694623 P n h1)). Qed.
Lemma lem1694712 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : x = (real_of_num n').
Proof. exact (proj1 (@lem1694628 n' x P h1)). Qed.
Lemma lem1694714 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term32 P x.
Proof. exact (proj2 (@lem1694628 n' x P h1)). Qed.
Lemma lem1694743 (P : real -> Prop) : (term223 P) = (term223 P).
Proof. exact (eq_refl (term223 P)). Qed.
Lemma lem1694744 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : (term224 P x) = (term225 P n').
Proof. exact (MK_COMB (@lem1694743 P) (@lem1694712 n' x P h1)). Qed.
Lemma lem1694745 (P : real -> Prop) (n' : nat) : (term225 P n') = (term57 P n').
Proof. exact (eq_refl (term225 P n')). Qed.
Lemma lem1694746 (P : real -> Prop) (x : real) : (term226 P x) = (term226 P x).
Proof. exact (eq_refl (term226 P x)). Qed.
Lemma lem1694747 (x : real) (P : real -> Prop) (n' : nat) : ((term224 P x) = (term225 P n')) = ((term224 P x) = (term57 P n')).
Proof. exact (MK_COMB (@lem1694746 P x) (@lem1694745 P n')). Qed.
Lemma lem1694748 (P : real -> Prop) (x : real) : (term224 P x) = (term32 P x).
Proof. exact (eq_refl (term224 P x)). Qed.
Lemma lem1694749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694750 (P : real -> Prop) (x : real) : (term226 P x) = (term227 P x).
Proof. exact (MK_COMB (@lem1694749) (@lem1694748 P x)). Qed.
Lemma lem1694751 (P : real -> Prop) (n' : nat) : (term57 P n') = (term57 P n').
Proof. exact (eq_refl (term57 P n')). Qed.
Lemma lem1694752 (x : real) (P : real -> Prop) (n' : nat) : ((term224 P x) = (term57 P n')) = ((term32 P x) = (term57 P n')).
Proof. exact (MK_COMB (@lem1694750 P x) (@lem1694751 P n')). Qed.
Lemma lem1694753 (x : real) (P : real -> Prop) (n' : nat) : ((term224 P x) = (term225 P n')) = ((term32 P x) = (term57 P n')).
Proof. exact (TRANS (@lem1694747 x P n') (@lem1694752 x P n')). Qed.
Lemma lem1694754 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : (term32 P x) = (term57 P n').
Proof. exact (EQ_MP (@lem1694753 x P n') (@lem1694744 n' x P h1)). Qed.
Lemma lem1694755 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term57 P n'.
Proof. exact (EQ_MP (@lem1694754 n' x P h1) (@lem1694714 n' x P h1)). Qed.
Lemma lem1694781 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1694782 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (@lem1694781 (real_of_num n)). Qed.
Lemma lem1694783 (n : nat) : term228 n.
Proof. exact (fun h0 : term229 n => @lem1694782 n). Qed.
Lemma lem1694785 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1694786 (n : nat) : (term228 n) = ((real_of_num n) = (real_of_num n)).
Proof. exact (@lem1694785 ((real_of_num n) = (real_of_num n))). Qed.
Lemma lem1694787 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (EQ_MP (@lem1694786 n) (@lem1694783 n)). Qed.
Lemma lem1694793 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1694794 (P : real -> Prop) (_26157 : real) (_26158 : nat) : (term215 _26158 P _26157) = (term231 P _26157 _26158).
Proof. exact (@lem1694793 (P _26157) (term28 _26157 _26158)). Qed.
Lemma lem1694802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1694803 (P : real -> Prop) (_26157 : real) (_26158 : nat) : (term232 _26158 P _26157) = (term233 P _26157 _26158).
Proof. exact (MK_COMB (@lem1694802) (@lem1694794 P _26157 _26158)). Qed.
Lemma lem1694811 (P : real -> Prop) (_26157 : real) (_26158 : nat) : (term231 P _26157 _26158) = (term231 P _26157 _26158).
Proof. exact (eq_refl (term231 P _26157 _26158)). Qed.
Lemma lem1694812 (P : real -> Prop) (_26157 : real) (_26158 : nat) : ((term215 _26158 P _26157) = (term231 P _26157 _26158)) = ((term231 P _26157 _26158) = (term231 P _26157 _26158)).
Proof. exact (MK_COMB (@lem1694803 P _26157 _26158) (@lem1694811 P _26157 _26158)). Qed.
Lemma lem1694814 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1694815 (x : Prop) : (x = x) = True.
Proof. exact (@lem1694814 Prop x). Qed.
Lemma lem1694816 (P : real -> Prop) (_26157 : real) (_26158 : nat) : ((term231 P _26157 _26158) = (term231 P _26157 _26158)) = True.
Proof. exact (@lem1694815 (term231 P _26157 _26158)). Qed.
Lemma lem1694817 (P : real -> Prop) (_26157 : real) (_26158 : nat) : ((term215 _26158 P _26157) = (term231 P _26157 _26158)) = True.
Proof. exact (TRANS (@lem1694812 P _26157 _26158) (@lem1694816 P _26157 _26158)). Qed.
Lemma lem1694818 (P : real -> Prop) (_26157 : real) (_26158 : nat) : True = ((term215 _26158 P _26157) = (term231 P _26157 _26158)).
Proof. exact (SYM (@lem1694817 P _26157 _26158)). Qed.
Lemma lem1694819 (P : real -> Prop) (_26157 : real) (_26158 : nat) : (term215 _26158 P _26157) = (term231 P _26157 _26158).
Proof. exact (EQ_MP (@lem1694818 P _26157 _26158) (@lem0)). Qed.
Lemma lem1694820 (_26157 : real) (_26158 : nat) (P : real -> Prop) (n : nat) (h1 : term85 P n) : term231 P _26157 _26158.
Proof. exact (EQ_MP (@lem1694819 P _26157 _26158) (@lem1694706 _26158 _26157 P n h1)). Qed.
Lemma lem1694822 (b : Prop) (a : Prop) : (a \/ b) = (term234 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1694823 (_26158 : nat) (P : real -> Prop) (_26157 : real) : (term231 P _26157 _26158) = (term235 _26158 P _26157).
Proof. exact (@lem1694822 (term28 _26157 _26158) (P _26157)). Qed.
Lemma lem1694825 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1694826 (_26157 : real) (_26158 : nat) : (term236 _26157 _26158) = (_26157 = (real_of_num _26158)).
Proof. exact (@lem1694825 (_26157 = (real_of_num _26158))). Qed.
Lemma lem1694827 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1694828 (_26157 : real) (_26158 : nat) : (term237 _26157 _26158) = (term238 _26157 _26158).
Proof. exact (MK_COMB (@lem1694827) (@lem1694826 _26157 _26158)). Qed.
Lemma lem1694829 (P : real -> Prop) (_26157 : real) : (P _26157) = (P _26157).
Proof. exact (eq_refl (P _26157)). Qed.
Lemma lem1694830 (_26158 : nat) (P : real -> Prop) (_26157 : real) : (term235 _26158 P _26157) = (term239 _26158 P _26157).
Proof. exact (MK_COMB (@lem1694828 _26157 _26158) (@lem1694829 P _26157)). Qed.
Lemma lem1694831 (_26158 : nat) (P : real -> Prop) (_26157 : real) : (term231 P _26157 _26158) = (term239 _26158 P _26157).
Proof. exact (TRANS (@lem1694823 _26158 P _26157) (@lem1694830 _26158 P _26157)). Qed.
Lemma lem1694834 (_26158 : nat) (_26157 : real) (P : real -> Prop) (n : nat) (h1 : term85 P n) : term239 _26158 P _26157.
Proof. exact (EQ_MP (@lem1694831 _26158 P _26157) (@lem1694820 _26157 _26158 P n h1)). Qed.
Lemma lem1694835 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term240 P n.
Proof. exact (@lem1694834 n (real_of_num n) P n h1). Qed.
Lemma lem1694838 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term14 P n.
Proof. exact (@lem1694835 P n h1 (@lem1694787 n)). Qed.
Lemma lem1694839 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term241 P n.
Proof. exact (fun h0 : term57 P n => @lem1694838 P n h1). Qed.
Lemma lem1694841 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1694842 (P : real -> Prop) (n : nat) : (term241 P n) = (term14 P n).
Proof. exact (@lem1694841 (term14 P n)). Qed.
Lemma lem1694843 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term14 P n.
Proof. exact (EQ_MP (@lem1694842 P n) (@lem1694839 P n h1)). Qed.
Lemma lem1694846 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1694848 (P : real -> Prop) (n : nat) : (term57 P n) = (term242 P n).
Proof. exact (@lem1694846 (term14 P n)). Qed.
Lemma lem1694851 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term242 P n.
Proof. exact (EQ_MP (@lem1694848 P n) (@lem1694708 P n h1)). Qed.
Lemma lem1694854 (P : real -> Prop) (n : nat) (h1 : term85 P n) : False.
Proof. exact (@lem1694851 P n h1 (@lem1694843 P n h1)). Qed.
Lemma lem1694855 (P : real -> Prop) (n : nat) (h1 : term85 P n) : term243.
Proof. exact (fun h0 : ~ False => @lem1694854 P n h1). Qed.
Lemma lem1694857 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1694858 : term243 = False.
Proof. exact (@lem1694857 False). Qed.
Lemma lem1694859 (P : real -> Prop) (n : nat) (h1 : term85 P n) : False.
Proof. exact (EQ_MP (@lem1694858) (@lem1694855 P n h1)). Qed.
Lemma lem1694861 (_26159 : nat) (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term14 P _26159.
Proof. exact (EQ_MP (@lem1694699 P _26159) (@lem1694698 _26159 n' x P h1)). Qed.
Lemma lem1694862 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term14 P n'.
Proof. exact (@lem1694861 n' n' x P h1). Qed.
Lemma lem1694863 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term241 P n'.
Proof. exact (fun h0 : term57 P n' => @lem1694862 n' x P h1). Qed.
Lemma lem1694865 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1694866 (P : real -> Prop) (n' : nat) : (term241 P n') = (term14 P n').
Proof. exact (@lem1694865 (term14 P n')). Qed.
Lemma lem1694867 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term14 P n'.
Proof. exact (EQ_MP (@lem1694866 P n') (@lem1694863 n' x P h1)). Qed.
Lemma lem1694870 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1694872 (P : real -> Prop) (n' : nat) : (term57 P n') = (term242 P n').
Proof. exact (@lem1694870 (term14 P n')). Qed.
Lemma lem1694875 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term242 P n'.
Proof. exact (EQ_MP (@lem1694872 P n') (@lem1694755 n' x P h1)). Qed.
Lemma lem1694878 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : False.
Proof. exact (@lem1694875 n' x P h1 (@lem1694867 n' x P h1)). Qed.
Lemma lem1694879 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : term243.
Proof. exact (fun h0 : ~ False => @lem1694878 n' x P h1). Qed.
Lemma lem1694881 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1694882 : term243 = False.
Proof. exact (@lem1694881 False). Qed.
Lemma lem1694884 (n' : nat) (x : real) (P : real -> Prop) (h1 : term140 n' x P) : False.
Proof. exact (EQ_MP (@lem1694882) (@lem1694879 n' x P h1)). Qed.
Lemma lem1694885 (n : nat) (n' : nat) (x : real) (P : real -> Prop) (h1 : term192 n n' x P) : False.
Proof. exact (or_elim (@lem1694622 n n' x P h1) (fun h0 : term85 P n => @lem1694859 P n h0) (fun h0 : term140 n' x P => @lem1694884 n' x P h0)). Qed.
Lemma lem1694886 (n : nat) (n' : nat) (x : real) (P : real -> Prop) (h1 : term192 n n' x P) : (term192 n n' x P) = False.
Proof. exact (prop_ext (fun h2 : term192 n n' x P => @lem1694885 n n' x P h1) (fun h2 : False => @lem1694622 n n' x P h1)). Qed.
Lemma lem1694887 (n : nat) (n' : nat) (x : real) (P : real -> Prop) (h1 : term192 n n' x P) : False.
Proof. exact (EQ_MP (@lem1694886 n n' x P h1) (@lem1694622 n n' x P h1)). Qed.
Lemma lem1694888 (n : nat) (x : real) (P : real -> Prop) (h1 : term195 n x P) : False.
Proof. exact (ex_elim (@lem1694560 n x P h1) (fun n' : nat => fun h0 : term194 n x P n' => @lem1694887 n n' x P h0)). Qed.
Lemma lem1694889 (n : nat) (P : real -> Prop) (h1 : term197 n P) : False.
Proof. exact (ex_elim (@lem1694559 n P h1) (fun x : real => fun h0 : term196 n P x => @lem1694888 n x P h0)). Qed.
Lemma lem1694890 (P : real -> Prop) (h1 : term4 P) : False.
Proof. exact (ex_elim (@lem1694558 P h1) (fun n : nat => fun h0 : term198 P n => @lem1694889 n P h0)). Qed.
Lemma lem1694891 (P : real -> Prop) (h1 : term4 P) : (term4 P) = False.
Proof. exact (prop_ext (fun h2 : term4 P => @lem1694890 P h1) (fun h2 : False => @lem1694210 P h1)). Qed.
Lemma lem1694892 (P : real -> Prop) (h1 : term4 P) : False.
Proof. exact (EQ_MP (@lem1694891 P h1) (@lem1694210 P h1)). Qed.
Lemma lem1694893 (P : real -> Prop) : term3 P.
Proof. exact (fun h0 : term4 P => @lem1694892 P h0). Qed.
Lemma lem1694894 (P : real -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem1694209 P) (@lem1694893 P)). Qed.
Lemma lem1694899 : term13.
Proof. exact (fun P : real -> Prop => @lem1694894 P). Qed.
Lemma lem1694900 : term12.
Proof. exact (EQ_MP (@lem1694205) (@lem1694899)). Qed.
Lemma lem1694901 (P : real -> Prop) : term244 P.
Proof. exact (@lem1694900 P). Qed.
Lemma lem1694902 (P : real -> Prop) : (term244 P) = (term3 P).
Proof. exact (eq_refl (term244 P)). Qed.
Lemma lem1694903 (P : real -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem1694902 P) (@lem1694901 P)). Qed.
Lemma lem1694905 (P : real -> Prop) : term3 P.
Proof. exact (@lem1694118 P (@lem1694903 P)). Qed.
Lemma lem1694906 (P : real -> Prop) (h1 : term4 P) : False.
Proof. exact (@lem1694905 P (@lem1694103 P h1)). Qed.
Lemma lem1694907 (P : real -> Prop) (h1 : term4 P) : (term4 P) = False.
Proof. exact (prop_ext (fun h2 : term4 P => @lem1694906 P h1) (fun h2 : False => @lem1694103 P h1)). Qed.
Lemma lem1694908 (P : real -> Prop) (h1 : term4 P) : False.
Proof. exact (EQ_MP (@lem1694907 P h1) (@lem1694103 P h1)). Qed.
Lemma lem1694909 (P : real -> Prop) : term3 P.
Proof. exact (fun h0 : term4 P => @lem1694908 P h0). Qed.
Lemma lem1694913 (t : Prop) : (term9 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1694919 (M : real) : (term245 M) = (term246 M).
Proof. exact (@lem1694913 (term246 M)). Qed.
Lemma lem1694920 (M : real) : (term246 M) = (term247 M).
Proof. exact (@lem1483523 (term248 M) M). Qed.
Lemma lem1694921 (M : real) : M = M.
Proof. exact (eq_refl M). Qed.
Lemma lem1694927 (M : real) : (term248 M) = (term249 M).
Proof. exact (@lem1483519 M term250). Qed.
Lemma lem1694929 (m : nat) (n : nat) : (term251 m n) = (term252 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1694930 : term253 = term254.
Proof. exact (@lem1694929 term255 term255). Qed.
Lemma lem1694931 : (term256 = (BIT1 0)) = (term257 = term255).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1694932 : term257 = term255.
Proof. exact (EQ_MP (@lem1694931) (@lem940073)). Qed.
Lemma lem1694933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1694934 : term258 = term250.
Proof. exact (MK_COMB (@lem1694933) (@lem1694932)). Qed.
Lemma lem1694935 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1694936 : term254 = term259.
Proof. exact (MK_COMB (@lem1694935) (@lem1694934)). Qed.
Lemma lem1694937 : term253 = term259.
Proof. exact (TRANS (@lem1694930) (@lem1694936)). Qed.
Lemma lem1694938 (M : real) : (real_add M) = (real_add M).
Proof. exact (eq_refl (real_add M)). Qed.
Lemma lem1694941 (M : real) : (term249 M) = (term260 M).
Proof. exact (MK_COMB (@lem1694938 M) (@lem1694937)). Qed.
Lemma lem1694943 (M : real) : (term248 M) = (term260 M).
Proof. exact (TRANS (@lem1694927 M) (@lem1694941 M)). Qed.
Lemma lem1694944 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1694945 (M : real) : (term261 M) = (term262 M).
Proof. exact (MK_COMB (@lem1694944) (@lem1694943 M)). Qed.
Lemma lem1694946 (M : real) : (term263 M) = (term264 M).
Proof. exact (MK_COMB (@lem1694945 M) (@lem1694921 M)). Qed.
Lemma lem1694947 (M : real) : (term264 M) = (term265 M).
Proof. exact (@lem1483519 (term260 M) M). Qed.
Lemma lem1694951 (M : real) : (term265 M) = (term266 M).
Proof. exact (@lem1483486 M (term267 M) term259). Qed.
Lemma lem1694952 (M : real) : (term268 M) = (term269 M).
Proof. exact (@lem1483442 term259 M). Qed.
Lemma lem1694954 (m : nat) : (term270 m) = term271.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1694955 : term272 = term271.
Proof. exact (@lem1694954 term255). Qed.
Lemma lem1694956 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1694957 : term273 = term274.
Proof. exact (MK_COMB (@lem1694956) (@lem1694955)). Qed.
Lemma lem1694958 (M : real) : M = M.
Proof. exact (eq_refl M). Qed.
Lemma lem1694959 (M : real) : (term269 M) = (term275 M).
Proof. exact (MK_COMB (@lem1694957) (@lem1694958 M)). Qed.
Lemma lem1694960 (M : real) : (term268 M) = (term275 M).
Proof. exact (TRANS (@lem1694952 M) (@lem1694959 M)). Qed.
Lemma lem1694961 (M : real) : (term275 M) = term271.
Proof. exact (@lem1483446 M). Qed.
Lemma lem1694962 (M : real) : (term268 M) = term271.
Proof. exact (TRANS (@lem1694960 M) (@lem1694961 M)). Qed.
Lemma lem1694963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1694964 (M : real) : (term276 M) = term277.
Proof. exact (MK_COMB (@lem1694963) (@lem1694962 M)). Qed.
Lemma lem1694965 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem1694966 (M : real) : (term266 M) = term278.
Proof. exact (MK_COMB (@lem1694964 M) (@lem1694965)). Qed.
Lemma lem1694967 (M : real) : (term265 M) = term278.
Proof. exact (TRANS (@lem1694951 M) (@lem1694966 M)). Qed.
Lemma lem1694968 : term278 = term259.
Proof. exact (@lem1483448 term259). Qed.
Lemma lem1694970 (M : real) : (term265 M) = term259.
Proof. exact (TRANS (@lem1694967 M) (@lem1694968)). Qed.
Lemma lem1694971 (M : real) : (term264 M) = term259.
Proof. exact (TRANS (@lem1694947 M) (@lem1694970 M)). Qed.
Lemma lem1694972 (M : real) : (term263 M) = term259.
Proof. exact (TRANS (@lem1694946 M) (@lem1694971 M)). Qed.
Lemma lem1694973 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1694974 (M : real) : (term279 M) = term280.
Proof. exact (MK_COMB (@lem1694973) (@lem1694972 M)). Qed.
Lemma lem1694975 : term271 = term271.
Proof. exact (eq_refl term271). Qed.
Lemma lem1694976 (M : real) : (term247 M) = term281.
Proof. exact (MK_COMB (@lem1694974 M) (@lem1694975)). Qed.
Lemma lem1694977 (M : real) : (term246 M) = term281.
Proof. exact (TRANS (@lem1694920 M) (@lem1694976 M)). Qed.
Lemma lem1694986 (M : real) : (term245 M) = term281.
Proof. exact (TRANS (@lem1694919 M) (@lem1694977 M)). Qed.
Lemma lem1694990 (h1 : term281) : term281.
Proof. exact (h1). Qed.
Lemma lem1694992 (m : nat) (n : nat) : (term282 m n) = (term283 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1694993 : term281 = term284.
Proof. exact (@lem1694992 term255 (NUMERAL 0)). Qed.
Lemma lem1694994 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1694995 : term285 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1694996 (h1 : term285 = (BIT1 0)) : (term255 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1694997 : (term285 = (BIT1 0)) = ((term255 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term285 = (BIT1 0) => @lem1694996 h1) (fun h1 : (term255 = (NUMERAL 0)) = False => @lem1694995)). Qed.
Lemma lem1694998 : (term255 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1694997) (@lem1694995)). Qed.
Lemma lem1694999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1695000 : term286 = (and False).
Proof. exact (MK_COMB (@lem1694999) (@lem1694998)). Qed.
Lemma lem1695001 : term284 = (False /\ True).
Proof. exact (MK_COMB (@lem1695000) (@lem1694994)). Qed.
Lemma lem1695003 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1695004 : term284 = False.
Proof. exact (TRANS (@lem1695001) (@lem1695003)). Qed.
Lemma lem1695005 : term281 = False.
Proof. exact (TRANS (@lem1694993) (@lem1695004)). Qed.
Lemma lem1695006 (h1 : term281) : False.
Proof. exact (EQ_MP (@lem1695005) (@lem1694990 h1)). Qed.
Lemma lem1695008 (h1 : term281) : term281.
Proof. exact (h1). Qed.
Lemma lem1695009 (h1 : term281) : term281 = False.
Proof. exact (prop_ext (fun h2 : term281 => @lem1695006 h1) (fun h2 : False => @lem1695008 h1)). Qed.
Lemma lem1695010 (h1 : term281) : False.
Proof. exact (EQ_MP (@lem1695009 h1) (@lem1695008 h1)). Qed.
Lemma lem1695011 (M : real) (h1 : term245 M) : term245 M.
Proof. exact (h1). Qed.
Lemma lem1695012 (M : real) (h1 : term245 M) : term281.
Proof. exact (EQ_MP (@lem1694986 M) (@lem1695011 M h1)). Qed.
Lemma lem1695013 (M : real) (h1 : term245 M) : term281 = False.
Proof. exact (prop_ext (fun h2 : term281 => @lem1695010 h2) (fun h2 : False => @lem1695012 M h1)). Qed.
Lemma lem1695014 (M : real) (h1 : term245 M) : False.
Proof. exact (EQ_MP (@lem1695013 M h1) (@lem1695012 M h1)). Qed.
Lemma lem1695015 (M : real) : term287 M.
Proof. exact (fun h0 : term245 M => @lem1695014 M h0). Qed.
Lemma lem1695016 (M : real) : term288 M.
Proof. exact (@lem1386578 (term289 M)). Qed.
Lemma lem1695017 (M : real) : term289 M.
Proof. exact (@lem1695016 M (@lem1695015 M)). Qed.
Lemma lem1695028 : term290.
Proof. exact (fun M : real => @lem1695017 M). Qed.
Lemma lem1695029 : term291.
Proof. exact (@lem1351370 term292). Qed.
Lemma lem1695030 : term291 = term293.
Proof. exact (eq_refl term291). Qed.
Lemma lem1695031 : term293.
Proof. exact (EQ_MP (@lem1695030) (@lem1695029)). Qed.
Lemma lem1695043 {A B : Type'} (f : A -> B) (y : A) : (term294 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1695044 (f : real -> Prop) (y : real) : (term295 f y) = (f y).
Proof. exact (@lem1695043 real Prop f y). Qed.
Lemma lem1695045 (x : real) : (term296 x) = (term297 x).
Proof. exact (@lem1695044 term292 x). Qed.
Lemma lem1695046 (y : real) : (term297 y) = (term17 y).
Proof. exact (eq_refl (term297 y)). Qed.
Lemma lem1695047 : term298 = term292.
Proof. exact (fun_ext (fun y : real => @lem1695046 y)). Qed.
Lemma lem1695048 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1695049 (x : real) : (term296 x) = (term297 x).
Proof. exact (MK_COMB (@lem1695047) (@lem1695048 x)). Qed.
Lemma lem1695050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1695051 (x : real) : (term299 x) = (term300 x).
Proof. exact (MK_COMB (@lem1695050) (@lem1695049 x)). Qed.
Lemma lem1695052 (x : real) : (term297 x) = (term17 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1695053 (x : real) : ((term296 x) = (term297 x)) = ((term297 x) = (term17 x)).
Proof. exact (MK_COMB (@lem1695051 x) (@lem1695052 x)). Qed.
Lemma lem1695054 (x : real) : (term297 x) = (term17 x).
Proof. exact (EQ_MP (@lem1695053 x) (@lem1695045 x)). Qed.
Lemma lem1695061 : term298 = term292.
Proof. exact (fun_ext (fun x : real => @lem1695054 x)). Qed.
Lemma lem1695062 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695063 : term301 = term302.
Proof. exact (MK_COMB (@lem1695062) (@lem1695061)). Qed.
Lemma lem1695068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1695069 : term303 = term304.
Proof. exact (MK_COMB (@lem1695068) (@lem1695063)). Qed.
Lemma lem1695081 {A B : Type'} (f : A -> B) (y : A) : (term294 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1695082 (f : real -> Prop) (y : real) : (term295 f y) = (f y).
Proof. exact (@lem1695081 real Prop f y). Qed.
Lemma lem1695083 (x : real) : (term296 x) = (term297 x).
Proof. exact (@lem1695082 term292 x). Qed.
Lemma lem1695084 (y : real) : (term297 y) = (term17 y).
Proof. exact (eq_refl (term297 y)). Qed.
Lemma lem1695085 : term298 = term292.
Proof. exact (fun_ext (fun y : real => @lem1695084 y)). Qed.
Lemma lem1695086 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1695087 (x : real) : (term296 x) = (term297 x).
Proof. exact (MK_COMB (@lem1695085) (@lem1695086 x)). Qed.
Lemma lem1695088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1695089 (x : real) : (term299 x) = (term300 x).
Proof. exact (MK_COMB (@lem1695088) (@lem1695087 x)). Qed.
Lemma lem1695090 (x : real) : (term297 x) = (term17 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1695091 (x : real) : ((term296 x) = (term297 x)) = ((term297 x) = (term17 x)).
Proof. exact (MK_COMB (@lem1695089 x) (@lem1695090 x)). Qed.
Lemma lem1695092 (x : real) : (term297 x) = (term17 x).
Proof. exact (EQ_MP (@lem1695091 x) (@lem1695083 x)). Qed.
Lemma lem1695099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695100 (x : real) : (term305 x) = (term18 x).
Proof. exact (MK_COMB (@lem1695099) (@lem1695092 x)). Qed.
Lemma lem1695101 (x : real) (M : real) : (real_le x M) = (real_le x M).
Proof. exact (eq_refl (real_le x M)). Qed.
Lemma lem1695102 (x : real) (M : real) : (term306 x M) = (term307 x M).
Proof. exact (MK_COMB (@lem1695100 x) (@lem1695101 x M)). Qed.
Lemma lem1695105 (M : real) : (term308 M) = (term309 M).
Proof. exact (fun_ext (fun x : real => @lem1695102 x M)). Qed.
Lemma lem1695106 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695107 (M : real) : (term310 M) = (term311 M).
Proof. exact (MK_COMB (@lem1695106) (@lem1695105 M)). Qed.
Lemma lem1695109 (P : real -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem1694102 P) (@lem1694909 P)). Qed.
Lemma lem1695110 (M : real) : (term312 M) = (term313 M).
Proof. exact (@lem1695109 (term314 M)). Qed.
Lemma lem1695111 (x : real) (M : real) : (term315 M x) = (real_le x M).
Proof. exact (eq_refl (term315 M x)). Qed.
Lemma lem1695112 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1695113 (x : real) (M : real) : (term316 M x) = (term307 x M).
Proof. exact (MK_COMB (@lem1695112 x) (@lem1695111 x M)). Qed.
Lemma lem1695114 (M : real) : (term317 M) = (term309 M).
Proof. exact (fun_ext (fun x : real => @lem1695113 x M)). Qed.
Lemma lem1695115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695116 (M : real) : (term312 M) = (term311 M).
Proof. exact (MK_COMB (@lem1695115) (@lem1695114 M)). Qed.
Lemma lem1695117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1695118 (M : real) : (term318 M) = (term319 M).
Proof. exact (MK_COMB (@lem1695117) (@lem1695116 M)). Qed.
Lemma lem1695119 (n : nat) (M : real) : (term320 M n) = (term321 n M).
Proof. exact (eq_refl (term320 M n)). Qed.
Lemma lem1695120 (M : real) : (term322 M) = (term323 M).
Proof. exact (fun_ext (fun n : nat => @lem1695119 n M)). Qed.
Lemma lem1695121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695122 (M : real) : (term313 M) = (term324 M).
Proof. exact (MK_COMB (@lem1695121) (@lem1695120 M)). Qed.
Lemma lem1695123 (M : real) : ((term312 M) = (term313 M)) = ((term311 M) = (term324 M)).
Proof. exact (MK_COMB (@lem1695118 M) (@lem1695122 M)). Qed.
Lemma lem1695124 (M : real) : (term311 M) = (term324 M).
Proof. exact (EQ_MP (@lem1695123 M) (@lem1695110 M)). Qed.
Lemma lem1695129 (M : real) : (term310 M) = (term324 M).
Proof. exact (TRANS (@lem1695107 M) (@lem1695124 M)). Qed.
Lemma lem1695130 : term325 = term326.
Proof. exact (fun_ext (fun M : real => @lem1695129 M)). Qed.
Lemma lem1695131 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695132 : term327 = term328.
Proof. exact (MK_COMB (@lem1695131) (@lem1695130)). Qed.
Lemma lem1695137 : term329 = term330.
Proof. exact (MK_COMB (@lem1695069) (@lem1695132)). Qed.
Lemma lem1695140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695141 : term331 = term332.
Proof. exact (MK_COMB (@lem1695140) (@lem1695137)). Qed.
Lemma lem1695155 {A B : Type'} (f : A -> B) (y : A) : (term294 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1695156 (f : real -> Prop) (y : real) : (term295 f y) = (f y).
Proof. exact (@lem1695155 real Prop f y). Qed.
Lemma lem1695157 (x : real) : (term296 x) = (term297 x).
Proof. exact (@lem1695156 term292 x). Qed.
Lemma lem1695158 (y : real) : (term297 y) = (term17 y).
Proof. exact (eq_refl (term297 y)). Qed.
Lemma lem1695159 : term298 = term292.
Proof. exact (fun_ext (fun y : real => @lem1695158 y)). Qed.
Lemma lem1695160 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1695161 (x : real) : (term296 x) = (term297 x).
Proof. exact (MK_COMB (@lem1695159) (@lem1695160 x)). Qed.
Lemma lem1695162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1695163 (x : real) : (term299 x) = (term300 x).
Proof. exact (MK_COMB (@lem1695162) (@lem1695161 x)). Qed.
Lemma lem1695164 (x : real) : (term297 x) = (term17 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1695165 (x : real) : ((term296 x) = (term297 x)) = ((term297 x) = (term17 x)).
Proof. exact (MK_COMB (@lem1695163 x) (@lem1695164 x)). Qed.
Lemma lem1695166 (x : real) : (term297 x) = (term17 x).
Proof. exact (EQ_MP (@lem1695165 x) (@lem1695157 x)). Qed.
Lemma lem1695173 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695174 (x : real) : (term305 x) = (term18 x).
Proof. exact (MK_COMB (@lem1695173) (@lem1695166 x)). Qed.
Lemma lem1695175 (x : real) (M : real) : (real_le x M) = (real_le x M).
Proof. exact (eq_refl (real_le x M)). Qed.
Lemma lem1695176 (x : real) (M : real) : (term306 x M) = (term307 x M).
Proof. exact (MK_COMB (@lem1695174 x) (@lem1695175 x M)). Qed.
Lemma lem1695179 (M : real) : (term308 M) = (term309 M).
Proof. exact (fun_ext (fun x : real => @lem1695176 x M)). Qed.
Lemma lem1695180 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695181 (M : real) : (term310 M) = (term311 M).
Proof. exact (MK_COMB (@lem1695180) (@lem1695179 M)). Qed.
Lemma lem1695183 (P : real -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem1694102 P) (@lem1694909 P)). Qed.
Lemma lem1695184 (M : real) : (term312 M) = (term313 M).
Proof. exact (@lem1695183 (term314 M)). Qed.
Lemma lem1695185 (x : real) (M : real) : (term315 M x) = (real_le x M).
Proof. exact (eq_refl (term315 M x)). Qed.
Lemma lem1695186 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1695187 (x : real) (M : real) : (term316 M x) = (term307 x M).
Proof. exact (MK_COMB (@lem1695186 x) (@lem1695185 x M)). Qed.
Lemma lem1695188 (M : real) : (term317 M) = (term309 M).
Proof. exact (fun_ext (fun x : real => @lem1695187 x M)). Qed.
Lemma lem1695189 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695190 (M : real) : (term312 M) = (term311 M).
Proof. exact (MK_COMB (@lem1695189) (@lem1695188 M)). Qed.
Lemma lem1695191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1695192 (M : real) : (term318 M) = (term319 M).
Proof. exact (MK_COMB (@lem1695191) (@lem1695190 M)). Qed.
Lemma lem1695193 (n : nat) (M : real) : (term320 M n) = (term321 n M).
Proof. exact (eq_refl (term320 M n)). Qed.
Lemma lem1695194 (M : real) : (term322 M) = (term323 M).
Proof. exact (fun_ext (fun n : nat => @lem1695193 n M)). Qed.
Lemma lem1695195 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695196 (M : real) : (term313 M) = (term324 M).
Proof. exact (MK_COMB (@lem1695195) (@lem1695194 M)). Qed.
Lemma lem1695197 (M : real) : ((term312 M) = (term313 M)) = ((term311 M) = (term324 M)).
Proof. exact (MK_COMB (@lem1695192 M) (@lem1695196 M)). Qed.
Lemma lem1695198 (M : real) : (term311 M) = (term324 M).
Proof. exact (EQ_MP (@lem1695197 M) (@lem1695184 M)). Qed.
Lemma lem1695203 (M : real) : (term310 M) = (term324 M).
Proof. exact (TRANS (@lem1695181 M) (@lem1695198 M)). Qed.
Lemma lem1695204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1695205 (M : real) : (term333 M) = (term334 M).
Proof. exact (MK_COMB (@lem1695204) (@lem1695203 M)). Qed.
Lemma lem1695219 {A B : Type'} (f : A -> B) (y : A) : (term294 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1695220 (f : real -> Prop) (y : real) : (term295 f y) = (f y).
Proof. exact (@lem1695219 real Prop f y). Qed.
Lemma lem1695221 (x : real) : (term296 x) = (term297 x).
Proof. exact (@lem1695220 term292 x). Qed.
Lemma lem1695222 (y : real) : (term297 y) = (term17 y).
Proof. exact (eq_refl (term297 y)). Qed.
Lemma lem1695223 : term298 = term292.
Proof. exact (fun_ext (fun y : real => @lem1695222 y)). Qed.
Lemma lem1695224 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1695225 (x : real) : (term296 x) = (term297 x).
Proof. exact (MK_COMB (@lem1695223) (@lem1695224 x)). Qed.
Lemma lem1695226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1695227 (x : real) : (term299 x) = (term300 x).
Proof. exact (MK_COMB (@lem1695226) (@lem1695225 x)). Qed.
Lemma lem1695228 (x : real) : (term297 x) = (term17 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1695229 (x : real) : ((term296 x) = (term297 x)) = ((term297 x) = (term17 x)).
Proof. exact (MK_COMB (@lem1695227 x) (@lem1695228 x)). Qed.
Lemma lem1695230 (x : real) : (term297 x) = (term17 x).
Proof. exact (EQ_MP (@lem1695229 x) (@lem1695221 x)). Qed.
Lemma lem1695237 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695238 (x : real) : (term305 x) = (term18 x).
Proof. exact (MK_COMB (@lem1695237) (@lem1695230 x)). Qed.
Lemma lem1695239 (x : real) (M' : real) : (real_le x M') = (real_le x M').
Proof. exact (eq_refl (real_le x M')). Qed.
Lemma lem1695240 (x : real) (M' : real) : (term306 x M') = (term307 x M').
Proof. exact (MK_COMB (@lem1695238 x) (@lem1695239 x M')). Qed.
Lemma lem1695243 (M' : real) : (term308 M') = (term309 M').
Proof. exact (fun_ext (fun x : real => @lem1695240 x M')). Qed.
Lemma lem1695244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695245 (M' : real) : (term310 M') = (term311 M').
Proof. exact (MK_COMB (@lem1695244) (@lem1695243 M')). Qed.
Lemma lem1695247 (P : real -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem1694102 P) (@lem1694909 P)). Qed.
Lemma lem1695248 (M' : real) : (term312 M') = (term313 M').
Proof. exact (@lem1695247 (term314 M')). Qed.
Lemma lem1695249 (x : real) (M' : real) : (term315 M' x) = (real_le x M').
Proof. exact (eq_refl (term315 M' x)). Qed.
Lemma lem1695250 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1695251 (x : real) (M' : real) : (term316 M' x) = (term307 x M').
Proof. exact (MK_COMB (@lem1695250 x) (@lem1695249 x M')). Qed.
Lemma lem1695252 (M' : real) : (term317 M') = (term309 M').
Proof. exact (fun_ext (fun x : real => @lem1695251 x M')). Qed.
Lemma lem1695253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695254 (M' : real) : (term312 M') = (term311 M').
Proof. exact (MK_COMB (@lem1695253) (@lem1695252 M')). Qed.
Lemma lem1695255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1695256 (M' : real) : (term318 M') = (term319 M').
Proof. exact (MK_COMB (@lem1695255) (@lem1695254 M')). Qed.
Lemma lem1695257 (n : nat) (M' : real) : (term320 M' n) = (term321 n M').
Proof. exact (eq_refl (term320 M' n)). Qed.
Lemma lem1695258 (M' : real) : (term322 M') = (term323 M').
Proof. exact (fun_ext (fun n : nat => @lem1695257 n M')). Qed.
Lemma lem1695259 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695260 (M' : real) : (term313 M') = (term324 M').
Proof. exact (MK_COMB (@lem1695259) (@lem1695258 M')). Qed.
Lemma lem1695261 (M' : real) : ((term312 M') = (term313 M')) = ((term311 M') = (term324 M')).
Proof. exact (MK_COMB (@lem1695256 M') (@lem1695260 M')). Qed.
Lemma lem1695262 (M' : real) : (term311 M') = (term324 M').
Proof. exact (EQ_MP (@lem1695261 M') (@lem1695248 M')). Qed.
Lemma lem1695267 (M' : real) : (term310 M') = (term324 M').
Proof. exact (TRANS (@lem1695245 M') (@lem1695262 M')). Qed.
Lemma lem1695268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695269 (M' : real) : (term335 M') = (term336 M').
Proof. exact (MK_COMB (@lem1695268) (@lem1695267 M')). Qed.
Lemma lem1695270 (M : real) (M' : real) : (real_le M M') = (real_le M M').
Proof. exact (eq_refl (real_le M M')). Qed.
Lemma lem1695271 (M : real) (M' : real) : (term337 M M') = (term338 M M').
Proof. exact (MK_COMB (@lem1695269 M') (@lem1695270 M M')). Qed.
Lemma lem1695274 (M : real) : (term339 M) = (term340 M).
Proof. exact (fun_ext (fun M' : real => @lem1695271 M M')). Qed.
Lemma lem1695275 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695276 (M : real) : (term341 M) = (term342 M).
Proof. exact (MK_COMB (@lem1695275) (@lem1695274 M)). Qed.
Lemma lem1695281 (M : real) : (term343 M) = (term344 M).
Proof. exact (MK_COMB (@lem1695205 M) (@lem1695276 M)). Qed.
Lemma lem1695284 : term345 = term346.
Proof. exact (fun_ext (fun M : real => @lem1695281 M)). Qed.
Lemma lem1695285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695286 : term347 = term348.
Proof. exact (MK_COMB (@lem1695285) (@lem1695284)). Qed.
Lemma lem1695291 : term293 = term349.
Proof. exact (MK_COMB (@lem1695141) (@lem1695286)). Qed.
Lemma lem1695294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695295 : term350 = term351.
Proof. exact (MK_COMB (@lem1695294) (@lem1695291)). Qed.
Lemma lem1695304 : term352 = term352.
Proof. exact (eq_refl term352). Qed.
Lemma lem1695305 : term353 = term354.
Proof. exact (MK_COMB (@lem1695295) (@lem1695304)). Qed.
Lemma lem1695308 : term354 = term353.
Proof. exact (SYM (@lem1695305)). Qed.
Lemma lem1695310 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1695311 : term354 = term355.
Proof. exact (@lem1695310 term354). Qed.
Lemma lem1695312 : term355 = term354.
Proof. exact (SYM (@lem1695311)). Qed.
Lemma lem1695313 (h1 : term356) : term356.
Proof. exact (h1). Qed.
Lemma lem1695316 (h1 : term357) : term357.
Proof. exact (h1). Qed.
Lemma lem1695317 : term358.
Proof. exact (fun h0 : term357 => @lem1695316 h0). Qed.
Lemma lem1695318 (h1 : term358) : term358.
Proof. exact (h1). Qed.
Lemma lem1695319 (h1 : term357) : term357.
Proof. exact (h1). Qed.
Lemma lem1695320 (h1 : term357) (h2 : term358) : term357.
Proof. exact (@lem1695318 h2 (@lem1695319 h1)). Qed.
Lemma lem1695321 (h1 : term357) : term359.
Proof. exact (fun h0 : term358 => @lem1695320 h1 h0). Qed.
Lemma lem1695322 (h1 : term358) : term358.
Proof. exact (h1). Qed.
Lemma lem1695323 (h1 : term357) (h2 : term358) : term357.
Proof. exact (@lem1695321 h1 (@lem1695322 h2)). Qed.
Lemma lem1695324 (h1 : term358) : term358.
Proof. exact (fun h0 : term357 => @lem1695323 h0 h1). Qed.
Lemma lem1695325 : term360.
Proof. exact (fun h0 : term358 => @lem1695324 h0). Qed.
Lemma lem1695328 : term358.
Proof. exact (@lem1695325 (@lem1695317)). Qed.
Lemma lem1695498 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1695499 : term361 = term362.
Proof. exact (@lem1695498 term363). Qed.
Lemma lem1695512 : term364 = term364.
Proof. exact (eq_refl term364). Qed.
Lemma lem1695513 : term365 = term366.
Proof. exact (MK_COMB (@lem1695512) (@lem1695499)). Qed.
Lemma lem1695516 : term367 = term367.
Proof. exact (eq_refl term367). Qed.
Lemma lem1695517 : term368 = term369.
Proof. exact (MK_COMB (@lem1695516) (@lem1695513)). Qed.
Lemma lem1695520 : term370 = term370.
Proof. exact (eq_refl term370). Qed.
Lemma lem1695521 : term371 = term372.
Proof. exact (MK_COMB (@lem1695520) (@lem1695517)). Qed.
Lemma lem1695524 : term373 = term373.
Proof. exact (eq_refl term373). Qed.
Lemma lem1695531 : term357 = term374.
Proof. exact (MK_COMB (@lem1695524) (@lem1695521)). Qed.
Lemma lem1695536 (x : real) (z : real) (y : real) : ((term375 x y z) = (term376 x z y)) = ((term375 x y z) = (term376 x z y)).
Proof. exact (eq_refl ((term375 x y z) = (term376 x z y))). Qed.
Lemma lem1695537 (x : real) (y : real) : (term377 x y) = (term377 x y).
Proof. exact (fun_ext (fun z : real => @lem1695536 x z y)). Qed.
Lemma lem1695538 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695539 (x : real) (y : real) : (term378 x y) = (term378 x y).
Proof. exact (MK_COMB (@lem1695538) (@lem1695537 x y)). Qed.
Lemma lem1695540 (x : real) : (term379 x) = (term379 x).
Proof. exact (fun_ext (fun y : real => @lem1695539 x y)). Qed.
Lemma lem1695541 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695542 (x : real) : (term380 x) = (term380 x).
Proof. exact (MK_COMB (@lem1695541) (@lem1695540 x)). Qed.
Lemma lem1695543 : term381 = term381.
Proof. exact (fun_ext (fun x : real => @lem1695542 x)). Qed.
Lemma lem1695544 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695545 : term363 = term363.
Proof. exact (MK_COMB (@lem1695544) (@lem1695543)). Qed.
Lemma lem1695546 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695547 : term362 = term362.
Proof. exact (MK_COMB (@lem1695546) (@lem1695545)). Qed.
Lemma lem1695548 (m : nat) (n : nat) : ((term382 m n) = (term383 m n)) = ((term382 m n) = (term383 m n)).
Proof. exact (eq_refl ((term382 m n) = (term383 m n))). Qed.
Lemma lem1695549 (m : nat) : (term384 m) = (term384 m).
Proof. exact (fun_ext (fun n : nat => @lem1695548 m n)). Qed.
Lemma lem1695550 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695551 (m : nat) : (term385 m) = (term385 m).
Proof. exact (MK_COMB (@lem1695550) (@lem1695549 m)). Qed.
Lemma lem1695552 : term386 = term386.
Proof. exact (fun_ext (fun m : nat => @lem1695551 m)). Qed.
Lemma lem1695553 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695554 : term387 = term387.
Proof. exact (MK_COMB (@lem1695553) (@lem1695552)). Qed.
Lemma lem1695555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695556 : term364 = term364.
Proof. exact (MK_COMB (@lem1695555) (@lem1695554)). Qed.
Lemma lem1695557 : term366 = term366.
Proof. exact (MK_COMB (@lem1695556) (@lem1695547)). Qed.
Lemma lem1695562 (y : real) (x : real) : (term388 y x) = (term388 y x).
Proof. exact (eq_refl (term388 y x)). Qed.
Lemma lem1695563 (x : real) : (term389 x) = (term389 x).
Proof. exact (fun_ext (fun y : real => @lem1695562 y x)). Qed.
Lemma lem1695564 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695565 (x : real) : (term390 x) = (term390 x).
Proof. exact (MK_COMB (@lem1695564) (@lem1695563 x)). Qed.
Lemma lem1695566 : term391 = term391.
Proof. exact (fun_ext (fun x : real => @lem1695565 x)). Qed.
Lemma lem1695567 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695568 : term392 = term392.
Proof. exact (MK_COMB (@lem1695567) (@lem1695566)). Qed.
Lemma lem1695569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695570 : term367 = term367.
Proof. exact (MK_COMB (@lem1695569) (@lem1695568)). Qed.
Lemma lem1695571 : term369 = term369.
Proof. exact (MK_COMB (@lem1695570) (@lem1695557)). Qed.
Lemma lem1695574 (M : real) : (term289 M) = (term289 M).
Proof. exact (eq_refl (term289 M)). Qed.
Lemma lem1695575 : term393 = term393.
Proof. exact (fun_ext (fun M : real => @lem1695574 M)). Qed.
Lemma lem1695576 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695577 : term290 = term290.
Proof. exact (MK_COMB (@lem1695576) (@lem1695575)). Qed.
Lemma lem1695578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695579 : term370 = term370.
Proof. exact (MK_COMB (@lem1695578) (@lem1695577)). Qed.
Lemma lem1695580 : term372 = term372.
Proof. exact (MK_COMB (@lem1695579) (@lem1695571)). Qed.
Lemma lem1695581 (x : real) (n : nat) : (term394 x n) = (term394 x n).
Proof. exact (eq_refl (term394 x n)). Qed.
Lemma lem1695582 (x : real) : (term395 x) = (term395 x).
Proof. exact (fun_ext (fun n : nat => @lem1695581 x n)). Qed.
Lemma lem1695583 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1695584 (x : real) : (term396 x) = (term396 x).
Proof. exact (MK_COMB (@lem1695583) (@lem1695582 x)). Qed.
Lemma lem1695585 : term397 = term397.
Proof. exact (fun_ext (fun x : real => @lem1695584 x)). Qed.
Lemma lem1695586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695587 : term352 = term352.
Proof. exact (MK_COMB (@lem1695586) (@lem1695585)). Qed.
Lemma lem1695588 (M : real) (M' : real) : (real_le M M') = (real_le M M').
Proof. exact (eq_refl (real_le M M')). Qed.
Lemma lem1695589 (n : nat) (M' : real) : (term321 n M') = (term321 n M').
Proof. exact (eq_refl (term321 n M')). Qed.
Lemma lem1695590 (M' : real) : (term323 M') = (term323 M').
Proof. exact (fun_ext (fun n : nat => @lem1695589 n M')). Qed.
Lemma lem1695591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695592 (M' : real) : (term324 M') = (term324 M').
Proof. exact (MK_COMB (@lem1695591) (@lem1695590 M')). Qed.
Lemma lem1695593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695594 (M' : real) : (term336 M') = (term336 M').
Proof. exact (MK_COMB (@lem1695593) (@lem1695592 M')). Qed.
Lemma lem1695595 (M : real) (M' : real) : (term338 M M') = (term338 M M').
Proof. exact (MK_COMB (@lem1695594 M') (@lem1695588 M M')). Qed.
Lemma lem1695596 (M : real) : (term340 M) = (term340 M).
Proof. exact (fun_ext (fun M' : real => @lem1695595 M M')). Qed.
Lemma lem1695597 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695598 (M : real) : (term342 M) = (term342 M).
Proof. exact (MK_COMB (@lem1695597) (@lem1695596 M)). Qed.
Lemma lem1695599 (n : nat) (M : real) : (term321 n M) = (term321 n M).
Proof. exact (eq_refl (term321 n M)). Qed.
Lemma lem1695600 (M : real) : (term323 M) = (term323 M).
Proof. exact (fun_ext (fun n : nat => @lem1695599 n M)). Qed.
Lemma lem1695601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695602 (M : real) : (term324 M) = (term324 M).
Proof. exact (MK_COMB (@lem1695601) (@lem1695600 M)). Qed.
Lemma lem1695603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1695604 (M : real) : (term334 M) = (term334 M).
Proof. exact (MK_COMB (@lem1695603) (@lem1695602 M)). Qed.
Lemma lem1695605 (M : real) : (term344 M) = (term344 M).
Proof. exact (MK_COMB (@lem1695604 M) (@lem1695598 M)). Qed.
Lemma lem1695606 : term346 = term346.
Proof. exact (fun_ext (fun M : real => @lem1695605 M)). Qed.
Lemma lem1695607 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695608 : term348 = term348.
Proof. exact (MK_COMB (@lem1695607) (@lem1695606)). Qed.
Lemma lem1695609 (n : nat) (M : real) : (term321 n M) = (term321 n M).
Proof. exact (eq_refl (term321 n M)). Qed.
Lemma lem1695610 (M : real) : (term323 M) = (term323 M).
Proof. exact (fun_ext (fun n : nat => @lem1695609 n M)). Qed.
Lemma lem1695611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695612 (M : real) : (term324 M) = (term324 M).
Proof. exact (MK_COMB (@lem1695611) (@lem1695610 M)). Qed.
Lemma lem1695613 : term326 = term326.
Proof. exact (fun_ext (fun M : real => @lem1695612 M)). Qed.
Lemma lem1695614 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695615 : term328 = term328.
Proof. exact (MK_COMB (@lem1695614) (@lem1695613)). Qed.
Lemma lem1695616 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem1695617 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun n : nat => @lem1695616 x n)). Qed.
Lemma lem1695618 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1695619 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1695618) (@lem1695617 x)). Qed.
Lemma lem1695620 : term292 = term292.
Proof. exact (fun_ext (fun x : real => @lem1695619 x)). Qed.
Lemma lem1695621 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695622 : term302 = term302.
Proof. exact (MK_COMB (@lem1695621) (@lem1695620)). Qed.
Lemma lem1695623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1695624 : term304 = term304.
Proof. exact (MK_COMB (@lem1695623) (@lem1695622)). Qed.
Lemma lem1695625 : term330 = term330.
Proof. exact (MK_COMB (@lem1695624) (@lem1695615)). Qed.
Lemma lem1695626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695627 : term332 = term332.
Proof. exact (MK_COMB (@lem1695626) (@lem1695625)). Qed.
Lemma lem1695628 : term349 = term349.
Proof. exact (MK_COMB (@lem1695627) (@lem1695608)). Qed.
Lemma lem1695629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695630 : term351 = term351.
Proof. exact (MK_COMB (@lem1695629) (@lem1695628)). Qed.
Lemma lem1695631 : term354 = term354.
Proof. exact (MK_COMB (@lem1695630) (@lem1695587)). Qed.
Lemma lem1695632 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695633 : term356 = term356.
Proof. exact (MK_COMB (@lem1695632) (@lem1695631)). Qed.
Lemma lem1695634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1695635 : term373 = term373.
Proof. exact (MK_COMB (@lem1695634) (@lem1695633)). Qed.
Lemma lem1695636 : term374 = term374.
Proof. exact (MK_COMB (@lem1695635) (@lem1695580)). Qed.
Lemma lem1695767 : term357 = term374.
Proof. exact (TRANS (@lem1695531) (@lem1695636)). Qed.
Lemma lem1695768 : term374 = term357.
Proof. exact (SYM (@lem1695767)). Qed.
Lemma lem1695769 (h1 : term356) : term356.
Proof. exact (h1). Qed.
Lemma lem1695770 (h1 : term290) : term290.
Proof. exact (h1). Qed.
Lemma lem1695771 (h1 : term392) : term392.
Proof. exact (h1). Qed.
Lemma lem1695772 (h1 : term387) : term387.
Proof. exact (h1). Qed.
Lemma lem1695773 (h1 : term363) : term363.
Proof. exact (h1). Qed.
Lemma lem1695775 (P : nat -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1695776 (x : real) : (term24 x) = (term25 x).
Proof. exact (@lem1695775 (term16 x)). Qed.
Lemma lem1695777 (x : real) (n : nat) : (term26 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem1695778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695780 (x : real) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (MK_COMB (@lem1695778) (@lem1695777 x n)). Qed.
Lemma lem1695781 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun n : nat => @lem1695780 x n)). Qed.
Lemma lem1695782 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695783 (x : real) : (term25 x) = (term31 x).
Proof. exact (MK_COMB (@lem1695782) (@lem1695781 x)). Qed.
Lemma lem1695784 (x : real) : (term24 x) = (term31 x).
Proof. exact (TRANS (@lem1695776 x) (@lem1695783 x)). Qed.
Lemma lem1695785 (P : real -> Prop) : (term398 P) = (term399 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem1695786 : term400 = term401.
Proof. exact (@lem1695785 term292). Qed.
Lemma lem1695787 (x : real) : (term297 x) = (term17 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1695788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695789 (x : real) : (term402 x) = (term24 x).
Proof. exact (MK_COMB (@lem1695788) (@lem1695787 x)). Qed.
Lemma lem1695790 (x : real) : (term402 x) = (term31 x).
Proof. exact (TRANS (@lem1695789 x) (@lem1695784 x)). Qed.
Lemma lem1695791 : term403 = term404.
Proof. exact (fun_ext (fun x : real => @lem1695790 x)). Qed.
Lemma lem1695792 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695793 : term401 = term405.
Proof. exact (MK_COMB (@lem1695792) (@lem1695791)). Qed.
Lemma lem1695794 : term400 = term405.
Proof. exact (TRANS (@lem1695786) (@lem1695793)). Qed.
Lemma lem1695796 (P : nat -> Prop) : (term51 P) = (term52 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1695797 (M : real) : (term406 M) = (term407 M).
Proof. exact (@lem1695796 (term323 M)). Qed.
Lemma lem1695798 (n : nat) (M : real) : (term408 M n) = (term321 n M).
Proof. exact (eq_refl (term408 M n)). Qed.
Lemma lem1695799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695801 (n : nat) (M : real) : (term409 M n) = (term410 n M).
Proof. exact (MK_COMB (@lem1695799) (@lem1695798 n M)). Qed.
Lemma lem1695802 (M : real) : (term411 M) = (term412 M).
Proof. exact (fun_ext (fun n : nat => @lem1695801 n M)). Qed.
Lemma lem1695803 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1695804 (M : real) : (term407 M) = (term413 M).
Proof. exact (MK_COMB (@lem1695803) (@lem1695802 M)). Qed.
Lemma lem1695805 (M : real) : (term406 M) = (term413 M).
Proof. exact (TRANS (@lem1695797 M) (@lem1695804 M)). Qed.
Lemma lem1695806 (P : real -> Prop) : (term398 P) = (term399 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem1695807 : term414 = term415.
Proof. exact (@lem1695806 term326). Qed.
Lemma lem1695808 (M : real) : (term416 M) = (term324 M).
Proof. exact (eq_refl (term416 M)). Qed.
Lemma lem1695809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695810 (M : real) : (term417 M) = (term406 M).
Proof. exact (MK_COMB (@lem1695809) (@lem1695808 M)). Qed.
Lemma lem1695811 (M : real) : (term417 M) = (term413 M).
Proof. exact (TRANS (@lem1695810 M) (@lem1695805 M)). Qed.
Lemma lem1695812 : term418 = term419.
Proof. exact (fun_ext (fun M : real => @lem1695811 M)). Qed.
Lemma lem1695813 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695814 : term415 = term420.
Proof. exact (MK_COMB (@lem1695813) (@lem1695812)). Qed.
Lemma lem1695815 : term414 = term420.
Proof. exact (TRANS (@lem1695807) (@lem1695814)). Qed.
Lemma lem1695816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1695817 : term421 = term422.
Proof. exact (MK_COMB (@lem1695816) (@lem1695794)). Qed.
Lemma lem1695818 : term423 = term424.
Proof. exact (MK_COMB (@lem1695817) (@lem1695815)). Qed.
Lemma lem1695819 : term425 = term423.
Proof. exact (@lem17045 term302 term328). Qed.
Lemma lem1695820 : term425 = term424.
Proof. exact (TRANS (@lem1695819) (@lem1695818)). Qed.
Lemma lem1695821 (n : nat) (M : real) : (term321 n M) = (term321 n M).
Proof. exact (eq_refl (term321 n M)). Qed.
Lemma lem1695822 (M : real) : (term323 M) = (term323 M).
Proof. exact (fun_ext (fun n : nat => @lem1695821 n M)). Qed.
Lemma lem1695823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695824 (M : real) : (term324 M) = (term324 M).
Proof. exact (MK_COMB (@lem1695823) (@lem1695822 M)). Qed.
Lemma lem1695826 (P : nat -> Prop) : (term51 P) = (term52 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1695827 (M' : real) : (term406 M') = (term407 M').
Proof. exact (@lem1695826 (term323 M')). Qed.
Lemma lem1695828 (n : nat) (M' : real) : (term408 M' n) = (term321 n M').
Proof. exact (eq_refl (term408 M' n)). Qed.
Lemma lem1695829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695831 (n : nat) (M' : real) : (term409 M' n) = (term410 n M').
Proof. exact (MK_COMB (@lem1695829) (@lem1695828 n M')). Qed.
Lemma lem1695832 (M' : real) : (term411 M') = (term412 M').
Proof. exact (fun_ext (fun n : nat => @lem1695831 n M')). Qed.
Lemma lem1695833 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1695834 (M' : real) : (term407 M') = (term413 M').
Proof. exact (MK_COMB (@lem1695833) (@lem1695832 M')). Qed.
Lemma lem1695835 (M' : real) : (term406 M') = (term413 M').
Proof. exact (TRANS (@lem1695827 M') (@lem1695834 M')). Qed.
Lemma lem1695836 (M : real) (M' : real) : (real_le M M') = (real_le M M').
Proof. exact (eq_refl (real_le M M')). Qed.
Lemma lem1695837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1695838 (M' : real) : (term426 M') = (term427 M').
Proof. exact (MK_COMB (@lem1695837) (@lem1695835 M')). Qed.
Lemma lem1695839 (M : real) (M' : real) : (term428 M M') = (term429 M M').
Proof. exact (MK_COMB (@lem1695838 M') (@lem1695836 M M')). Qed.
Lemma lem1695840 (M : real) (M' : real) : (term338 M M') = (term428 M M').
Proof. exact (@lem17265 (term324 M') (real_le M M')). Qed.
Lemma lem1695841 (M : real) (M' : real) : (term338 M M') = (term429 M M').
Proof. exact (TRANS (@lem1695840 M M') (@lem1695839 M M')). Qed.
Lemma lem1695842 (M : real) : (term340 M) = (term430 M).
Proof. exact (fun_ext (fun M' : real => @lem1695841 M M')). Qed.
Lemma lem1695843 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1695844 (M : real) : (term342 M) = (term431 M).
Proof. exact (MK_COMB (@lem1695843) (@lem1695842 M)). Qed.
Lemma lem1695845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1695846 (M : real) : (term334 M) = (term334 M).
Proof. exact (MK_COMB (@lem1695845) (@lem1695824 M)). Qed.
Lemma lem1695847 (M : real) : (term344 M) = (term432 M).
Proof. exact (MK_COMB (@lem1695846 M) (@lem1695844 M)). Qed.
Lemma lem1695848 : term346 = term433.
Proof. exact (fun_ext (fun M : real => @lem1695847 M)). Qed.
Lemma lem1695849 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695850 : term348 = term434.
Proof. exact (MK_COMB (@lem1695849) (@lem1695848)). Qed.
Lemma lem1695851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1695852 : term435 = term436.
Proof. exact (MK_COMB (@lem1695851) (@lem1695820)). Qed.
Lemma lem1695853 : term437 = term438.
Proof. exact (MK_COMB (@lem1695852) (@lem1695850)). Qed.
Lemma lem1695854 : term349 = term437.
Proof. exact (@lem17265 term330 term348). Qed.
Lemma lem1695855 : term349 = term438.
Proof. exact (TRANS (@lem1695854) (@lem1695853)). Qed.
Lemma lem1695857 (P : nat -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1695858 (x : real) : (term439 x) = (term440 x).
Proof. exact (@lem1695857 (term395 x)). Qed.
Lemma lem1695859 (x : real) (n : nat) : (term441 x n) = (term394 x n).
Proof. exact (eq_refl (term441 x n)). Qed.
Lemma lem1695860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695862 (x : real) (n : nat) : (term442 x n) = (term443 x n).
Proof. exact (MK_COMB (@lem1695860) (@lem1695859 x n)). Qed.
Lemma lem1695863 (x : real) : (term444 x) = (term445 x).
Proof. exact (fun_ext (fun n : nat => @lem1695862 x n)). Qed.
Lemma lem1695864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1695865 (x : real) : (term440 x) = (term446 x).
Proof. exact (MK_COMB (@lem1695864) (@lem1695863 x)). Qed.
Lemma lem1695866 (x : real) : (term439 x) = (term446 x).
Proof. exact (TRANS (@lem1695858 x) (@lem1695865 x)). Qed.
Lemma lem1695867 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1695868 : term447 = term448.
Proof. exact (@lem1695867 term397). Qed.
Lemma lem1695869 (x : real) : (term449 x) = (term396 x).
Proof. exact (eq_refl (term449 x)). Qed.
Lemma lem1695870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1695871 (x : real) : (term450 x) = (term439 x).
Proof. exact (MK_COMB (@lem1695870) (@lem1695869 x)). Qed.
Lemma lem1695872 (x : real) : (term450 x) = (term446 x).
Proof. exact (TRANS (@lem1695871 x) (@lem1695866 x)). Qed.
Lemma lem1695873 : term451 = term452.
Proof. exact (fun_ext (fun x : real => @lem1695872 x)). Qed.
Lemma lem1695874 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1695875 : term448 = term453.
Proof. exact (MK_COMB (@lem1695874) (@lem1695873)). Qed.
Lemma lem1695876 : term447 = term453.
Proof. exact (TRANS (@lem1695868) (@lem1695875)). Qed.
Lemma lem1695877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1695878 : term454 = term455.
Proof. exact (MK_COMB (@lem1695877) (@lem1695855)). Qed.
Lemma lem1695879 : term456 = term457.
Proof. exact (MK_COMB (@lem1695878) (@lem1695876)). Qed.
Lemma lem1695880 : term356 = term456.
Proof. exact (@lem17362 term349 term352). Qed.
Lemma lem1695881 : term356 = term457.
Proof. exact (TRANS (@lem1695880) (@lem1695879)). Qed.
Lemma lem1696012 {A B : Type'} (P : type1413 A B) : (term458 A B P) = (term459 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1696013 (P : type1622) : (term460 P) = (term461 P).
Proof. exact (@lem1696012 real nat P). Qed.
Lemma lem1696014 : term462 = term463.
Proof. exact (@lem1696013 term464). Qed.
Lemma lem1696015 (M : real) : (term465 M) = (term412 M).
Proof. exact (eq_refl (term465 M)). Qed.
Lemma lem1696016 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1696017 (M : real) (n : nat) : (term466 M n) = (term467 M n).
Proof. exact (MK_COMB (@lem1696015 M) (@lem1696016 n)). Qed.
Lemma lem1696018 (n : nat) (M : real) : (term467 M n) = (term410 n M).
Proof. exact (eq_refl (term467 M n)). Qed.
Lemma lem1696019 (n : nat) (M : real) : (term466 M n) = (term410 n M).
Proof. exact (TRANS (@lem1696017 M n) (@lem1696018 n M)). Qed.
Lemma lem1696020 (M : real) : (term468 M) = (term412 M).
Proof. exact (fun_ext (fun n : nat => @lem1696019 n M)). Qed.
Lemma lem1696021 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1696022 (M : real) : (term469 M) = (term413 M).
Proof. exact (MK_COMB (@lem1696021) (@lem1696020 M)). Qed.
Lemma lem1696023 : term470 = term419.
Proof. exact (fun_ext (fun M : real => @lem1696022 M)). Qed.
Lemma lem1696024 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696025 : term462 = term420.
Proof. exact (MK_COMB (@lem1696024) (@lem1696023)). Qed.
Lemma lem1696026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696027 : term471 = term472.
Proof. exact (MK_COMB (@lem1696026) (@lem1696025)). Qed.
Lemma lem1696028 (M : real) : (term465 M) = (term412 M).
Proof. exact (eq_refl (term465 M)). Qed.
Lemma lem1696029 (n : real -> nat) (M : real) : (n M) = (n M).
Proof. exact (eq_refl (n M)). Qed.
Lemma lem1696030 (n : real -> nat) (M : real) : (term473 n M) = (term474 n M).
Proof. exact (MK_COMB (@lem1696028 M) (@lem1696029 n M)). Qed.
Lemma lem1696031 (n : real -> nat) (M : real) : (term474 n M) = (term475 n M).
Proof. exact (eq_refl (term474 n M)). Qed.
Lemma lem1696032 (n : real -> nat) (M : real) : (term473 n M) = (term475 n M).
Proof. exact (TRANS (@lem1696030 n M) (@lem1696031 n M)). Qed.
Lemma lem1696033 (n : real -> nat) : (term476 n) = (term477 n).
Proof. exact (fun_ext (fun M : real => @lem1696032 n M)). Qed.
Lemma lem1696034 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696035 (n : real -> nat) : (term478 n) = (term479 n).
Proof. exact (MK_COMB (@lem1696034) (@lem1696033 n)). Qed.
Lemma lem1696036 : term480 = term481.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696035 n)). Qed.
Lemma lem1696037 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696038 : term463 = term482.
Proof. exact (MK_COMB (@lem1696037) (@lem1696036)). Qed.
Lemma lem1696039 : (term462 = term463) = (term420 = term482).
Proof. exact (MK_COMB (@lem1696027) (@lem1696038)). Qed.
Lemma lem1696040 : term420 = term482.
Proof. exact (EQ_MP (@lem1696039) (@lem1696014)). Qed.
Lemma lem1696041 : term422 = term422.
Proof. exact (eq_refl term422). Qed.
Lemma lem1696042 : term424 = term483.
Proof. exact (MK_COMB (@lem1696041) (@lem1696040)). Qed.
Lemma lem1696044 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1696045 (P : Prop) (Q : type1024) : (term484 P Q) = (term485 P Q).
Proof. exact (@lem1696044 (real -> nat) P Q). Qed.
Lemma lem1696046 : term486 = term487.
Proof. exact (@lem1696045 term405 term481). Qed.
Lemma lem1696047 (n : real -> nat) : (term488 n) = (term479 n).
Proof. exact (eq_refl (term488 n)). Qed.
Lemma lem1696048 : term489 = term481.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696047 n)). Qed.
Lemma lem1696049 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696050 : term490 = term482.
Proof. exact (MK_COMB (@lem1696049) (@lem1696048)). Qed.
Lemma lem1696051 : term422 = term422.
Proof. exact (eq_refl term422). Qed.
Lemma lem1696052 : term486 = term483.
Proof. exact (MK_COMB (@lem1696051) (@lem1696050)). Qed.
Lemma lem1696053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696054 : term491 = term492.
Proof. exact (MK_COMB (@lem1696053) (@lem1696052)). Qed.
Lemma lem1696055 (n : real -> nat) : (term488 n) = (term479 n).
Proof. exact (eq_refl (term488 n)). Qed.
Lemma lem1696056 : term422 = term422.
Proof. exact (eq_refl term422). Qed.
Lemma lem1696057 (n : real -> nat) : (term493 n) = (term494 n).
Proof. exact (MK_COMB (@lem1696056) (@lem1696055 n)). Qed.
Lemma lem1696058 : term495 = term496.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696057 n)). Qed.
Lemma lem1696059 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696060 : term487 = term497.
Proof. exact (MK_COMB (@lem1696059) (@lem1696058)). Qed.
Lemma lem1696061 : (term486 = term487) = (term483 = term497).
Proof. exact (MK_COMB (@lem1696054) (@lem1696060)). Qed.
Lemma lem1696062 : term483 = term497.
Proof. exact (EQ_MP (@lem1696061) (@lem1696046)). Qed.
Lemma lem1696063 : term424 = term497.
Proof. exact (TRANS (@lem1696042) (@lem1696062)). Qed.
Lemma lem1696064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1696065 : term436 = term498.
Proof. exact (MK_COMB (@lem1696064) (@lem1696063)). Qed.
Lemma lem1696067 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1696068 (P : nat -> Prop) (Q : Prop) : (term149 P Q) = (term150 P Q).
Proof. exact (@lem1696067 nat P Q). Qed.
Lemma lem1696069 (M : real) (M' : real) : (term499 M M') = (term500 M M').
Proof. exact (@lem1696068 (term412 M') (real_le M M')). Qed.
Lemma lem1696070 (n : nat) (M' : real) : (term467 M' n) = (term410 n M').
Proof. exact (eq_refl (term467 M' n)). Qed.
Lemma lem1696071 (M' : real) : (term501 M') = (term412 M').
Proof. exact (fun_ext (fun n : nat => @lem1696070 n M')). Qed.
Lemma lem1696072 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1696073 (M' : real) : (term502 M') = (term413 M').
Proof. exact (MK_COMB (@lem1696072) (@lem1696071 M')). Qed.
Lemma lem1696074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1696075 (M' : real) : (term503 M') = (term427 M').
Proof. exact (MK_COMB (@lem1696074) (@lem1696073 M')). Qed.
Lemma lem1696076 (M : real) (M' : real) : (real_le M M') = (real_le M M').
Proof. exact (eq_refl (real_le M M')). Qed.
Lemma lem1696077 (M : real) (M' : real) : (term499 M M') = (term429 M M').
Proof. exact (MK_COMB (@lem1696075 M') (@lem1696076 M M')). Qed.
Lemma lem1696078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696079 (M : real) (M' : real) : (term504 M M') = (term505 M M').
Proof. exact (MK_COMB (@lem1696078) (@lem1696077 M M')). Qed.
Lemma lem1696080 (n : nat) (M' : real) : (term467 M' n) = (term410 n M').
Proof. exact (eq_refl (term467 M' n)). Qed.
Lemma lem1696081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1696082 (n : nat) (M' : real) : (term506 M' n) = (term507 n M').
Proof. exact (MK_COMB (@lem1696081) (@lem1696080 n M')). Qed.
Lemma lem1696083 (M : real) (M' : real) : (real_le M M') = (real_le M M').
Proof. exact (eq_refl (real_le M M')). Qed.
Lemma lem1696084 (n : nat) (M : real) (M' : real) : (term508 n M M') = (term509 n M M').
Proof. exact (MK_COMB (@lem1696082 n M') (@lem1696083 M M')). Qed.
Lemma lem1696085 (M : real) (M' : real) : (term510 M M') = (term511 M M').
Proof. exact (fun_ext (fun n : nat => @lem1696084 n M M')). Qed.
Lemma lem1696086 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1696087 (M : real) (M' : real) : (term500 M M') = (term512 M M').
Proof. exact (MK_COMB (@lem1696086) (@lem1696085 M M')). Qed.
Lemma lem1696088 (M : real) (M' : real) : ((term499 M M') = (term500 M M')) = ((term429 M M') = (term512 M M')).
Proof. exact (MK_COMB (@lem1696079 M M') (@lem1696087 M M')). Qed.
Lemma lem1696089 (M : real) (M' : real) : (term429 M M') = (term512 M M').
Proof. exact (EQ_MP (@lem1696088 M M') (@lem1696069 M M')). Qed.
Lemma lem1696090 (M : real) : (term430 M) = (term513 M).
Proof. exact (fun_ext (fun M' : real => @lem1696089 M M')). Qed.
Lemma lem1696091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696092 (M : real) : (term431 M) = (term514 M).
Proof. exact (MK_COMB (@lem1696091) (@lem1696090 M)). Qed.
Lemma lem1696094 {A B : Type'} (P : type1413 A B) : (term458 A B P) = (term459 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1696095 (P : type1622) : (term460 P) = (term461 P).
Proof. exact (@lem1696094 real nat P). Qed.
Lemma lem1696096 (M : real) : (term515 M) = (term516 M).
Proof. exact (@lem1696095 (term517 M)). Qed.
Lemma lem1696097 (M : real) (M' : real) : (term518 M M') = (term511 M M').
Proof. exact (eq_refl (term518 M M')). Qed.
Lemma lem1696098 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1696099 (M : real) (M' : real) (n : nat) : (term519 M M' n) = (term520 M M' n).
Proof. exact (MK_COMB (@lem1696097 M M') (@lem1696098 n)). Qed.
Lemma lem1696100 (n : nat) (M : real) (M' : real) : (term520 M M' n) = (term509 n M M').
Proof. exact (eq_refl (term520 M M' n)). Qed.
Lemma lem1696101 (n : nat) (M : real) (M' : real) : (term519 M M' n) = (term509 n M M').
Proof. exact (TRANS (@lem1696099 M M' n) (@lem1696100 n M M')). Qed.
Lemma lem1696102 (M : real) (M' : real) : (term521 M M') = (term511 M M').
Proof. exact (fun_ext (fun n : nat => @lem1696101 n M M')). Qed.
Lemma lem1696103 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1696104 (M : real) (M' : real) : (term522 M M') = (term512 M M').
Proof. exact (MK_COMB (@lem1696103) (@lem1696102 M M')). Qed.
Lemma lem1696105 (M : real) : (term523 M) = (term513 M).
Proof. exact (fun_ext (fun M' : real => @lem1696104 M M')). Qed.
Lemma lem1696106 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696107 (M : real) : (term515 M) = (term514 M).
Proof. exact (MK_COMB (@lem1696106) (@lem1696105 M)). Qed.
Lemma lem1696108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696109 (M : real) : (term524 M) = (term525 M).
Proof. exact (MK_COMB (@lem1696108) (@lem1696107 M)). Qed.
Lemma lem1696110 (M : real) (M' : real) : (term518 M M') = (term511 M M').
Proof. exact (eq_refl (term518 M M')). Qed.
Lemma lem1696111 (n : real -> nat) (M' : real) : (n M') = (n M').
Proof. exact (eq_refl (n M')). Qed.
Lemma lem1696112 (M : real) (n : real -> nat) (M' : real) : (term526 M n M') = (term527 M n M').
Proof. exact (MK_COMB (@lem1696110 M M') (@lem1696111 n M')). Qed.
Lemma lem1696113 (n : real -> nat) (M : real) (M' : real) : (term527 M n M') = (term528 n M M').
Proof. exact (eq_refl (term527 M n M')). Qed.
Lemma lem1696114 (n : real -> nat) (M : real) (M' : real) : (term526 M n M') = (term528 n M M').
Proof. exact (TRANS (@lem1696112 M n M') (@lem1696113 n M M')). Qed.
Lemma lem1696115 (n : real -> nat) (M : real) : (term529 M n) = (term530 n M).
Proof. exact (fun_ext (fun M' : real => @lem1696114 n M M')). Qed.
Lemma lem1696116 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696117 (n : real -> nat) (M : real) : (term531 M n) = (term532 n M).
Proof. exact (MK_COMB (@lem1696116) (@lem1696115 n M)). Qed.
Lemma lem1696118 (M : real) : (term533 M) = (term534 M).
Proof. exact (fun_ext (fun n : real -> nat => @lem1696117 n M)). Qed.
Lemma lem1696119 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696120 (M : real) : (term516 M) = (term535 M).
Proof. exact (MK_COMB (@lem1696119) (@lem1696118 M)). Qed.
Lemma lem1696121 (M : real) : ((term515 M) = (term516 M)) = ((term514 M) = (term535 M)).
Proof. exact (MK_COMB (@lem1696109 M) (@lem1696120 M)). Qed.
Lemma lem1696122 (M : real) : (term514 M) = (term535 M).
Proof. exact (EQ_MP (@lem1696121 M) (@lem1696096 M)). Qed.
Lemma lem1696123 (M : real) : (term431 M) = (term535 M).
Proof. exact (TRANS (@lem1696092 M) (@lem1696122 M)). Qed.
Lemma lem1696124 (M : real) : (term334 M) = (term334 M).
Proof. exact (eq_refl (term334 M)). Qed.
Lemma lem1696125 (M : real) : (term432 M) = (term536 M).
Proof. exact (MK_COMB (@lem1696124 M) (@lem1696123 M)). Qed.
Lemma lem1696127 {A : Type'} (P : Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1696128 (P : Prop) (Q : type1024) : (term537 P Q) = (term538 P Q).
Proof. exact (@lem1696127 (real -> nat) P Q). Qed.
Lemma lem1696129 (M : real) : (term539 M) = (term540 M).
Proof. exact (@lem1696128 (term324 M) (term534 M)). Qed.
Lemma lem1696130 (n : real -> nat) (M : real) : (term541 M n) = (term532 n M).
Proof. exact (eq_refl (term541 M n)). Qed.
Lemma lem1696131 (M : real) : (term542 M) = (term534 M).
Proof. exact (fun_ext (fun n : real -> nat => @lem1696130 n M)). Qed.
Lemma lem1696132 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696133 (M : real) : (term543 M) = (term535 M).
Proof. exact (MK_COMB (@lem1696132) (@lem1696131 M)). Qed.
Lemma lem1696134 (M : real) : (term334 M) = (term334 M).
Proof. exact (eq_refl (term334 M)). Qed.
Lemma lem1696135 (M : real) : (term539 M) = (term536 M).
Proof. exact (MK_COMB (@lem1696134 M) (@lem1696133 M)). Qed.
Lemma lem1696136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696137 (M : real) : (term544 M) = (term545 M).
Proof. exact (MK_COMB (@lem1696136) (@lem1696135 M)). Qed.
Lemma lem1696138 (n : real -> nat) (M : real) : (term541 M n) = (term532 n M).
Proof. exact (eq_refl (term541 M n)). Qed.
Lemma lem1696139 (M : real) : (term334 M) = (term334 M).
Proof. exact (eq_refl (term334 M)). Qed.
Lemma lem1696140 (n : real -> nat) (M : real) : (term546 M n) = (term547 n M).
Proof. exact (MK_COMB (@lem1696139 M) (@lem1696138 n M)). Qed.
Lemma lem1696141 (M : real) : (term548 M) = (term549 M).
Proof. exact (fun_ext (fun n : real -> nat => @lem1696140 n M)). Qed.
Lemma lem1696142 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696143 (M : real) : (term540 M) = (term550 M).
Proof. exact (MK_COMB (@lem1696142) (@lem1696141 M)). Qed.
Lemma lem1696144 (M : real) : ((term539 M) = (term540 M)) = ((term536 M) = (term550 M)).
Proof. exact (MK_COMB (@lem1696137 M) (@lem1696143 M)). Qed.
Lemma lem1696145 (M : real) : (term536 M) = (term550 M).
Proof. exact (EQ_MP (@lem1696144 M) (@lem1696129 M)). Qed.
Lemma lem1696146 (M : real) : (term432 M) = (term550 M).
Proof. exact (TRANS (@lem1696125 M) (@lem1696145 M)). Qed.
Lemma lem1696147 : term433 = term551.
Proof. exact (fun_ext (fun M : real => @lem1696146 M)). Qed.
Lemma lem1696148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696149 : term434 = term552.
Proof. exact (MK_COMB (@lem1696148) (@lem1696147)). Qed.
Lemma lem1696150 : term438 = term553.
Proof. exact (MK_COMB (@lem1696065) (@lem1696149)). Qed.
Lemma lem1696154 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1696155 (P : type1024) (Q : Prop) : (term554 P Q) = (term555 P Q).
Proof. exact (@lem1696154 (real -> nat) P Q). Qed.
Lemma lem1696156 : term556 = term557.
Proof. exact (@lem1696155 term496 term552). Qed.
Lemma lem1696157 (n : real -> nat) : (term558 n) = (term494 n).
Proof. exact (eq_refl (term558 n)). Qed.
Lemma lem1696158 : term559 = term496.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696157 n)). Qed.
Lemma lem1696159 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696160 : term560 = term497.
Proof. exact (MK_COMB (@lem1696159) (@lem1696158)). Qed.
Lemma lem1696161 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1696162 : term561 = term498.
Proof. exact (MK_COMB (@lem1696161) (@lem1696160)). Qed.
Lemma lem1696163 : term552 = term552.
Proof. exact (eq_refl term552). Qed.
Lemma lem1696164 : term556 = term553.
Proof. exact (MK_COMB (@lem1696162) (@lem1696163)). Qed.
Lemma lem1696165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696166 : term562 = term563.
Proof. exact (MK_COMB (@lem1696165) (@lem1696164)). Qed.
Lemma lem1696167 (n : real -> nat) : (term558 n) = (term494 n).
Proof. exact (eq_refl (term558 n)). Qed.
Lemma lem1696168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1696169 (n : real -> nat) : (term564 n) = (term565 n).
Proof. exact (MK_COMB (@lem1696168) (@lem1696167 n)). Qed.
Lemma lem1696170 : term552 = term552.
Proof. exact (eq_refl term552). Qed.
Lemma lem1696171 (n : real -> nat) : (term566 n) = (term567 n).
Proof. exact (MK_COMB (@lem1696169 n) (@lem1696170)). Qed.
Lemma lem1696172 : term568 = term569.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696171 n)). Qed.
Lemma lem1696173 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696174 : term557 = term570.
Proof. exact (MK_COMB (@lem1696173) (@lem1696172)). Qed.
Lemma lem1696175 : (term556 = term557) = (term553 = term570).
Proof. exact (MK_COMB (@lem1696166) (@lem1696174)). Qed.
Lemma lem1696176 : term553 = term570.
Proof. exact (EQ_MP (@lem1696175) (@lem1696156)). Qed.
Lemma lem1696178 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1696179 (P : Prop) (Q : real -> Prop) : (term168 P Q) = (term169 P Q).
Proof. exact (@lem1696178 real P Q). Qed.
Lemma lem1696180 (n : real -> nat) : (term571 n) = (term572 n).
Proof. exact (@lem1696179 (term494 n) term551). Qed.
Lemma lem1696181 (M : real) : (term573 M) = (term550 M).
Proof. exact (eq_refl (term573 M)). Qed.
Lemma lem1696182 : term574 = term551.
Proof. exact (fun_ext (fun M : real => @lem1696181 M)). Qed.
Lemma lem1696183 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696184 : term575 = term552.
Proof. exact (MK_COMB (@lem1696183) (@lem1696182)). Qed.
Lemma lem1696185 (n : real -> nat) : (term565 n) = (term565 n).
Proof. exact (eq_refl (term565 n)). Qed.
Lemma lem1696186 (n : real -> nat) : (term571 n) = (term567 n).
Proof. exact (MK_COMB (@lem1696185 n) (@lem1696184)). Qed.
Lemma lem1696187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696188 (n : real -> nat) : (term576 n) = (term577 n).
Proof. exact (MK_COMB (@lem1696187) (@lem1696186 n)). Qed.
Lemma lem1696189 (M : real) : (term573 M) = (term550 M).
Proof. exact (eq_refl (term573 M)). Qed.
Lemma lem1696190 (n : real -> nat) : (term565 n) = (term565 n).
Proof. exact (eq_refl (term565 n)). Qed.
Lemma lem1696191 (n : real -> nat) (M : real) : (term578 n M) = (term579 n M).
Proof. exact (MK_COMB (@lem1696190 n) (@lem1696189 M)). Qed.
Lemma lem1696192 (n : real -> nat) : (term580 n) = (term581 n).
Proof. exact (fun_ext (fun M : real => @lem1696191 n M)). Qed.
Lemma lem1696193 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696194 (n : real -> nat) : (term572 n) = (term582 n).
Proof. exact (MK_COMB (@lem1696193) (@lem1696192 n)). Qed.
Lemma lem1696195 (n : real -> nat) : ((term571 n) = (term572 n)) = ((term567 n) = (term582 n)).
Proof. exact (MK_COMB (@lem1696188 n) (@lem1696194 n)). Qed.
Lemma lem1696196 (n : real -> nat) : (term567 n) = (term582 n).
Proof. exact (EQ_MP (@lem1696195 n) (@lem1696180 n)). Qed.
Lemma lem1696198 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1696199 (P : Prop) (Q : type1024) : (term484 P Q) = (term485 P Q).
Proof. exact (@lem1696198 (real -> nat) P Q). Qed.
Lemma lem1696200 (n : real -> nat) (M : real) : (term583 n M) = (term584 n M).
Proof. exact (@lem1696199 (term494 n) (term549 M)). Qed.
Lemma lem1696201 (n : real -> nat) (M : real) : (term585 M n) = (term547 n M).
Proof. exact (eq_refl (term585 M n)). Qed.
Lemma lem1696202 (M : real) : (term586 M) = (term549 M).
Proof. exact (fun_ext (fun n : real -> nat => @lem1696201 n M)). Qed.
Lemma lem1696203 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696204 (M : real) : (term587 M) = (term550 M).
Proof. exact (MK_COMB (@lem1696203) (@lem1696202 M)). Qed.
Lemma lem1696205 (n : real -> nat) : (term565 n) = (term565 n).
Proof. exact (eq_refl (term565 n)). Qed.
Lemma lem1696206 (n : real -> nat) (M : real) : (term583 n M) = (term579 n M).
Proof. exact (MK_COMB (@lem1696205 n) (@lem1696204 M)). Qed.
Lemma lem1696207 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696208 (n : real -> nat) (M : real) : (term588 n M) = (term589 n M).
Proof. exact (MK_COMB (@lem1696207) (@lem1696206 n M)). Qed.
Lemma lem1696209 (n' : real -> nat) (M : real) : (term585 M n') = (term547 n' M).
Proof. exact (eq_refl (term585 M n')). Qed.
Lemma lem1696210 (n : real -> nat) : (term565 n) = (term565 n).
Proof. exact (eq_refl (term565 n)). Qed.
Lemma lem1696211 (n : real -> nat) (n' : real -> nat) (M : real) : (term590 n M n') = (term591 n n' M).
Proof. exact (MK_COMB (@lem1696210 n) (@lem1696209 n' M)). Qed.
Lemma lem1696212 (n : real -> nat) (M : real) : (term592 n M) = (term593 n M).
Proof. exact (fun_ext (fun n' : real -> nat => @lem1696211 n n' M)). Qed.
Lemma lem1696213 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696214 (n : real -> nat) (M : real) : (term584 n M) = (term594 n M).
Proof. exact (MK_COMB (@lem1696213) (@lem1696212 n M)). Qed.
Lemma lem1696215 (n : real -> nat) (M : real) : ((term583 n M) = (term584 n M)) = ((term579 n M) = (term594 n M)).
Proof. exact (MK_COMB (@lem1696208 n M) (@lem1696214 n M)). Qed.
Lemma lem1696216 (n : real -> nat) (M : real) : (term579 n M) = (term594 n M).
Proof. exact (EQ_MP (@lem1696215 n M) (@lem1696200 n M)). Qed.
Lemma lem1696217 (n : real -> nat) : (term581 n) = (term595 n).
Proof. exact (fun_ext (fun M : real => @lem1696216 n M)). Qed.
Lemma lem1696218 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696219 (n : real -> nat) : (term582 n) = (term596 n).
Proof. exact (MK_COMB (@lem1696218) (@lem1696217 n)). Qed.
Lemma lem1696220 (n : real -> nat) : (term567 n) = (term596 n).
Proof. exact (TRANS (@lem1696196 n) (@lem1696219 n)). Qed.
Lemma lem1696221 : term569 = term597.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696220 n)). Qed.
Lemma lem1696222 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696223 : term570 = term598.
Proof. exact (MK_COMB (@lem1696222) (@lem1696221)). Qed.
Lemma lem1696224 : term553 = term598.
Proof. exact (TRANS (@lem1696176) (@lem1696223)). Qed.
Lemma lem1696225 : term438 = term598.
Proof. exact (TRANS (@lem1696150) (@lem1696224)). Qed.
Lemma lem1696226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696227 : term455 = term599.
Proof. exact (MK_COMB (@lem1696226) (@lem1696225)). Qed.
Lemma lem1696228 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem1696229 : term457 = term600.
Proof. exact (MK_COMB (@lem1696227) (@lem1696228)). Qed.
Lemma lem1696231 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1696232 (P : type1024) (Q : Prop) : (term601 P Q) = (term602 P Q).
Proof. exact (@lem1696231 (real -> nat) P Q). Qed.
Lemma lem1696233 : term603 = term604.
Proof. exact (@lem1696232 term597 term453). Qed.
Lemma lem1696234 (n : real -> nat) : (term605 n) = (term596 n).
Proof. exact (eq_refl (term605 n)). Qed.
Lemma lem1696235 : term606 = term597.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696234 n)). Qed.
Lemma lem1696236 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696237 : term607 = term598.
Proof. exact (MK_COMB (@lem1696236) (@lem1696235)). Qed.
Lemma lem1696238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696239 : term608 = term599.
Proof. exact (MK_COMB (@lem1696238) (@lem1696237)). Qed.
Lemma lem1696240 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem1696241 : term603 = term600.
Proof. exact (MK_COMB (@lem1696239) (@lem1696240)). Qed.
Lemma lem1696242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696243 : term609 = term610.
Proof. exact (MK_COMB (@lem1696242) (@lem1696241)). Qed.
Lemma lem1696244 (n : real -> nat) : (term605 n) = (term596 n).
Proof. exact (eq_refl (term605 n)). Qed.
Lemma lem1696245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696246 (n : real -> nat) : (term611 n) = (term612 n).
Proof. exact (MK_COMB (@lem1696245) (@lem1696244 n)). Qed.
Lemma lem1696247 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem1696248 (n : real -> nat) : (term613 n) = (term614 n).
Proof. exact (MK_COMB (@lem1696246 n) (@lem1696247)). Qed.
Lemma lem1696249 : term615 = term616.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696248 n)). Qed.
Lemma lem1696250 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696251 : term604 = term617.
Proof. exact (MK_COMB (@lem1696250) (@lem1696249)). Qed.
Lemma lem1696252 : (term603 = term604) = (term600 = term617).
Proof. exact (MK_COMB (@lem1696243) (@lem1696251)). Qed.
Lemma lem1696253 : term600 = term617.
Proof. exact (EQ_MP (@lem1696252) (@lem1696233)). Qed.
Lemma lem1696255 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1696256 (P : real -> Prop) (Q : Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem1696255 real P Q). Qed.
Lemma lem1696257 (n : real -> nat) : (term618 n) = (term619 n).
Proof. exact (@lem1696256 (term595 n) term453). Qed.
Lemma lem1696258 (n : real -> nat) (M : real) : (term620 n M) = (term594 n M).
Proof. exact (eq_refl (term620 n M)). Qed.
Lemma lem1696259 (n : real -> nat) : (term621 n) = (term595 n).
Proof. exact (fun_ext (fun M : real => @lem1696258 n M)). Qed.
Lemma lem1696260 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696261 (n : real -> nat) : (term622 n) = (term596 n).
Proof. exact (MK_COMB (@lem1696260) (@lem1696259 n)). Qed.
Lemma lem1696262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696263 (n : real -> nat) : (term623 n) = (term612 n).
Proof. exact (MK_COMB (@lem1696262) (@lem1696261 n)). Qed.
Lemma lem1696264 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem1696265 (n : real -> nat) : (term618 n) = (term614 n).
Proof. exact (MK_COMB (@lem1696263 n) (@lem1696264)). Qed.
Lemma lem1696266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696267 (n : real -> nat) : (term624 n) = (term625 n).
Proof. exact (MK_COMB (@lem1696266) (@lem1696265 n)). Qed.
Lemma lem1696268 (n : real -> nat) (M : real) : (term620 n M) = (term594 n M).
Proof. exact (eq_refl (term620 n M)). Qed.
Lemma lem1696269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696270 (n : real -> nat) (M : real) : (term626 n M) = (term627 n M).
Proof. exact (MK_COMB (@lem1696269) (@lem1696268 n M)). Qed.
Lemma lem1696271 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem1696272 (n : real -> nat) (M : real) : (term628 n M) = (term629 n M).
Proof. exact (MK_COMB (@lem1696270 n M) (@lem1696271)). Qed.
Lemma lem1696273 (n : real -> nat) : (term630 n) = (term631 n).
Proof. exact (fun_ext (fun M : real => @lem1696272 n M)). Qed.
Lemma lem1696274 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696275 (n : real -> nat) : (term619 n) = (term632 n).
Proof. exact (MK_COMB (@lem1696274) (@lem1696273 n)). Qed.
Lemma lem1696276 (n : real -> nat) : ((term618 n) = (term619 n)) = ((term614 n) = (term632 n)).
Proof. exact (MK_COMB (@lem1696267 n) (@lem1696275 n)). Qed.
Lemma lem1696277 (n : real -> nat) : (term614 n) = (term632 n).
Proof. exact (EQ_MP (@lem1696276 n) (@lem1696257 n)). Qed.
Lemma lem1696279 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1696280 (P : type1024) (Q : Prop) : (term601 P Q) = (term602 P Q).
Proof. exact (@lem1696279 (real -> nat) P Q). Qed.
Lemma lem1696281 (n : real -> nat) (M : real) : (term633 n M) = (term634 n M).
Proof. exact (@lem1696280 (term593 n M) term453). Qed.
Lemma lem1696282 (n : real -> nat) (n' : real -> nat) (M : real) : (term635 n M n') = (term591 n n' M).
Proof. exact (eq_refl (term635 n M n')). Qed.
Lemma lem1696283 (n : real -> nat) (M : real) : (term636 n M) = (term593 n M).
Proof. exact (fun_ext (fun n' : real -> nat => @lem1696282 n n' M)). Qed.
Lemma lem1696284 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696285 (n : real -> nat) (M : real) : (term637 n M) = (term594 n M).
Proof. exact (MK_COMB (@lem1696284) (@lem1696283 n M)). Qed.
Lemma lem1696286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696287 (n : real -> nat) (M : real) : (term638 n M) = (term627 n M).
Proof. exact (MK_COMB (@lem1696286) (@lem1696285 n M)). Qed.
Lemma lem1696288 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem1696289 (n : real -> nat) (M : real) : (term633 n M) = (term629 n M).
Proof. exact (MK_COMB (@lem1696287 n M) (@lem1696288)). Qed.
Lemma lem1696290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696291 (n : real -> nat) (M : real) : (term639 n M) = (term640 n M).
Proof. exact (MK_COMB (@lem1696290) (@lem1696289 n M)). Qed.
Lemma lem1696292 (n : real -> nat) (n' : real -> nat) (M : real) : (term635 n M n') = (term591 n n' M).
Proof. exact (eq_refl (term635 n M n')). Qed.
Lemma lem1696293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696294 (n : real -> nat) (n' : real -> nat) (M : real) : (term641 n M n') = (term642 n n' M).
Proof. exact (MK_COMB (@lem1696293) (@lem1696292 n n' M)). Qed.
Lemma lem1696295 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem1696296 (n : real -> nat) (n' : real -> nat) (M : real) : (term643 n M n') = (term644 n n' M).
Proof. exact (MK_COMB (@lem1696294 n n' M) (@lem1696295)). Qed.
Lemma lem1696297 (n : real -> nat) (M : real) : (term645 n M) = (term646 n M).
Proof. exact (fun_ext (fun n' : real -> nat => @lem1696296 n n' M)). Qed.
Lemma lem1696298 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696299 (n : real -> nat) (M : real) : (term634 n M) = (term647 n M).
Proof. exact (MK_COMB (@lem1696298) (@lem1696297 n M)). Qed.
Lemma lem1696300 (n : real -> nat) (M : real) : ((term633 n M) = (term634 n M)) = ((term629 n M) = (term647 n M)).
Proof. exact (MK_COMB (@lem1696291 n M) (@lem1696299 n M)). Qed.
Lemma lem1696301 (n : real -> nat) (M : real) : (term629 n M) = (term647 n M).
Proof. exact (EQ_MP (@lem1696300 n M) (@lem1696281 n M)). Qed.
Lemma lem1696303 {A : Type'} (P : Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1696304 (P : Prop) (Q : real -> Prop) : (term648 P Q) = (term649 P Q).
Proof. exact (@lem1696303 real P Q). Qed.
Lemma lem1696305 (n : real -> nat) (n' : real -> nat) (M : real) : (term650 n n' M) = (term651 n n' M).
Proof. exact (@lem1696304 (term591 n n' M) term452). Qed.
Lemma lem1696306 (x : real) : (term652 x) = (term446 x).
Proof. exact (eq_refl (term652 x)). Qed.
Lemma lem1696307 : term653 = term452.
Proof. exact (fun_ext (fun x : real => @lem1696306 x)). Qed.
Lemma lem1696308 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696309 : term654 = term453.
Proof. exact (MK_COMB (@lem1696308) (@lem1696307)). Qed.
Lemma lem1696310 (n : real -> nat) (n' : real -> nat) (M : real) : (term642 n n' M) = (term642 n n' M).
Proof. exact (eq_refl (term642 n n' M)). Qed.
Lemma lem1696311 (n : real -> nat) (n' : real -> nat) (M : real) : (term650 n n' M) = (term644 n n' M).
Proof. exact (MK_COMB (@lem1696310 n n' M) (@lem1696309)). Qed.
Lemma lem1696312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696313 (n : real -> nat) (n' : real -> nat) (M : real) : (term655 n n' M) = (term656 n n' M).
Proof. exact (MK_COMB (@lem1696312) (@lem1696311 n n' M)). Qed.
Lemma lem1696314 (x : real) : (term652 x) = (term446 x).
Proof. exact (eq_refl (term652 x)). Qed.
Lemma lem1696315 (n : real -> nat) (n' : real -> nat) (M : real) : (term642 n n' M) = (term642 n n' M).
Proof. exact (eq_refl (term642 n n' M)). Qed.
Lemma lem1696316 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) : (term657 n n' M x) = (term658 n n' M x).
Proof. exact (MK_COMB (@lem1696315 n n' M) (@lem1696314 x)). Qed.
Lemma lem1696317 (n : real -> nat) (n' : real -> nat) (M : real) : (term659 n n' M) = (term660 n n' M).
Proof. exact (fun_ext (fun x : real => @lem1696316 n n' M x)). Qed.
Lemma lem1696318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696319 (n : real -> nat) (n' : real -> nat) (M : real) : (term651 n n' M) = (term661 n n' M).
Proof. exact (MK_COMB (@lem1696318) (@lem1696317 n n' M)). Qed.
Lemma lem1696320 (n : real -> nat) (n' : real -> nat) (M : real) : ((term650 n n' M) = (term651 n n' M)) = ((term644 n n' M) = (term661 n n' M)).
Proof. exact (MK_COMB (@lem1696313 n n' M) (@lem1696319 n n' M)). Qed.
Lemma lem1696321 (n : real -> nat) (n' : real -> nat) (M : real) : (term644 n n' M) = (term661 n n' M).
Proof. exact (EQ_MP (@lem1696320 n n' M) (@lem1696305 n n' M)). Qed.
Lemma lem1696322 (n : real -> nat) (M : real) : (term646 n M) = (term662 n M).
Proof. exact (fun_ext (fun n' : real -> nat => @lem1696321 n n' M)). Qed.
Lemma lem1696323 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696324 (n : real -> nat) (M : real) : (term647 n M) = (term663 n M).
Proof. exact (MK_COMB (@lem1696323) (@lem1696322 n M)). Qed.
Lemma lem1696325 (n : real -> nat) (M : real) : (term629 n M) = (term663 n M).
Proof. exact (TRANS (@lem1696301 n M) (@lem1696324 n M)). Qed.
Lemma lem1696326 (n : real -> nat) : (term631 n) = (term664 n).
Proof. exact (fun_ext (fun M : real => @lem1696325 n M)). Qed.
Lemma lem1696327 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1696328 (n : real -> nat) : (term632 n) = (term665 n).
Proof. exact (MK_COMB (@lem1696327) (@lem1696326 n)). Qed.
Lemma lem1696329 (n : real -> nat) : (term614 n) = (term665 n).
Proof. exact (TRANS (@lem1696277 n) (@lem1696328 n)). Qed.
Lemma lem1696330 : term616 = term666.
Proof. exact (fun_ext (fun n : real -> nat => @lem1696329 n)). Qed.
Lemma lem1696331 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1696332 : term617 = term667.
Proof. exact (MK_COMB (@lem1696331) (@lem1696330)). Qed.
Lemma lem1696333 : term600 = term667.
Proof. exact (TRANS (@lem1696253) (@lem1696332)). Qed.
Lemma lem1696335 : term457 = term667.
Proof. exact (TRANS (@lem1696229) (@lem1696333)). Qed.
Lemma lem1696336 : term356 = term667.
Proof. exact (TRANS (@lem1695881) (@lem1696335)). Qed.
Lemma lem1696337 (h1 : term356) : term667.
Proof. exact (EQ_MP (@lem1696336) (@lem1695769 h1)). Qed.
Lemma lem1696338 (M : real) : (term289 M) = (term289 M).
Proof. exact (eq_refl (term289 M)). Qed.
Lemma lem1696339 : term393 = term393.
Proof. exact (fun_ext (fun M : real => @lem1696338 M)). Qed.
Lemma lem1696340 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696349 : term290 = term290.
Proof. exact (MK_COMB (@lem1696340) (@lem1696339)). Qed.
Lemma lem1696350 (h1 : term290) : term290.
Proof. exact (EQ_MP (@lem1696349) (@lem1695770 h1)). Qed.
Lemma lem1696355 (y : real) (x : real) : (term388 y x) = (term388 y x).
Proof. exact (eq_refl (term388 y x)). Qed.
Lemma lem1696356 (x : real) : (term389 x) = (term389 x).
Proof. exact (fun_ext (fun y : real => @lem1696355 y x)). Qed.
Lemma lem1696357 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696358 (x : real) : (term390 x) = (term390 x).
Proof. exact (MK_COMB (@lem1696357) (@lem1696356 x)). Qed.
Lemma lem1696359 : term391 = term391.
Proof. exact (fun_ext (fun x : real => @lem1696358 x)). Qed.
Lemma lem1696360 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696417 : term392 = term392.
Proof. exact (MK_COMB (@lem1696360) (@lem1696359)). Qed.
Lemma lem1696418 (h1 : term392) : term392.
Proof. exact (EQ_MP (@lem1696417) (@lem1695771 h1)). Qed.
Lemma lem1696419 (m : nat) (n : nat) : ((term382 m n) = (term383 m n)) = ((term382 m n) = (term383 m n)).
Proof. exact (eq_refl ((term382 m n) = (term383 m n))). Qed.
Lemma lem1696420 (m : nat) : (term384 m) = (term384 m).
Proof. exact (fun_ext (fun n : nat => @lem1696419 m n)). Qed.
Lemma lem1696421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1696422 (m : nat) : (term385 m) = (term385 m).
Proof. exact (MK_COMB (@lem1696421) (@lem1696420 m)). Qed.
Lemma lem1696423 : term386 = term386.
Proof. exact (fun_ext (fun m : nat => @lem1696422 m)). Qed.
Lemma lem1696424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1696437 : term387 = term387.
Proof. exact (MK_COMB (@lem1696424) (@lem1696423)). Qed.
Lemma lem1696438 (h1 : term387) : term387.
Proof. exact (EQ_MP (@lem1696437) (@lem1695772 h1)). Qed.
Lemma lem1696453 (x : real) (z : real) (y : real) : ((term375 x y z) = (term376 x z y)) = (term668 x z y).
Proof. exact (@lem17784 (term375 x y z) (term376 x z y)). Qed.
Lemma lem1696454 (x : real) (y : real) : (term377 x y) = (term669 x y).
Proof. exact (fun_ext (fun z : real => @lem1696453 x z y)). Qed.
Lemma lem1696455 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696456 (x : real) (y : real) : (term378 x y) = (term670 x y).
Proof. exact (MK_COMB (@lem1696455) (@lem1696454 x y)). Qed.
Lemma lem1696457 (x : real) : (term379 x) = (term671 x).
Proof. exact (fun_ext (fun y : real => @lem1696456 x y)). Qed.
Lemma lem1696458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696459 (x : real) : (term380 x) = (term672 x).
Proof. exact (MK_COMB (@lem1696458) (@lem1696457 x)). Qed.
Lemma lem1696460 : term381 = term673.
Proof. exact (fun_ext (fun x : real => @lem1696459 x)). Qed.
Lemma lem1696461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696462 : term363 = term674.
Proof. exact (MK_COMB (@lem1696461) (@lem1696460)). Qed.
Lemma lem1696472 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term675 A P Q) = (term676 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1696473 (P : real -> Prop) (Q : real -> Prop) : (term677 P Q) = (term678 P Q).
Proof. exact (@lem1696472 real P Q). Qed.
Lemma lem1696474 (x : real) (y : real) : (term679 x y) = (term680 x y).
Proof. exact (@lem1696473 (term681 x y) (term682 x y)). Qed.
Lemma lem1696475 (x : real) (z : real) (y : real) : (term683 x y z) = (term684 x z y).
Proof. exact (eq_refl (term683 x y z)). Qed.
Lemma lem1696476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696477 (x : real) (z : real) (y : real) : (term685 x y z) = (term686 x z y).
Proof. exact (MK_COMB (@lem1696476) (@lem1696475 x z y)). Qed.
Lemma lem1696478 (x : real) (z : real) (y : real) : (term687 x y z) = (term688 x z y).
Proof. exact (eq_refl (term687 x y z)). Qed.
Lemma lem1696479 (x : real) (z : real) (y : real) : (term689 x y z) = (term668 x z y).
Proof. exact (MK_COMB (@lem1696477 x z y) (@lem1696478 x z y)). Qed.
Lemma lem1696480 (x : real) (y : real) : (term690 x y) = (term669 x y).
Proof. exact (fun_ext (fun z : real => @lem1696479 x z y)). Qed.
Lemma lem1696481 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696482 (x : real) (y : real) : (term679 x y) = (term670 x y).
Proof. exact (MK_COMB (@lem1696481) (@lem1696480 x y)). Qed.
Lemma lem1696483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696484 (x : real) (y : real) : (term691 x y) = (term692 x y).
Proof. exact (MK_COMB (@lem1696483) (@lem1696482 x y)). Qed.
Lemma lem1696485 (x : real) (z : real) (y : real) : (term683 x y z) = (term684 x z y).
Proof. exact (eq_refl (term683 x y z)). Qed.
Lemma lem1696486 (x : real) (y : real) : (term693 x y) = (term681 x y).
Proof. exact (fun_ext (fun z : real => @lem1696485 x z y)). Qed.
Lemma lem1696487 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696488 (x : real) (y : real) : (term694 x y) = (term695 x y).
Proof. exact (MK_COMB (@lem1696487) (@lem1696486 x y)). Qed.
Lemma lem1696489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696490 (x : real) (y : real) : (term696 x y) = (term697 x y).
Proof. exact (MK_COMB (@lem1696489) (@lem1696488 x y)). Qed.
Lemma lem1696491 (x : real) (z : real) (y : real) : (term687 x y z) = (term688 x z y).
Proof. exact (eq_refl (term687 x y z)). Qed.
Lemma lem1696492 (x : real) (y : real) : (term698 x y) = (term682 x y).
Proof. exact (fun_ext (fun z : real => @lem1696491 x z y)). Qed.
Lemma lem1696493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696494 (x : real) (y : real) : (term699 x y) = (term700 x y).
Proof. exact (MK_COMB (@lem1696493) (@lem1696492 x y)). Qed.
Lemma lem1696495 (x : real) (y : real) : (term680 x y) = (term701 x y).
Proof. exact (MK_COMB (@lem1696490 x y) (@lem1696494 x y)). Qed.
Lemma lem1696496 (x : real) (y : real) : ((term679 x y) = (term680 x y)) = ((term670 x y) = (term701 x y)).
Proof. exact (MK_COMB (@lem1696484 x y) (@lem1696495 x y)). Qed.
Lemma lem1696497 (x : real) (y : real) : (term670 x y) = (term701 x y).
Proof. exact (EQ_MP (@lem1696496 x y) (@lem1696474 x y)). Qed.
Lemma lem1696594 (x : real) : (term671 x) = (term702 x).
Proof. exact (fun_ext (fun y : real => @lem1696497 x y)). Qed.
Lemma lem1696595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696596 (x : real) : (term672 x) = (term703 x).
Proof. exact (MK_COMB (@lem1696595) (@lem1696594 x)). Qed.
Lemma lem1696598 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term675 A P Q) = (term676 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1696599 (P : real -> Prop) (Q : real -> Prop) : (term677 P Q) = (term678 P Q).
Proof. exact (@lem1696598 real P Q). Qed.
Lemma lem1696600 (x : real) : (term704 x) = (term705 x).
Proof. exact (@lem1696599 (term706 x) (term707 x)). Qed.
Lemma lem1696601 (x : real) (y : real) : (term708 x y) = (term695 x y).
Proof. exact (eq_refl (term708 x y)). Qed.
Lemma lem1696602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696603 (x : real) (y : real) : (term709 x y) = (term697 x y).
Proof. exact (MK_COMB (@lem1696602) (@lem1696601 x y)). Qed.
Lemma lem1696604 (x : real) (y : real) : (term710 x y) = (term700 x y).
Proof. exact (eq_refl (term710 x y)). Qed.
Lemma lem1696605 (x : real) (y : real) : (term711 x y) = (term701 x y).
Proof. exact (MK_COMB (@lem1696603 x y) (@lem1696604 x y)). Qed.
Lemma lem1696606 (x : real) : (term712 x) = (term702 x).
Proof. exact (fun_ext (fun y : real => @lem1696605 x y)). Qed.
Lemma lem1696607 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696608 (x : real) : (term704 x) = (term703 x).
Proof. exact (MK_COMB (@lem1696607) (@lem1696606 x)). Qed.
Lemma lem1696609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696610 (x : real) : (term713 x) = (term714 x).
Proof. exact (MK_COMB (@lem1696609) (@lem1696608 x)). Qed.
Lemma lem1696611 (x : real) (y : real) : (term708 x y) = (term695 x y).
Proof. exact (eq_refl (term708 x y)). Qed.
Lemma lem1696612 (x : real) : (term715 x) = (term706 x).
Proof. exact (fun_ext (fun y : real => @lem1696611 x y)). Qed.
Lemma lem1696613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696614 (x : real) : (term716 x) = (term717 x).
Proof. exact (MK_COMB (@lem1696613) (@lem1696612 x)). Qed.
Lemma lem1696615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696616 (x : real) : (term718 x) = (term719 x).
Proof. exact (MK_COMB (@lem1696615) (@lem1696614 x)). Qed.
Lemma lem1696617 (x : real) (y : real) : (term710 x y) = (term700 x y).
Proof. exact (eq_refl (term710 x y)). Qed.
Lemma lem1696618 (x : real) : (term720 x) = (term707 x).
Proof. exact (fun_ext (fun y : real => @lem1696617 x y)). Qed.
Lemma lem1696619 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696620 (x : real) : (term721 x) = (term722 x).
Proof. exact (MK_COMB (@lem1696619) (@lem1696618 x)). Qed.
Lemma lem1696621 (x : real) : (term705 x) = (term723 x).
Proof. exact (MK_COMB (@lem1696616 x) (@lem1696620 x)). Qed.
Lemma lem1696622 (x : real) : ((term704 x) = (term705 x)) = ((term703 x) = (term723 x)).
Proof. exact (MK_COMB (@lem1696610 x) (@lem1696621 x)). Qed.
Lemma lem1696623 (x : real) : (term703 x) = (term723 x).
Proof. exact (EQ_MP (@lem1696622 x) (@lem1696600 x)). Qed.
Lemma lem1696728 (x : real) : (term672 x) = (term723 x).
Proof. exact (TRANS (@lem1696596 x) (@lem1696623 x)). Qed.
Lemma lem1696729 : term673 = term724.
Proof. exact (fun_ext (fun x : real => @lem1696728 x)). Qed.
Lemma lem1696730 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696731 : term674 = term725.
Proof. exact (MK_COMB (@lem1696730) (@lem1696729)). Qed.
Lemma lem1696733 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term675 A P Q) = (term676 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1696734 (P : real -> Prop) (Q : real -> Prop) : (term677 P Q) = (term678 P Q).
Proof. exact (@lem1696733 real P Q). Qed.
Lemma lem1696735 : term726 = term727.
Proof. exact (@lem1696734 term728 term729). Qed.
Lemma lem1696736 (x : real) : (term730 x) = (term717 x).
Proof. exact (eq_refl (term730 x)). Qed.
Lemma lem1696737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696738 (x : real) : (term731 x) = (term719 x).
Proof. exact (MK_COMB (@lem1696737) (@lem1696736 x)). Qed.
Lemma lem1696739 (x : real) : (term732 x) = (term722 x).
Proof. exact (eq_refl (term732 x)). Qed.
Lemma lem1696740 (x : real) : (term733 x) = (term723 x).
Proof. exact (MK_COMB (@lem1696738 x) (@lem1696739 x)). Qed.
Lemma lem1696741 : term734 = term724.
Proof. exact (fun_ext (fun x : real => @lem1696740 x)). Qed.
Lemma lem1696742 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696743 : term726 = term725.
Proof. exact (MK_COMB (@lem1696742) (@lem1696741)). Qed.
Lemma lem1696744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1696745 : term735 = term736.
Proof. exact (MK_COMB (@lem1696744) (@lem1696743)). Qed.
Lemma lem1696746 (x : real) : (term730 x) = (term717 x).
Proof. exact (eq_refl (term730 x)). Qed.
Lemma lem1696747 : term737 = term728.
Proof. exact (fun_ext (fun x : real => @lem1696746 x)). Qed.
Lemma lem1696748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696749 : term738 = term739.
Proof. exact (MK_COMB (@lem1696748) (@lem1696747)). Qed.
Lemma lem1696750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1696751 : term740 = term741.
Proof. exact (MK_COMB (@lem1696750) (@lem1696749)). Qed.
Lemma lem1696752 (x : real) : (term732 x) = (term722 x).
Proof. exact (eq_refl (term732 x)). Qed.
Lemma lem1696753 : term742 = term729.
Proof. exact (fun_ext (fun x : real => @lem1696752 x)). Qed.
Lemma lem1696754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696755 : term743 = term744.
Proof. exact (MK_COMB (@lem1696754) (@lem1696753)). Qed.
Lemma lem1696756 : term727 = term745.
Proof. exact (MK_COMB (@lem1696751) (@lem1696755)). Qed.
Lemma lem1696757 : (term726 = term727) = (term725 = term745).
Proof. exact (MK_COMB (@lem1696745) (@lem1696756)). Qed.
Lemma lem1696758 : term725 = term745.
Proof. exact (EQ_MP (@lem1696757) (@lem1696735)). Qed.
Lemma lem1696873 : term674 = term745.
Proof. exact (TRANS (@lem1696731) (@lem1696758)). Qed.
Lemma lem1696874 : term363 = term745.
Proof. exact (TRANS (@lem1696462) (@lem1696873)). Qed.
Lemma lem1696875 (h1 : term363) : term745.
Proof. exact (EQ_MP (@lem1696874) (@lem1695773 h1)). Qed.
Lemma lem1696876 (n : real -> nat) (h1 : term665 n) : term665 n.
Proof. exact (h1). Qed.
Lemma lem1696877 (n : real -> nat) (M : real) (h1 : term663 n M) : term663 n M.
Proof. exact (h1). Qed.
Lemma lem1696878 (n : real -> nat) (n' : real -> nat) (M : real) (h1 : term661 n n' M) : term661 n n' M.
Proof. exact (h1). Qed.
Lemma lem1696879 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term658 n n' M x.
Proof. exact (h1). Qed.
Lemma lem1696896 (M : real) : (term289 M) = (term289 M).
Proof. exact (eq_refl (term289 M)). Qed.
Lemma lem1696897 : term393 = term393.
Proof. exact (fun_ext (fun M : real => @lem1696896 M)). Qed.
Lemma lem1696898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696899 : term290 = term290.
Proof. exact (MK_COMB (@lem1696898) (@lem1696897)). Qed.
Lemma lem1696900 (h1 : term290) : term290.
Proof. exact (EQ_MP (@lem1696899) (@lem1696350 h1)). Qed.
Lemma lem1696913 (y : real) (x : real) : (term388 y x) = (term388 y x).
Proof. exact (eq_refl (term388 y x)). Qed.
Lemma lem1696914 (x : real) : (term389 x) = (term389 x).
Proof. exact (fun_ext (fun y : real => @lem1696913 y x)). Qed.
Lemma lem1696915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696916 (x : real) : (term390 x) = (term390 x).
Proof. exact (MK_COMB (@lem1696915) (@lem1696914 x)). Qed.
Lemma lem1696917 : term391 = term391.
Proof. exact (fun_ext (fun x : real => @lem1696916 x)). Qed.
Lemma lem1696918 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696919 : term392 = term392.
Proof. exact (MK_COMB (@lem1696918) (@lem1696917)). Qed.
Lemma lem1696920 (h1 : term392) : term392.
Proof. exact (EQ_MP (@lem1696919) (@lem1696418 h1)). Qed.
Lemma lem1696939 (m : nat) (n : nat) : ((term382 m n) = (term383 m n)) = ((term382 m n) = (term383 m n)).
Proof. exact (eq_refl ((term382 m n) = (term383 m n))). Qed.
Lemma lem1696940 (m : nat) : (term384 m) = (term384 m).
Proof. exact (fun_ext (fun n : nat => @lem1696939 m n)). Qed.
Lemma lem1696941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1696942 (m : nat) : (term385 m) = (term385 m).
Proof. exact (MK_COMB (@lem1696941) (@lem1696940 m)). Qed.
Lemma lem1696943 : term386 = term386.
Proof. exact (fun_ext (fun m : nat => @lem1696942 m)). Qed.
Lemma lem1696944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1696945 : term387 = term387.
Proof. exact (MK_COMB (@lem1696944) (@lem1696943)). Qed.
Lemma lem1696946 (h1 : term387) : term387.
Proof. exact (EQ_MP (@lem1696945) (@lem1696438 h1)). Qed.
Lemma lem1696969 (x : real) (z : real) (y : real) : (term688 x z y) = (term688 x z y).
Proof. exact (eq_refl (term688 x z y)). Qed.
Lemma lem1696970 (x : real) (y : real) : (term682 x y) = (term682 x y).
Proof. exact (fun_ext (fun z : real => @lem1696969 x z y)). Qed.
Lemma lem1696971 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696972 (x : real) (y : real) : (term700 x y) = (term700 x y).
Proof. exact (MK_COMB (@lem1696971) (@lem1696970 x y)). Qed.
Lemma lem1696973 (x : real) : (term707 x) = (term707 x).
Proof. exact (fun_ext (fun y : real => @lem1696972 x y)). Qed.
Lemma lem1696974 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696975 (x : real) : (term722 x) = (term722 x).
Proof. exact (MK_COMB (@lem1696974) (@lem1696973 x)). Qed.
Lemma lem1696976 : term729 = term729.
Proof. exact (fun_ext (fun x : real => @lem1696975 x)). Qed.
Lemma lem1696977 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1696978 : term744 = term744.
Proof. exact (MK_COMB (@lem1696977) (@lem1696976)). Qed.
Lemma lem1697001 (x : real) (z : real) (y : real) : (term684 x z y) = (term684 x z y).
Proof. exact (eq_refl (term684 x z y)). Qed.
Lemma lem1697002 (x : real) (y : real) : (term681 x y) = (term681 x y).
Proof. exact (fun_ext (fun z : real => @lem1697001 x z y)). Qed.
Lemma lem1697003 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697004 (x : real) (y : real) : (term695 x y) = (term695 x y).
Proof. exact (MK_COMB (@lem1697003) (@lem1697002 x y)). Qed.
Lemma lem1697005 (x : real) : (term706 x) = (term706 x).
Proof. exact (fun_ext (fun y : real => @lem1697004 x y)). Qed.
Lemma lem1697006 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697007 (x : real) : (term717 x) = (term717 x).
Proof. exact (MK_COMB (@lem1697006) (@lem1697005 x)). Qed.
Lemma lem1697008 : term728 = term728.
Proof. exact (fun_ext (fun x : real => @lem1697007 x)). Qed.
Lemma lem1697009 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697010 : term739 = term739.
Proof. exact (MK_COMB (@lem1697009) (@lem1697008)). Qed.
Lemma lem1697011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1697012 : term741 = term741.
Proof. exact (MK_COMB (@lem1697011) (@lem1697010)). Qed.
Lemma lem1697013 : term745 = term745.
Proof. exact (MK_COMB (@lem1697012) (@lem1696978)). Qed.
Lemma lem1697014 (h1 : term363) : term745.
Proof. exact (EQ_MP (@lem1697013) (@lem1696875 h1)). Qed.
Lemma lem1697023 (x : real) (n : nat) : (term443 x n) = (term443 x n).
Proof. exact (eq_refl (term443 x n)). Qed.
Lemma lem1697024 (x : real) : (term445 x) = (term445 x).
Proof. exact (fun_ext (fun n : nat => @lem1697023 x n)). Qed.
Lemma lem1697025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697026 (x : real) : (term446 x) = (term446 x).
Proof. exact (MK_COMB (@lem1697025) (@lem1697024 x)). Qed.
Lemma lem1697045 (n' : real -> nat) (M : real) (M' : real) : (term528 n' M M') = (term528 n' M M').
Proof. exact (eq_refl (term528 n' M M')). Qed.
Lemma lem1697046 (n' : real -> nat) (M : real) : (term530 n' M) = (term530 n' M).
Proof. exact (fun_ext (fun M' : real => @lem1697045 n' M M')). Qed.
Lemma lem1697047 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697048 (n' : real -> nat) (M : real) : (term532 n' M) = (term532 n' M).
Proof. exact (MK_COMB (@lem1697047) (@lem1697046 n' M)). Qed.
Lemma lem1697055 (n : nat) (M : real) : (term321 n M) = (term321 n M).
Proof. exact (eq_refl (term321 n M)). Qed.
Lemma lem1697056 (M : real) : (term323 M) = (term323 M).
Proof. exact (fun_ext (fun n : nat => @lem1697055 n M)). Qed.
Lemma lem1697057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697058 (M : real) : (term324 M) = (term324 M).
Proof. exact (MK_COMB (@lem1697057) (@lem1697056 M)). Qed.
Lemma lem1697059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1697060 (M : real) : (term334 M) = (term334 M).
Proof. exact (MK_COMB (@lem1697059) (@lem1697058 M)). Qed.
Lemma lem1697061 (n' : real -> nat) (M : real) : (term547 n' M) = (term547 n' M).
Proof. exact (MK_COMB (@lem1697060 M) (@lem1697048 n' M)). Qed.
Lemma lem1697072 (n : real -> nat) (M : real) : (term475 n M) = (term475 n M).
Proof. exact (eq_refl (term475 n M)). Qed.
Lemma lem1697073 (n : real -> nat) : (term477 n) = (term477 n).
Proof. exact (fun_ext (fun M : real => @lem1697072 n M)). Qed.
Lemma lem1697074 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697075 (n : real -> nat) : (term479 n) = (term479 n).
Proof. exact (MK_COMB (@lem1697074) (@lem1697073 n)). Qed.
Lemma lem1697084 (x : real) (n : nat) : (term28 x n) = (term28 x n).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem1697085 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun n : nat => @lem1697084 x n)). Qed.
Lemma lem1697086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697087 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1697086) (@lem1697085 x)). Qed.
Lemma lem1697088 : term404 = term404.
Proof. exact (fun_ext (fun x : real => @lem1697087 x)). Qed.
Lemma lem1697089 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697090 : term405 = term405.
Proof. exact (MK_COMB (@lem1697089) (@lem1697088)). Qed.
Lemma lem1697091 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1697092 : term422 = term422.
Proof. exact (MK_COMB (@lem1697091) (@lem1697090)). Qed.
Lemma lem1697093 (n : real -> nat) : (term494 n) = (term494 n).
Proof. exact (MK_COMB (@lem1697092) (@lem1697075 n)). Qed.
Lemma lem1697094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1697095 (n : real -> nat) : (term565 n) = (term565 n).
Proof. exact (MK_COMB (@lem1697094) (@lem1697093 n)). Qed.
Lemma lem1697096 (n : real -> nat) (n' : real -> nat) (M : real) : (term591 n n' M) = (term591 n n' M).
Proof. exact (MK_COMB (@lem1697095 n) (@lem1697061 n' M)). Qed.
Lemma lem1697097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1697098 (n : real -> nat) (n' : real -> nat) (M : real) : (term642 n n' M) = (term642 n n' M).
Proof. exact (MK_COMB (@lem1697097) (@lem1697096 n n' M)). Qed.
Lemma lem1697099 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) : (term658 n n' M x) = (term658 n n' M x).
Proof. exact (MK_COMB (@lem1697098 n n' M) (@lem1697026 x)). Qed.
Lemma lem1697100 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term658 n n' M x.
Proof. exact (EQ_MP (@lem1697099 n n' M x) (@lem1696879 n n' M x h1)). Qed.
Lemma lem1697101 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term446 x.
Proof. exact (proj2 (@lem1697100 n n' M x h1)). Qed.
Lemma lem1697102 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term591 n n' M.
Proof. exact (proj1 (@lem1697100 n n' M x h1)). Qed.
Lemma lem1697104 (h1 : term363) : term739.
Proof. exact (proj1 (@lem1697014 h1)). Qed.
Lemma lem1697105 (n : real -> nat) (h1 : term494 n) : term494 n.
Proof. exact (h1). Qed.
Lemma lem1697106 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term547 n' M.
Proof. exact (h1). Qed.
Lemma lem1697107 (h1 : term405) : term405.
Proof. exact (h1). Qed.
Lemma lem1697108 (n : real -> nat) (h1 : term479 n) : term479 n.
Proof. exact (h1). Qed.
Lemma lem1697109 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term532 n' M.
Proof. exact (proj2 (@lem1697106 n' M h1)). Qed.
Lemma lem1697110 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term324 M.
Proof. exact (proj1 (@lem1697106 n' M h1)). Qed.
Lemma lem1697135 (m : nat) (n : nat) : ((term382 m n) = (term383 m n)) = ((term382 m n) = (term383 m n)).
Proof. exact (eq_refl ((term382 m n) = (term383 m n))). Qed.
Lemma lem1697136 (m : nat) : (term384 m) = (term384 m).
Proof. exact (fun_ext (fun n : nat => @lem1697135 m n)). Qed.
Lemma lem1697137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697138 (m : nat) : (term385 m) = (term385 m).
Proof. exact (MK_COMB (@lem1697137) (@lem1697136 m)). Qed.
Lemma lem1697139 : term386 = term386.
Proof. exact (fun_ext (fun m : nat => @lem1697138 m)). Qed.
Lemma lem1697140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697142 : term387 = term387.
Proof. exact (MK_COMB (@lem1697140) (@lem1697139)). Qed.
Lemma lem1697143 (h1 : term387) : term387.
Proof. exact (EQ_MP (@lem1697142) (@lem1696946 h1)). Qed.
Lemma lem1697190 (x : real) (n : nat) : (term28 x n) = (term28 x n).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem1697191 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun n : nat => @lem1697190 x n)). Qed.
Lemma lem1697192 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697193 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1697192) (@lem1697191 x)). Qed.
Lemma lem1697194 : term404 = term404.
Proof. exact (fun_ext (fun x : real => @lem1697193 x)). Qed.
Lemma lem1697195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697197 : term405 = term405.
Proof. exact (MK_COMB (@lem1697195) (@lem1697194)). Qed.
Lemma lem1697198 (h1 : term405) : term405.
Proof. exact (EQ_MP (@lem1697197) (@lem1697107 h1)). Qed.
Lemma lem1697213 (y : real) (x : real) : (term388 y x) = (term388 y x).
Proof. exact (eq_refl (term388 y x)). Qed.
Lemma lem1697214 (x : real) : (term389 x) = (term389 x).
Proof. exact (fun_ext (fun y : real => @lem1697213 y x)). Qed.
Lemma lem1697215 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697216 (x : real) : (term390 x) = (term390 x).
Proof. exact (MK_COMB (@lem1697215) (@lem1697214 x)). Qed.
Lemma lem1697217 : term391 = term391.
Proof. exact (fun_ext (fun x : real => @lem1697216 x)). Qed.
Lemma lem1697218 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697220 : term392 = term392.
Proof. exact (MK_COMB (@lem1697218) (@lem1697217)). Qed.
Lemma lem1697221 (h1 : term392) : term392.
Proof. exact (EQ_MP (@lem1697220) (@lem1696920 h1)). Qed.
Lemma lem1697233 (x : real) (n : nat) : (term443 x n) = (term443 x n).
Proof. exact (eq_refl (term443 x n)). Qed.
Lemma lem1697234 (x : real) : (term445 x) = (term445 x).
Proof. exact (fun_ext (fun n : nat => @lem1697233 x n)). Qed.
Lemma lem1697235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697237 (x : real) : (term446 x) = (term446 x).
Proof. exact (MK_COMB (@lem1697235) (@lem1697234 x)). Qed.
Lemma lem1697238 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term446 x.
Proof. exact (EQ_MP (@lem1697237 x) (@lem1697101 n n' M x h1)). Qed.
Lemma lem1697278 (n : real -> nat) (M : real) : (term475 n M) = (term475 n M).
Proof. exact (eq_refl (term475 n M)). Qed.
Lemma lem1697279 (n : real -> nat) : (term477 n) = (term477 n).
Proof. exact (fun_ext (fun M : real => @lem1697278 n M)). Qed.
Lemma lem1697280 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697282 (n : real -> nat) : (term479 n) = (term479 n).
Proof. exact (MK_COMB (@lem1697280) (@lem1697279 n)). Qed.
Lemma lem1697283 (n : real -> nat) (h1 : term479 n) : term479 n.
Proof. exact (EQ_MP (@lem1697282 n) (@lem1697108 n h1)). Qed.
Lemma lem1697285 (M : real) : (term289 M) = (term289 M).
Proof. exact (eq_refl (term289 M)). Qed.
Lemma lem1697286 : term393 = term393.
Proof. exact (fun_ext (fun M : real => @lem1697285 M)). Qed.
Lemma lem1697287 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697289 : term290 = term290.
Proof. exact (MK_COMB (@lem1697287) (@lem1697286)). Qed.
Lemma lem1697290 (h1 : term290) : term290.
Proof. exact (EQ_MP (@lem1697289) (@lem1696900 h1)). Qed.
Lemma lem1697308 (m : nat) (n : nat) : ((term382 m n) = (term383 m n)) = ((term382 m n) = (term383 m n)).
Proof. exact (eq_refl ((term382 m n) = (term383 m n))). Qed.
Lemma lem1697309 (m : nat) : (term384 m) = (term384 m).
Proof. exact (fun_ext (fun n : nat => @lem1697308 m n)). Qed.
Lemma lem1697310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697311 (m : nat) : (term385 m) = (term385 m).
Proof. exact (MK_COMB (@lem1697310) (@lem1697309 m)). Qed.
Lemma lem1697312 : term386 = term386.
Proof. exact (fun_ext (fun m : nat => @lem1697311 m)). Qed.
Lemma lem1697313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697315 : term387 = term387.
Proof. exact (MK_COMB (@lem1697313) (@lem1697312)). Qed.
Lemma lem1697316 (h1 : term387) : term387.
Proof. exact (EQ_MP (@lem1697315) (@lem1696946 h1)). Qed.
Lemma lem1697331 (x : real) (z : real) (y : real) : (term684 x z y) = (term684 x z y).
Proof. exact (eq_refl (term684 x z y)). Qed.
Lemma lem1697332 (x : real) (y : real) : (term681 x y) = (term681 x y).
Proof. exact (fun_ext (fun z : real => @lem1697331 x z y)). Qed.
Lemma lem1697333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697334 (x : real) (y : real) : (term695 x y) = (term695 x y).
Proof. exact (MK_COMB (@lem1697333) (@lem1697332 x y)). Qed.
Lemma lem1697335 (x : real) : (term706 x) = (term706 x).
Proof. exact (fun_ext (fun y : real => @lem1697334 x y)). Qed.
Lemma lem1697336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697337 (x : real) : (term717 x) = (term717 x).
Proof. exact (MK_COMB (@lem1697336) (@lem1697335 x)). Qed.
Lemma lem1697338 : term728 = term728.
Proof. exact (fun_ext (fun x : real => @lem1697337 x)). Qed.
Lemma lem1697339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697341 : term739 = term739.
Proof. exact (MK_COMB (@lem1697339) (@lem1697338)). Qed.
Lemma lem1697342 (h1 : term363) : term739.
Proof. exact (EQ_MP (@lem1697341) (@lem1697104 h1)). Qed.
Lemma lem1697363 (n : nat) (M : real) : (term321 n M) = (term321 n M).
Proof. exact (eq_refl (term321 n M)). Qed.
Lemma lem1697364 (M : real) : (term323 M) = (term323 M).
Proof. exact (fun_ext (fun n : nat => @lem1697363 n M)). Qed.
Lemma lem1697365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1697367 (M : real) : (term324 M) = (term324 M).
Proof. exact (MK_COMB (@lem1697365) (@lem1697364 M)). Qed.
Lemma lem1697368 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term324 M.
Proof. exact (EQ_MP (@lem1697367 M) (@lem1697110 n' M h1)). Qed.
Lemma lem1697376 (n' : real -> nat) (M : real) (M' : real) : (term528 n' M M') = (term528 n' M M').
Proof. exact (eq_refl (term528 n' M M')). Qed.
Lemma lem1697377 (n' : real -> nat) (M : real) : (term530 n' M) = (term530 n' M).
Proof. exact (fun_ext (fun M' : real => @lem1697376 n' M M')). Qed.
Lemma lem1697378 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1697380 (n' : real -> nat) (M : real) : (term532 n' M) = (term532 n' M).
Proof. exact (MK_COMB (@lem1697378) (@lem1697377 n' M)). Qed.
Lemma lem1697381 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term532 n' M.
Proof. exact (EQ_MP (@lem1697380 n' M) (@lem1697109 n' M h1)). Qed.
Lemma lem1697391 (_26173 : nat) (h1 : term387) : term746 _26173.
Proof. exact (@lem1697143 h1 _26173). Qed.
Lemma lem1697392 (_26173 : nat) : (term746 _26173) = (term385 _26173).
Proof. exact (eq_refl (term746 _26173)). Qed.
Lemma lem1697393 (_26173 : nat) (h1 : term387) : term385 _26173.
Proof. exact (EQ_MP (@lem1697392 _26173) (@lem1697391 _26173 h1)). Qed.
Lemma lem1697394 (_26173 : nat) (_26174 : nat) (h1 : term387) : term747 _26173 _26174.
Proof. exact (@lem1697393 _26173 h1 _26174). Qed.
Lemma lem1697395 (_26173 : nat) (_26174 : nat) : (term747 _26173 _26174) = ((term382 _26173 _26174) = (term383 _26173 _26174)).
Proof. exact (eq_refl (term747 _26173 _26174)). Qed.
Lemma lem1697418 (_26182 : real) (h1 : term405) : term748 _26182.
Proof. exact (@lem1697198 h1 _26182). Qed.
Lemma lem1697419 (_26182 : real) : (term748 _26182) = (term31 _26182).
Proof. exact (eq_refl (term748 _26182)). Qed.
Lemma lem1697420 (_26182 : real) (h1 : term405) : term31 _26182.
Proof. exact (EQ_MP (@lem1697419 _26182) (@lem1697418 _26182 h1)). Qed.
Lemma lem1697421 (_26182 : real) (_26183 : nat) (h1 : term405) : term206 _26182 _26183.
Proof. exact (@lem1697420 _26182 h1 _26183). Qed.
Lemma lem1697422 (_26182 : real) (_26183 : nat) : (term206 _26182 _26183) = (term28 _26182 _26183).
Proof. exact (eq_refl (term206 _26182 _26183)). Qed.
Lemma lem1697427 (_26185 : real) (h1 : term392) : term749 _26185.
Proof. exact (@lem1697221 h1 _26185). Qed.
Lemma lem1697428 (_26185 : real) : (term749 _26185) = (term390 _26185).
Proof. exact (eq_refl (term749 _26185)). Qed.
Lemma lem1697429 (_26185 : real) (h1 : term392) : term390 _26185.
Proof. exact (EQ_MP (@lem1697428 _26185) (@lem1697427 _26185 h1)). Qed.
Lemma lem1697430 (_26185 : real) (_26186 : real) (h1 : term392) : term750 _26185 _26186.
Proof. exact (@lem1697429 _26185 h1 _26186). Qed.
Lemma lem1697431 (_26186 : real) (_26185 : real) : (term750 _26185 _26186) = (term388 _26186 _26185).
Proof. exact (eq_refl (term750 _26185 _26186)). Qed.
Lemma lem1697439 (_26189 : nat) (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term751 x _26189.
Proof. exact (@lem1697238 n n' M x h1 _26189). Qed.
Lemma lem1697440 (x : real) (_26189 : nat) : (term751 x _26189) = (term443 x _26189).
Proof. exact (eq_refl (term751 x _26189)). Qed.
Lemma lem1697460 (_26196 : real) (n : real -> nat) (h1 : term479 n) : term752 n _26196.
Proof. exact (@lem1697283 n h1 _26196). Qed.
Lemma lem1697461 (n : real -> nat) (_26196 : real) : (term752 n _26196) = (term475 n _26196).
Proof. exact (eq_refl (term752 n _26196)). Qed.
Lemma lem1697463 (_26197 : real) (h1 : term290) : term753 _26197.
Proof. exact (@lem1697290 h1 _26197). Qed.
Lemma lem1697464 (_26197 : real) : (term753 _26197) = (term289 _26197).
Proof. exact (eq_refl (term753 _26197)). Qed.
Lemma lem1697472 (_26200 : nat) (h1 : term387) : term746 _26200.
Proof. exact (@lem1697316 h1 _26200). Qed.
Lemma lem1697473 (_26200 : nat) : (term746 _26200) = (term385 _26200).
Proof. exact (eq_refl (term746 _26200)). Qed.
Lemma lem1697474 (_26200 : nat) (h1 : term387) : term385 _26200.
Proof. exact (EQ_MP (@lem1697473 _26200) (@lem1697472 _26200 h1)). Qed.
Lemma lem1697475 (_26200 : nat) (_26201 : nat) (h1 : term387) : term747 _26200 _26201.
Proof. exact (@lem1697474 _26200 h1 _26201). Qed.
Lemma lem1697476 (_26200 : nat) (_26201 : nat) : (term747 _26200 _26201) = ((term382 _26200 _26201) = (term383 _26200 _26201)).
Proof. exact (eq_refl (term747 _26200 _26201)). Qed.
Lemma lem1697481 (_26203 : real) (h1 : term363) : term730 _26203.
Proof. exact (@lem1697342 h1 _26203). Qed.
Lemma lem1697482 (_26203 : real) : (term730 _26203) = (term717 _26203).
Proof. exact (eq_refl (term730 _26203)). Qed.
Lemma lem1697483 (_26203 : real) (h1 : term363) : term717 _26203.
Proof. exact (EQ_MP (@lem1697482 _26203) (@lem1697481 _26203 h1)). Qed.
Lemma lem1697484 (_26203 : real) (_26204 : real) (h1 : term363) : term708 _26203 _26204.
Proof. exact (@lem1697483 _26203 h1 _26204). Qed.
Lemma lem1697485 (_26203 : real) (_26204 : real) : (term708 _26203 _26204) = (term695 _26203 _26204).
Proof. exact (eq_refl (term708 _26203 _26204)). Qed.
Lemma lem1697486 (_26203 : real) (_26204 : real) (h1 : term363) : term695 _26203 _26204.
Proof. exact (EQ_MP (@lem1697485 _26203 _26204) (@lem1697484 _26203 _26204 h1)). Qed.
Lemma lem1697487 (_26203 : real) (_26204 : real) (_26205 : real) (h1 : term363) : term683 _26203 _26204 _26205.
Proof. exact (@lem1697486 _26203 _26204 h1 _26205). Qed.
Lemma lem1697488 (_26203 : real) (_26205 : real) (_26204 : real) : (term683 _26203 _26204 _26205) = (term684 _26203 _26205 _26204).
Proof. exact (eq_refl (term683 _26203 _26204 _26205)). Qed.
Lemma lem1697499 (_26209 : nat) (n' : real -> nat) (M : real) (h1 : term547 n' M) : term408 M _26209.
Proof. exact (@lem1697368 n' M h1 _26209). Qed.
Lemma lem1697500 (_26209 : nat) (M : real) : (term408 M _26209) = (term321 _26209 M).
Proof. exact (eq_refl (term408 M _26209)). Qed.
Lemma lem1697502 (_26210 : real) (n' : real -> nat) (M : real) (h1 : term547 n' M) : term754 n' M _26210.
Proof. exact (@lem1697381 n' M h1 _26210). Qed.
Lemma lem1697503 (n' : real -> nat) (M : real) (_26210 : real) : (term754 n' M _26210) = (term528 n' M _26210).
Proof. exact (eq_refl (term754 n' M _26210)). Qed.
Lemma lem1697530 (_26182 : real) (_26183 : nat) (h1 : term405) : term28 _26182 _26183.
Proof. exact (EQ_MP (@lem1697422 _26182 _26183) (@lem1697421 _26182 _26183 h1)). Qed.
Lemma lem1697538 (_26186 : real) (_26185 : real) (h1 : term392) : term388 _26186 _26185.
Proof. exact (EQ_MP (@lem1697431 _26186 _26185) (@lem1697430 _26185 _26186 h1)). Qed.
Lemma lem1697556 (_26196 : real) (n : real -> nat) (h1 : term479 n) : term475 n _26196.
Proof. exact (EQ_MP (@lem1697461 n _26196) (@lem1697460 _26196 n h1)). Qed.
Lemma lem1697558 (_26197 : real) (h1 : term290) : term289 _26197.
Proof. exact (EQ_MP (@lem1697464 _26197) (@lem1697463 _26197 h1)). Qed.
Lemma lem1697574 (_26203 : real) (_26205 : real) (_26204 : real) (h1 : term363) : term684 _26203 _26205 _26204.
Proof. exact (EQ_MP (@lem1697488 _26203 _26205 _26204) (@lem1697487 _26203 _26204 _26205 h1)). Qed.
Lemma lem1697588 (_26210 : real) (n' : real -> nat) (M : real) (h1 : term547 n' M) : term528 n' M _26210.
Proof. exact (EQ_MP (@lem1697503 n' M _26210) (@lem1697502 _26210 n' M h1)). Qed.
Lemma lem1697682 (_26173 : nat) (_26174 : nat) (h1 : term387) : (term382 _26173 _26174) = (term383 _26173 _26174).
Proof. exact (EQ_MP (@lem1697395 _26173 _26174) (@lem1697394 _26173 _26174 h1)). Qed.
Lemma lem1697683 (_26233 : nat) (_26234 : nat) (h1 : term387) : (term382 _26233 _26234) = (term383 _26233 _26234).
Proof. exact (@lem1697682 _26233 _26234 h1). Qed.
Lemma lem1697684 (_26233 : nat) (_26234 : nat) (h1 : term387) : term755 _26233 _26234.
Proof. exact (fun h0 : term756 _26233 _26234 => @lem1697683 _26233 _26234 h1). Qed.
Lemma lem1697686 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1697687 (_26233 : nat) (_26234 : nat) : (term755 _26233 _26234) = ((term382 _26233 _26234) = (term383 _26233 _26234)).
Proof. exact (@lem1697686 ((term382 _26233 _26234) = (term383 _26233 _26234))). Qed.
Lemma lem1697688 (_26233 : nat) (_26234 : nat) (h1 : term387) : (term382 _26233 _26234) = (term383 _26233 _26234).
Proof. exact (EQ_MP (@lem1697687 _26233 _26234) (@lem1697684 _26233 _26234 h1)). Qed.
Lemma lem1697691 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1697693 (_26182 : real) (_26183 : nat) : (term28 _26182 _26183) = (term757 _26182 _26183).
Proof. exact (@lem1697691 (_26182 = (real_of_num _26183))). Qed.
Lemma lem1697696 (_26182 : real) (_26183 : nat) (h1 : term405) : term757 _26182 _26183.
Proof. exact (EQ_MP (@lem1697693 _26182 _26183) (@lem1697530 _26182 _26183 h1)). Qed.
Lemma lem1697697 (_26233 : nat) (_26234 : nat) (h1 : term405) : term758 _26233 _26234.
Proof. exact (@lem1697696 (term382 _26233 _26234) (Nat.add _26233 _26234) h1). Qed.
Lemma lem1697700 (h1 : term387) (h2 : term405) : False.
Proof. exact (@lem1697697 (@el nat) (@el nat) h2 (@lem1697688 (@el nat) (@el nat) h1)). Qed.
Lemma lem1697701 (h1 : term387) (h2 : term405) : term243.
Proof. exact (fun h0 : ~ False => @lem1697700 h1 h2). Qed.
Lemma lem1697703 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1697704 : term243 = False.
Proof. exact (@lem1697703 False). Qed.
Lemma lem1697705 (h1 : term387) (h2 : term405) : False.
Proof. exact (EQ_MP (@lem1697704) (@lem1697701 h1 h2)). Qed.
Lemma lem1697807 (_26189 : nat) (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term443 x _26189.
Proof. exact (EQ_MP (@lem1697440 x _26189) (@lem1697439 _26189 n n' M x h1)). Qed.
Lemma lem1697808 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term759 n x.
Proof. exact (@lem1697807 (n x) n n' M x h1). Qed.
Lemma lem1697809 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term760 n x.
Proof. exact (fun h0 : term761 n x => @lem1697808 n n' M x h1). Qed.
Lemma lem1697811 (p : Prop) : (term762 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1697812 (n : real -> nat) (x : real) : (term760 n x) = (term759 n x).
Proof. exact (@lem1697811 (term761 n x)). Qed.
Lemma lem1697813 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term658 n n' M x) : term759 n x.
Proof. exact (EQ_MP (@lem1697812 n x) (@lem1697809 n n' M x h1)). Qed.
Lemma lem1697824 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1697825 (_26186 : real) (_26185 : real) : (term388 _26185 _26186) = (term388 _26186 _26185).
Proof. exact (@lem1697824 (real_le _26185 _26186) (real_le _26186 _26185)). Qed.
Lemma lem1697831 (_26186 : real) (_26185 : real) : (term763 _26186 _26185) = (term763 _26186 _26185).
Proof. exact (eq_refl (term763 _26186 _26185)). Qed.
Lemma lem1697832 (_26186 : real) (_26185 : real) : ((term388 _26186 _26185) = (term388 _26185 _26186)) = ((term388 _26186 _26185) = (term388 _26186 _26185)).
Proof. exact (MK_COMB (@lem1697831 _26186 _26185) (@lem1697825 _26186 _26185)). Qed.
Lemma lem1697834 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1697835 (x : Prop) : (x = x) = True.
Proof. exact (@lem1697834 Prop x). Qed.
Lemma lem1697836 (_26186 : real) (_26185 : real) : ((term388 _26186 _26185) = (term388 _26186 _26185)) = True.
Proof. exact (@lem1697835 (term388 _26186 _26185)). Qed.
Lemma lem1697837 (_26185 : real) (_26186 : real) : ((term388 _26186 _26185) = (term388 _26185 _26186)) = True.
Proof. exact (TRANS (@lem1697832 _26186 _26185) (@lem1697836 _26186 _26185)). Qed.
Lemma lem1697838 (_26185 : real) (_26186 : real) : True = ((term388 _26186 _26185) = (term388 _26185 _26186)).
Proof. exact (SYM (@lem1697837 _26185 _26186)). Qed.
Lemma lem1697839 (_26185 : real) (_26186 : real) : (term388 _26186 _26185) = (term388 _26185 _26186).
Proof. exact (EQ_MP (@lem1697838 _26185 _26186) (@lem0)). Qed.
Lemma lem1697840 (_26185 : real) (_26186 : real) (h1 : term392) : term388 _26185 _26186.
Proof. exact (EQ_MP (@lem1697839 _26185 _26186) (@lem1697538 _26186 _26185 h1)). Qed.
Lemma lem1697842 (b : Prop) (a : Prop) : (a \/ b) = (term234 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1697845 (_26186 : real) (_26185 : real) : (term388 _26185 _26186) = (term764 _26186 _26185).
Proof. exact (@lem1697842 (real_le _26185 _26186) (real_le _26186 _26185)). Qed.
Lemma lem1697848 (_26186 : real) (_26185 : real) (h1 : term392) : term764 _26186 _26185.
Proof. exact (EQ_MP (@lem1697845 _26186 _26185) (@lem1697840 _26185 _26186 h1)). Qed.
Lemma lem1697849 (n : real -> nat) (x : real) (h1 : term392) : term765 n x.
Proof. exact (@lem1697848 (term766 n x) x h1). Qed.
Lemma lem1697852 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term658 n n' M x) : term767 n x.
Proof. exact (@lem1697849 n x h1 (@lem1697813 n n' M x h2)). Qed.
Lemma lem1697853 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term658 n n' M x) : term768 n x.
Proof. exact (fun h0 : term475 n x => @lem1697852 n n' M x h1 h2). Qed.
Lemma lem1697855 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1697856 (n : real -> nat) (x : real) : (term768 n x) = (term767 n x).
Proof. exact (@lem1697855 (term767 n x)). Qed.
Lemma lem1697857 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term658 n n' M x) : term767 n x.
Proof. exact (EQ_MP (@lem1697856 n x) (@lem1697853 n n' M x h1 h2)). Qed.
Lemma lem1697860 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1697862 (n : real -> nat) (_26196 : real) : (term475 n _26196) = (term769 n _26196).
Proof. exact (@lem1697860 (term767 n _26196)). Qed.
Lemma lem1697865 (_26196 : real) (n : real -> nat) (h1 : term479 n) : term769 n _26196.
Proof. exact (EQ_MP (@lem1697862 n _26196) (@lem1697556 _26196 n h1)). Qed.
Lemma lem1697866 (x : real) (n : real -> nat) (h1 : term479 n) : term769 n x.
Proof. exact (@lem1697865 x n h1). Qed.
Lemma lem1697869 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term479 n) (h3 : term658 n n' M x) : False.
Proof. exact (@lem1697866 x n h2 (@lem1697857 n n' M x h1 h3)). Qed.
Lemma lem1697870 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term479 n) (h3 : term658 n n' M x) : term243.
Proof. exact (fun h0 : ~ False => @lem1697869 n n' M x h1 h2 h3). Qed.
Lemma lem1697872 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1697873 : term243 = False.
Proof. exact (@lem1697872 False). Qed.
Lemma lem1697874 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term479 n) (h3 : term658 n n' M x) : False.
Proof. exact (EQ_MP (@lem1697873) (@lem1697870 n n' M x h1 h2 h3)). Qed.
Lemma lem1697875 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1697876 (_26259 : real) (_26261 : real) (h1 : _26259 = _26261) : _26259 = _26261.
Proof. exact (h1). Qed.
Lemma lem1697877 (_26260 : real) (_26262 : real) (h1 : _26260 = _26262) : _26260 = _26262.
Proof. exact (h1). Qed.
Lemma lem1697878 (_26259 : real) (_26261 : real) (h1 : _26259 = _26261) : (real_le _26259) = (real_le _26261).
Proof. exact (MK_COMB (@lem1697875) (@lem1697876 _26259 _26261 h1)). Qed.
Lemma lem1697879 (_26259 : real) (_26261 : real) (_26260 : real) (_26262 : real) (h1 : _26259 = _26261) (h2 : _26260 = _26262) : (real_le _26259 _26260) = (real_le _26261 _26262).
Proof. exact (MK_COMB (@lem1697878 _26259 _26261 h1) (@lem1697877 _26260 _26262 h2)). Qed.
Lemma lem1697881 (b : Prop) (a : Prop) : term770 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1697882 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : term771 _26261 _26262 _26259 _26260.
Proof. exact (@lem1697881 (real_le _26261 _26262) (real_le _26259 _26260)). Qed.
Lemma lem1697883 (_26259 : real) (_26261 : real) (_26260 : real) (_26262 : real) (h1 : _26259 = _26261) (h2 : _26260 = _26262) : term772 _26261 _26262 _26259 _26260.
Proof. exact (@lem1697882 _26261 _26262 _26259 _26260 (@lem1697879 _26259 _26261 _26260 _26262 h1 h2)). Qed.
Lemma lem1697884 (_26262 : real) (_26260 : real) (_26259 : real) (_26261 : real) (h1 : _26259 = _26261) : term773 _26261 _26262 _26259 _26260.
Proof. exact (fun h0 : _26260 = _26262 => @lem1697883 _26259 _26261 _26260 _26262 h1 h0). Qed.
Lemma lem1697886 (a : Prop) (b : Prop) : (a -> b) = (term774 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1697887 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term773 _26261 _26262 _26259 _26260) = (term775 _26261 _26262 _26259 _26260).
Proof. exact (@lem1697886 (_26260 = _26262) (term772 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1697888 (_26262 : real) (_26260 : real) (_26259 : real) (_26261 : real) (h1 : _26259 = _26261) : term775 _26261 _26262 _26259 _26260.
Proof. exact (EQ_MP (@lem1697887 _26261 _26262 _26259 _26260) (@lem1697884 _26262 _26260 _26259 _26261 h1)). Qed.
Lemma lem1697889 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : term776 _26261 _26262 _26259 _26260.
Proof. exact (fun h0 : _26259 = _26261 => @lem1697888 _26262 _26260 _26259 _26261 h0). Qed.
Lemma lem1697891 (a : Prop) (b : Prop) : (a -> b) = (term774 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1697892 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term776 _26261 _26262 _26259 _26260) = (term777 _26261 _26262 _26259 _26260).
Proof. exact (@lem1697891 (_26259 = _26261) (term775 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1697893 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : term777 _26261 _26262 _26259 _26260.
Proof. exact (EQ_MP (@lem1697892 _26261 _26262 _26259 _26260) (@lem1697889 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1697972 (x : real) (y : real) (z : real) : term778 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1697976 (_26200 : nat) (_26201 : nat) (h1 : term387) : (term382 _26200 _26201) = (term383 _26200 _26201).
Proof. exact (EQ_MP (@lem1697476 _26200 _26201) (@lem1697475 _26200 _26201 h1)). Qed.
Lemma lem1697977 (n' : real -> nat) (M : real) (h1 : term387) : (term779 n' M) = (term780 n' M).
Proof. exact (@lem1697976 (term781 n' M) term255 h1). Qed.
Lemma lem1697978 (n' : real -> nat) (M : real) (h1 : term387) : term782 n' M.
Proof. exact (fun h0 : term783 n' M => @lem1697977 n' M h1). Qed.
Lemma lem1697980 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1697981 (n' : real -> nat) (M : real) : (term782 n' M) = ((term779 n' M) = (term780 n' M)).
Proof. exact (@lem1697980 ((term779 n' M) = (term780 n' M))). Qed.
Lemma lem1697982 (n' : real -> nat) (M : real) (h1 : term387) : (term779 n' M) = (term780 n' M).
Proof. exact (EQ_MP (@lem1697981 n' M) (@lem1697978 n' M h1)). Qed.
Lemma lem1697984 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1697985 (n' : real -> nat) (M : real) : (term779 n' M) = (term779 n' M).
Proof. exact (@lem1697984 (term779 n' M)). Qed.
Lemma lem1697986 (n' : real -> nat) (M : real) : term784 n' M.
Proof. exact (fun h0 : term785 n' M => @lem1697985 n' M). Qed.
Lemma lem1697988 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1697989 (n' : real -> nat) (M : real) : (term784 n' M) = ((term779 n' M) = (term779 n' M)).
Proof. exact (@lem1697988 ((term779 n' M) = (term779 n' M))). Qed.
Lemma lem1697990 (n' : real -> nat) (M : real) : (term779 n' M) = (term779 n' M).
Proof. exact (EQ_MP (@lem1697989 n' M) (@lem1697986 n' M)). Qed.
Lemma lem1698008 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1698009 (y : real) (x : real) (z : real) : (term786 x y z) = (term787 y x z).
Proof. exact (@lem1698008 (y = z) (term788 x z)). Qed.
Lemma lem1698019 (x : real) (y : real) : (term789 x y) = (term789 x y).
Proof. exact (eq_refl (term789 x y)). Qed.
Lemma lem1698020 (y : real) (x : real) (z : real) : (term778 x y z) = (term790 y x z).
Proof. exact (MK_COMB (@lem1698019 x y) (@lem1698009 y x z)). Qed.
Lemma lem1698024 (q : Prop) (p : Prop) (r : Prop) : (term791 p q r) = (term791 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1698025 (y : real) (x : real) (z : real) : (term790 y x z) = (term792 y x z).
Proof. exact (@lem1698024 (y = z) (term788 x y) (term788 x z)). Qed.
Lemma lem1698047 (y : real) (x : real) (z : real) : (term778 x y z) = (term792 y x z).
Proof. exact (TRANS (@lem1698020 y x z) (@lem1698025 y x z)). Qed.
Lemma lem1698048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1698049 (y : real) (x : real) (z : real) : (term793 x y z) = (term794 y x z).
Proof. exact (MK_COMB (@lem1698048) (@lem1698047 y x z)). Qed.
Lemma lem1698071 (y : real) (x : real) (z : real) : (term792 y x z) = (term792 y x z).
Proof. exact (eq_refl (term792 y x z)). Qed.
Lemma lem1698072 (y : real) (x : real) (z : real) : ((term778 x y z) = (term792 y x z)) = ((term792 y x z) = (term792 y x z)).
Proof. exact (MK_COMB (@lem1698049 y x z) (@lem1698071 y x z)). Qed.
Lemma lem1698074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1698075 (x : Prop) : (x = x) = True.
Proof. exact (@lem1698074 Prop x). Qed.
Lemma lem1698076 (y : real) (x : real) (z : real) : ((term792 y x z) = (term792 y x z)) = True.
Proof. exact (@lem1698075 (term792 y x z)). Qed.
Lemma lem1698077 (y : real) (x : real) (z : real) : ((term778 x y z) = (term792 y x z)) = True.
Proof. exact (TRANS (@lem1698072 y x z) (@lem1698076 y x z)). Qed.
Lemma lem1698078 (y : real) (x : real) (z : real) : True = ((term778 x y z) = (term792 y x z)).
Proof. exact (SYM (@lem1698077 y x z)). Qed.
Lemma lem1698079 (y : real) (x : real) (z : real) : (term778 x y z) = (term792 y x z).
Proof. exact (EQ_MP (@lem1698078 y x z) (@lem0)). Qed.
Lemma lem1698080 (y : real) (x : real) (z : real) : term792 y x z.
Proof. exact (EQ_MP (@lem1698079 y x z) (@lem1697972 x y z)). Qed.
Lemma lem1698082 (b : Prop) (a : Prop) : (a \/ b) = (term234 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1698083 (x : real) (y : real) (z : real) : (term792 y x z) = (term795 x y z).
Proof. exact (@lem1698082 (term796 y x z) (y = z)). Qed.
Lemma lem1698085 (a : Prop) (b : Prop) : (term797 a b) = (term798 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1698086 (y : real) (x : real) (z : real) : (term799 y x z) = (term800 y x z).
Proof. exact (@lem1698085 (term788 x y) (term788 x z)). Qed.
Lemma lem1698088 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1698089 (x : real) (y : real) : (term801 x y) = (x = y).
Proof. exact (@lem1698088 (x = y)). Qed.
Lemma lem1698090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1698091 (x : real) (y : real) : (term802 x y) = (term803 x y).
Proof. exact (MK_COMB (@lem1698090) (@lem1698089 x y)). Qed.
Lemma lem1698093 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1698094 (x : real) (z : real) : (term801 x z) = (x = z).
Proof. exact (@lem1698093 (x = z)). Qed.
Lemma lem1698095 (y : real) (x : real) (z : real) : (term800 y x z) = (term804 y x z).
Proof. exact (MK_COMB (@lem1698091 x y) (@lem1698094 x z)). Qed.
Lemma lem1698096 (y : real) (x : real) (z : real) : (term799 y x z) = (term804 y x z).
Proof. exact (TRANS (@lem1698086 y x z) (@lem1698095 y x z)). Qed.
Lemma lem1698097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1698098 (y : real) (x : real) (z : real) : (term805 y x z) = (term806 y x z).
Proof. exact (MK_COMB (@lem1698097) (@lem1698096 y x z)). Qed.
Lemma lem1698099 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1698100 (x : real) (y : real) (z : real) : (term795 x y z) = (term807 x y z).
Proof. exact (MK_COMB (@lem1698098 y x z) (@lem1698099 y z)). Qed.
Lemma lem1698101 (x : real) (y : real) (z : real) : (term792 y x z) = (term807 x y z).
Proof. exact (TRANS (@lem1698083 x y z) (@lem1698100 x y z)). Qed.
Lemma lem1698103 (n' : real -> nat) (M : real) (h1 : term387) : term808 n' M.
Proof. exact (conj (@lem1697982 n' M h1) (@lem1697990 n' M)). Qed.
Lemma lem1698105 (x : real) (y : real) (z : real) : term807 x y z.
Proof. exact (EQ_MP (@lem1698101 x y z) (@lem1698080 y x z)). Qed.
Lemma lem1698106 (n' : real -> nat) (M : real) : term809 n' M.
Proof. exact (@lem1698105 (term779 n' M) (term780 n' M) (term779 n' M)). Qed.
Lemma lem1698109 (n' : real -> nat) (M : real) (h1 : term387) : (term780 n' M) = (term779 n' M).
Proof. exact (@lem1698106 n' M (@lem1698103 n' M h1)). Qed.
Lemma lem1698110 (n' : real -> nat) (M : real) (h1 : term387) : term810 n' M.
Proof. exact (fun h0 : term811 n' M => @lem1698109 n' M h1). Qed.
Lemma lem1698112 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1698113 (n' : real -> nat) (M : real) : (term810 n' M) = ((term780 n' M) = (term779 n' M)).
Proof. exact (@lem1698112 ((term780 n' M) = (term779 n' M))). Qed.
Lemma lem1698114 (n' : real -> nat) (M : real) (h1 : term387) : (term780 n' M) = (term779 n' M).
Proof. exact (EQ_MP (@lem1698113 n' M) (@lem1698110 n' M h1)). Qed.
Lemma lem1698116 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1698117 (M : real) : M = M.
Proof. exact (@lem1698116 M). Qed.
Lemma lem1698118 (M : real) : term812 M.
Proof. exact (fun h0 : term813 M => @lem1698117 M). Qed.
Lemma lem1698120 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1698121 (M : real) : (term812 M) = (M = M).
Proof. exact (@lem1698120 (M = M)). Qed.
Lemma lem1698122 (M : real) : M = M.
Proof. exact (EQ_MP (@lem1698121 M) (@lem1698118 M)). Qed.
Lemma lem1698124 (_26209 : nat) (n' : real -> nat) (M : real) (h1 : term547 n' M) : term321 _26209 M.
Proof. exact (EQ_MP (@lem1697500 _26209 M) (@lem1697499 _26209 n' M h1)). Qed.
Lemma lem1698125 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term814 n' M.
Proof. exact (@lem1698124 (term815 n' M) n' M h1). Qed.
Lemma lem1698126 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term816 n' M.
Proof. exact (fun h0 : term817 n' M => @lem1698125 n' M h1). Qed.
Lemma lem1698128 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1698129 (n' : real -> nat) (M : real) : (term816 n' M) = (term814 n' M).
Proof. exact (@lem1698128 (term814 n' M)). Qed.
Lemma lem1698130 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term814 n' M.
Proof. exact (EQ_MP (@lem1698129 n' M) (@lem1698126 n' M h1)). Qed.
Lemma lem1698148 (q : Prop) (p : Prop) (r : Prop) : (term791 p q r) = (term791 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1698149 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term775 _26261 _26262 _26259 _26260) = (term818 _26261 _26262 _26259 _26260).
Proof. exact (@lem1698148 (real_le _26261 _26262) (term788 _26260 _26262) (term819 _26259 _26260)). Qed.
Lemma lem1698167 (_26259 : real) (_26261 : real) : (term789 _26259 _26261) = (term789 _26259 _26261).
Proof. exact (eq_refl (term789 _26259 _26261)). Qed.
Lemma lem1698168 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term777 _26261 _26262 _26259 _26260) = (term820 _26261 _26262 _26259 _26260).
Proof. exact (MK_COMB (@lem1698167 _26259 _26261) (@lem1698149 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698172 (q : Prop) (p : Prop) (r : Prop) : (term791 p q r) = (term791 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1698173 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term820 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260).
Proof. exact (@lem1698172 (real_le _26261 _26262) (term788 _26259 _26261) (term822 _26262 _26259 _26260)). Qed.
Lemma lem1698203 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term777 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260).
Proof. exact (TRANS (@lem1698168 _26261 _26262 _26259 _26260) (@lem1698173 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1698205 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term823 _26261 _26262 _26259 _26260) = (term824 _26261 _26262 _26259 _26260).
Proof. exact (MK_COMB (@lem1698204) (@lem1698203 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698235 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term821 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260).
Proof. exact (eq_refl (term821 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698236 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : ((term777 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260)) = ((term821 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260)).
Proof. exact (MK_COMB (@lem1698205 _26261 _26262 _26259 _26260) (@lem1698235 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698238 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1698239 (x : Prop) : (x = x) = True.
Proof. exact (@lem1698238 Prop x). Qed.
Lemma lem1698240 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : ((term821 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260)) = True.
Proof. exact (@lem1698239 (term821 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698241 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : ((term777 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260)) = True.
Proof. exact (TRANS (@lem1698236 _26261 _26262 _26259 _26260) (@lem1698240 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698242 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : True = ((term777 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260)).
Proof. exact (SYM (@lem1698241 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698243 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term777 _26261 _26262 _26259 _26260) = (term821 _26261 _26262 _26259 _26260).
Proof. exact (EQ_MP (@lem1698242 _26261 _26262 _26259 _26260) (@lem0)). Qed.
Lemma lem1698244 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : term821 _26261 _26262 _26259 _26260.
Proof. exact (EQ_MP (@lem1698243 _26261 _26262 _26259 _26260) (@lem1697893 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698246 (b : Prop) (a : Prop) : (a \/ b) = (term234 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1698247 (_26259 : real) (_26260 : real) (_26261 : real) (_26262 : real) : (term821 _26261 _26262 _26259 _26260) = (term825 _26259 _26260 _26261 _26262).
Proof. exact (@lem1698246 (term826 _26261 _26262 _26259 _26260) (real_le _26261 _26262)). Qed.
Lemma lem1698249 (a : Prop) (b : Prop) : (term797 a b) = (term798 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1698250 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term827 _26261 _26262 _26259 _26260) = (term828 _26261 _26262 _26259 _26260).
Proof. exact (@lem1698249 (term788 _26259 _26261) (term822 _26262 _26259 _26260)). Qed.
Lemma lem1698252 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1698253 (_26259 : real) (_26261 : real) : (term801 _26259 _26261) = (_26259 = _26261).
Proof. exact (@lem1698252 (_26259 = _26261)). Qed.
Lemma lem1698254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1698255 (_26259 : real) (_26261 : real) : (term802 _26259 _26261) = (term803 _26259 _26261).
Proof. exact (MK_COMB (@lem1698254) (@lem1698253 _26259 _26261)). Qed.
Lemma lem1698257 (a : Prop) (b : Prop) : (term797 a b) = (term798 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1698258 (_26262 : real) (_26259 : real) (_26260 : real) : (term829 _26262 _26259 _26260) = (term830 _26262 _26259 _26260).
Proof. exact (@lem1698257 (term788 _26260 _26262) (term819 _26259 _26260)). Qed.
Lemma lem1698260 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1698261 (_26260 : real) (_26262 : real) : (term801 _26260 _26262) = (_26260 = _26262).
Proof. exact (@lem1698260 (_26260 = _26262)). Qed.
Lemma lem1698262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1698263 (_26260 : real) (_26262 : real) : (term802 _26260 _26262) = (term803 _26260 _26262).
Proof. exact (MK_COMB (@lem1698262) (@lem1698261 _26260 _26262)). Qed.
Lemma lem1698265 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1698266 (_26259 : real) (_26260 : real) : (term831 _26259 _26260) = (real_le _26259 _26260).
Proof. exact (@lem1698265 (real_le _26259 _26260)). Qed.
Lemma lem1698267 (_26262 : real) (_26259 : real) (_26260 : real) : (term830 _26262 _26259 _26260) = (term832 _26262 _26259 _26260).
Proof. exact (MK_COMB (@lem1698263 _26260 _26262) (@lem1698266 _26259 _26260)). Qed.
Lemma lem1698268 (_26262 : real) (_26259 : real) (_26260 : real) : (term829 _26262 _26259 _26260) = (term832 _26262 _26259 _26260).
Proof. exact (TRANS (@lem1698258 _26262 _26259 _26260) (@lem1698267 _26262 _26259 _26260)). Qed.
Lemma lem1698269 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term828 _26261 _26262 _26259 _26260) = (term833 _26261 _26262 _26259 _26260).
Proof. exact (MK_COMB (@lem1698255 _26259 _26261) (@lem1698268 _26262 _26259 _26260)). Qed.
Lemma lem1698270 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term827 _26261 _26262 _26259 _26260) = (term833 _26261 _26262 _26259 _26260).
Proof. exact (TRANS (@lem1698250 _26261 _26262 _26259 _26260) (@lem1698269 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1698272 (_26261 : real) (_26262 : real) (_26259 : real) (_26260 : real) : (term834 _26261 _26262 _26259 _26260) = (term835 _26261 _26262 _26259 _26260).
Proof. exact (MK_COMB (@lem1698271) (@lem1698270 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698273 (_26261 : real) (_26262 : real) : (real_le _26261 _26262) = (real_le _26261 _26262).
Proof. exact (eq_refl (real_le _26261 _26262)). Qed.
Lemma lem1698274 (_26259 : real) (_26260 : real) (_26261 : real) (_26262 : real) : (term825 _26259 _26260 _26261 _26262) = (term836 _26259 _26260 _26261 _26262).
Proof. exact (MK_COMB (@lem1698272 _26261 _26262 _26259 _26260) (@lem1698273 _26261 _26262)). Qed.
Lemma lem1698275 (_26259 : real) (_26260 : real) (_26261 : real) (_26262 : real) : (term821 _26261 _26262 _26259 _26260) = (term836 _26259 _26260 _26261 _26262).
Proof. exact (TRANS (@lem1698247 _26259 _26260 _26261 _26262) (@lem1698274 _26259 _26260 _26261 _26262)). Qed.
Lemma lem1698277 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term837 n' M.
Proof. exact (conj (@lem1698122 M) (@lem1698130 n' M h1)). Qed.
Lemma lem1698278 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term547 n' M) : term838 n' M.
Proof. exact (conj (@lem1698114 n' M h1) (@lem1698277 n' M h2)). Qed.
Lemma lem1698280 (_26259 : real) (_26260 : real) (_26261 : real) (_26262 : real) : term836 _26259 _26260 _26261 _26262.
Proof. exact (EQ_MP (@lem1698275 _26259 _26260 _26261 _26262) (@lem1698244 _26261 _26262 _26259 _26260)). Qed.
Lemma lem1698281 (n' : real -> nat) (M : real) : term839 n' M.
Proof. exact (@lem1698280 (term780 n' M) M (term779 n' M) M). Qed.
Lemma lem1698284 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term547 n' M) : term840 n' M.
Proof. exact (@lem1698281 n' M (@lem1698278 n' M h1 h2)). Qed.
Lemma lem1698285 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term547 n' M) : term841 n' M.
Proof. exact (fun h0 : term842 n' M => @lem1698284 n' M h1 h2). Qed.
Lemma lem1698287 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1698288 (n' : real -> nat) (M : real) : (term841 n' M) = (term840 n' M).
Proof. exact (@lem1698287 (term840 n' M)). Qed.
Lemma lem1698289 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term547 n' M) : term840 n' M.
Proof. exact (EQ_MP (@lem1698288 n' M) (@lem1698285 n' M h1 h2)). Qed.
Lemma lem1698291 (b : Prop) (a : Prop) : (a \/ b) = (term234 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1698292 (_26203 : real) (_26204 : real) (_26205 : real) : (term684 _26203 _26205 _26204) = (term843 _26203 _26204 _26205).
Proof. exact (@lem1698291 (term844 _26203 _26205 _26204) (term375 _26203 _26204 _26205)). Qed.
Lemma lem1698294 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1698295 (_26203 : real) (_26205 : real) (_26204 : real) : (term845 _26203 _26205 _26204) = (term376 _26203 _26205 _26204).
Proof. exact (@lem1698294 (term376 _26203 _26205 _26204)). Qed.
Lemma lem1698296 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1698297 (_26203 : real) (_26205 : real) (_26204 : real) : (term846 _26203 _26205 _26204) = (term847 _26203 _26205 _26204).
Proof. exact (MK_COMB (@lem1698296) (@lem1698295 _26203 _26205 _26204)). Qed.
Lemma lem1698298 (_26203 : real) (_26204 : real) (_26205 : real) : (term375 _26203 _26204 _26205) = (term375 _26203 _26204 _26205).
Proof. exact (eq_refl (term375 _26203 _26204 _26205)). Qed.
Lemma lem1698299 (_26203 : real) (_26204 : real) (_26205 : real) : (term843 _26203 _26204 _26205) = (term848 _26203 _26204 _26205).
Proof. exact (MK_COMB (@lem1698297 _26203 _26205 _26204) (@lem1698298 _26203 _26204 _26205)). Qed.
Lemma lem1698300 (_26203 : real) (_26204 : real) (_26205 : real) : (term684 _26203 _26205 _26204) = (term848 _26203 _26204 _26205).
Proof. exact (TRANS (@lem1698292 _26203 _26204 _26205) (@lem1698299 _26203 _26204 _26205)). Qed.
Lemma lem1698303 (_26203 : real) (_26204 : real) (_26205 : real) (h1 : term363) : term848 _26203 _26204 _26205.
Proof. exact (EQ_MP (@lem1698300 _26203 _26204 _26205) (@lem1697574 _26203 _26205 _26204 h1)). Qed.
Lemma lem1698304 (n' : real -> nat) (M : real) (h1 : term363) : term849 n' M.
Proof. exact (@lem1698303 (term850 n' M) M term250 h1). Qed.
Lemma lem1698307 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term547 n' M) : term851 n' M.
Proof. exact (@lem1698304 n' M h2 (@lem1698289 n' M h1 h3)). Qed.
Lemma lem1698308 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term547 n' M) : term852 n' M.
Proof. exact (fun h0 : term853 n' M => @lem1698307 n' M h1 h2 h3). Qed.
Lemma lem1698310 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1698311 (n' : real -> nat) (M : real) : (term852 n' M) = (term851 n' M).
Proof. exact (@lem1698310 (term851 n' M)). Qed.
Lemma lem1698312 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term547 n' M) : term851 n' M.
Proof. exact (EQ_MP (@lem1698311 n' M) (@lem1698308 n' M h1 h2 h3)). Qed.
Lemma lem1698318 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1698319 (M : real) (n' : real -> nat) (_26210 : real) : (term528 n' M _26210) = (term854 M n' _26210).
Proof. exact (@lem1698318 (real_le M _26210) (term475 n' _26210)). Qed.
Lemma lem1698325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1698326 (M : real) (n' : real -> nat) (_26210 : real) : (term855 n' M _26210) = (term856 M n' _26210).
Proof. exact (MK_COMB (@lem1698325) (@lem1698319 M n' _26210)). Qed.
Lemma lem1698332 (M : real) (n' : real -> nat) (_26210 : real) : (term854 M n' _26210) = (term854 M n' _26210).
Proof. exact (eq_refl (term854 M n' _26210)). Qed.
Lemma lem1698333 (M : real) (n' : real -> nat) (_26210 : real) : ((term528 n' M _26210) = (term854 M n' _26210)) = ((term854 M n' _26210) = (term854 M n' _26210)).
Proof. exact (MK_COMB (@lem1698326 M n' _26210) (@lem1698332 M n' _26210)). Qed.
Lemma lem1698335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1698336 (x : Prop) : (x = x) = True.
Proof. exact (@lem1698335 Prop x). Qed.
Lemma lem1698337 (M : real) (n' : real -> nat) (_26210 : real) : ((term854 M n' _26210) = (term854 M n' _26210)) = True.
Proof. exact (@lem1698336 (term854 M n' _26210)). Qed.
Lemma lem1698338 (M : real) (n' : real -> nat) (_26210 : real) : ((term528 n' M _26210) = (term854 M n' _26210)) = True.
Proof. exact (TRANS (@lem1698333 M n' _26210) (@lem1698337 M n' _26210)). Qed.
Lemma lem1698339 (M : real) (n' : real -> nat) (_26210 : real) : True = ((term528 n' M _26210) = (term854 M n' _26210)).
Proof. exact (SYM (@lem1698338 M n' _26210)). Qed.
Lemma lem1698340 (M : real) (n' : real -> nat) (_26210 : real) : (term528 n' M _26210) = (term854 M n' _26210).
Proof. exact (EQ_MP (@lem1698339 M n' _26210) (@lem0)). Qed.
Lemma lem1698341 (_26210 : real) (n' : real -> nat) (M : real) (h1 : term547 n' M) : term854 M n' _26210.
Proof. exact (EQ_MP (@lem1698340 M n' _26210) (@lem1697588 _26210 n' M h1)). Qed.
Lemma lem1698343 (b : Prop) (a : Prop) : (a \/ b) = (term234 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1698344 (n' : real -> nat) (M : real) (_26210 : real) : (term854 M n' _26210) = (term857 n' M _26210).
Proof. exact (@lem1698343 (term475 n' _26210) (real_le M _26210)). Qed.
Lemma lem1698346 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1698347 (n' : real -> nat) (_26210 : real) : (term858 n' _26210) = (term767 n' _26210).
Proof. exact (@lem1698346 (term767 n' _26210)). Qed.
Lemma lem1698348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1698349 (n' : real -> nat) (_26210 : real) : (term859 n' _26210) = (term860 n' _26210).
Proof. exact (MK_COMB (@lem1698348) (@lem1698347 n' _26210)). Qed.
Lemma lem1698350 (M : real) (_26210 : real) : (real_le M _26210) = (real_le M _26210).
Proof. exact (eq_refl (real_le M _26210)). Qed.
Lemma lem1698351 (n' : real -> nat) (M : real) (_26210 : real) : (term857 n' M _26210) = (term861 n' M _26210).
Proof. exact (MK_COMB (@lem1698349 n' _26210) (@lem1698350 M _26210)). Qed.
Lemma lem1698352 (n' : real -> nat) (M : real) (_26210 : real) : (term854 M n' _26210) = (term861 n' M _26210).
Proof. exact (TRANS (@lem1698344 n' M _26210) (@lem1698351 n' M _26210)). Qed.
Lemma lem1698355 (_26210 : real) (n' : real -> nat) (M : real) (h1 : term547 n' M) : term861 n' M _26210.
Proof. exact (EQ_MP (@lem1698352 n' M _26210) (@lem1698341 _26210 n' M h1)). Qed.
Lemma lem1698356 (n' : real -> nat) (M : real) (h1 : term547 n' M) : term862 n' M.
Proof. exact (@lem1698355 (term248 M) n' M h1). Qed.
Lemma lem1698359 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term547 n' M) : term246 M.
Proof. exact (@lem1698356 n' M h3 (@lem1698312 n' M h1 h2 h3)). Qed.
Lemma lem1698360 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term547 n' M) : term863 M.
Proof. exact (fun h0 : term289 M => @lem1698359 n' M h1 h2 h3). Qed.
Lemma lem1698362 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1698363 (M : real) : (term863 M) = (term246 M).
Proof. exact (@lem1698362 (term246 M)). Qed.
Lemma lem1698364 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term547 n' M) : term246 M.
Proof. exact (EQ_MP (@lem1698363 M) (@lem1698360 n' M h1 h2 h3)). Qed.
Lemma lem1698367 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1698369 (_26197 : real) : (term289 _26197) = (term864 _26197).
Proof. exact (@lem1698367 (term246 _26197)). Qed.
Lemma lem1698372 (_26197 : real) (h1 : term290) : term864 _26197.
Proof. exact (EQ_MP (@lem1698369 _26197) (@lem1697558 _26197 h1)). Qed.
Lemma lem1698373 (M : real) (h1 : term290) : term864 M.
Proof. exact (@lem1698372 M h1). Qed.
Lemma lem1698376 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term290) (h4 : term547 n' M) : False.
Proof. exact (@lem1698373 M h3 (@lem1698364 n' M h1 h2 h4)). Qed.
Lemma lem1698377 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term290) (h4 : term547 n' M) : term243.
Proof. exact (fun h0 : ~ False => @lem1698376 n' M h1 h2 h3 h4). Qed.
Lemma lem1698379 (p : Prop) : (term230 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1698380 : term243 = False.
Proof. exact (@lem1698379 False). Qed.
Lemma lem1698381 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term290) (h4 : term547 n' M) : False.
Proof. exact (EQ_MP (@lem1698380) (@lem1698377 n' M h1 h2 h3 h4)). Qed.
Lemma lem1698382 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term290) (h4 : term547 n' M) : term387 = False.
Proof. exact (prop_ext (fun h5 : term387 => @lem1698381 n' M h1 h2 h3 h4) (fun h5 : False => @lem1697316 h1)). Qed.
Lemma lem1698383 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term290) (h4 : term547 n' M) : False.
Proof. exact (EQ_MP (@lem1698382 n' M h1 h2 h3 h4) (@lem1697316 h1)). Qed.
Lemma lem1698384 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term290) (h4 : term547 n' M) : term290 = False.
Proof. exact (prop_ext (fun h5 : term290 => @lem1698383 n' M h1 h2 h3 h4) (fun h5 : False => @lem1697290 h3)). Qed.
Lemma lem1698385 (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term290) (h4 : term547 n' M) : False.
Proof. exact (EQ_MP (@lem1698384 n' M h1 h2 h3 h4) (@lem1697290 h3)). Qed.
Lemma lem1698386 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term479 n) (h3 : term658 n n' M x) : (term479 n) = False.
Proof. exact (prop_ext (fun h4 : term479 n => @lem1697874 n n' M x h1 h2 h3) (fun h4 : False => @lem1697283 n h2)). Qed.
Lemma lem1698387 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term479 n) (h3 : term658 n n' M x) : False.
Proof. exact (EQ_MP (@lem1698386 n n' M x h1 h2 h3) (@lem1697283 n h2)). Qed.
Lemma lem1698388 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term479 n) (h3 : term658 n n' M x) : term392 = False.
Proof. exact (prop_ext (fun h4 : term392 => @lem1698387 n n' M x h1 h2 h3) (fun h4 : False => @lem1697221 h1)). Qed.
Lemma lem1698389 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term392) (h2 : term479 n) (h3 : term658 n n' M x) : False.
Proof. exact (EQ_MP (@lem1698388 n n' M x h1 h2 h3) (@lem1697221 h1)). Qed.
Lemma lem1698390 (h1 : term387) (h2 : term405) : term405 = False.
Proof. exact (prop_ext (fun h3 : term405 => @lem1697705 h1 h2) (fun h3 : False => @lem1697198 h2)). Qed.
Lemma lem1698391 (h1 : term387) (h2 : term405) : False.
Proof. exact (EQ_MP (@lem1698390 h1 h2) (@lem1697198 h2)). Qed.
Lemma lem1698392 (h1 : term387) (h2 : term405) : term387 = False.
Proof. exact (prop_ext (fun h3 : term387 => @lem1698391 h1 h2) (fun h3 : False => @lem1697143 h1)). Qed.
Lemma lem1698393 (h1 : term387) (h2 : term405) : False.
Proof. exact (EQ_MP (@lem1698392 h1 h2) (@lem1697143 h1)). Qed.
Lemma lem1698394 (n' : real -> nat) (M : real) (x : real) (n : real -> nat) (h1 : term387) (h2 : term392) (h3 : term658 n n' M x) (h4 : term494 n) : False.
Proof. exact (or_elim (@lem1697105 n h4) (fun h0 : term405 => @lem1698393 h1 h0) (fun h0 : term479 n => @lem1698389 n n' M x h2 h0 h3)). Qed.
Lemma lem1698395 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : False.
Proof. exact (or_elim (@lem1697102 n n' M x h5) (fun h0 : term494 n => @lem1698394 n' M x n h1 h3 h5 h0) (fun h0 : term547 n' M => @lem1698385 n' M h1 h2 h4 h0)). Qed.
Lemma lem1698396 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : (term658 n n' M x) = False.
Proof. exact (prop_ext (fun h6 : term658 n n' M x => @lem1698395 n n' M x h1 h2 h3 h4 h5) (fun h6 : False => @lem1697100 n n' M x h5)). Qed.
Lemma lem1698397 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : False.
Proof. exact (EQ_MP (@lem1698396 n n' M x h1 h2 h3 h4 h5) (@lem1697100 n n' M x h5)). Qed.
Lemma lem1698398 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : term387 = False.
Proof. exact (prop_ext (fun h6 : term387 => @lem1698397 n n' M x h1 h2 h3 h4 h5) (fun h6 : False => @lem1696946 h1)). Qed.
Lemma lem1698399 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : False.
Proof. exact (EQ_MP (@lem1698398 n n' M x h1 h2 h3 h4 h5) (@lem1696946 h1)). Qed.
Lemma lem1698400 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : term392 = False.
Proof. exact (prop_ext (fun h6 : term392 => @lem1698399 n n' M x h1 h2 h3 h4 h5) (fun h6 : False => @lem1696920 h3)). Qed.
Lemma lem1698401 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : False.
Proof. exact (EQ_MP (@lem1698400 n n' M x h1 h2 h3 h4 h5) (@lem1696920 h3)). Qed.
Lemma lem1698402 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : term290 = False.
Proof. exact (prop_ext (fun h6 : term290 => @lem1698401 n n' M x h1 h2 h3 h4 h5) (fun h6 : False => @lem1696900 h4)). Qed.
Lemma lem1698403 (n : real -> nat) (n' : real -> nat) (M : real) (x : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term658 n n' M x) : False.
Proof. exact (EQ_MP (@lem1698402 n n' M x h1 h2 h3 h4 h5) (@lem1696900 h4)). Qed.
Lemma lem1698404 (n : real -> nat) (n' : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term661 n n' M) : False.
Proof. exact (ex_elim (@lem1696878 n n' M h5) (fun x : real => fun h0 : term660 n n' M x => @lem1698403 n n' M x h1 h2 h3 h4 h0)). Qed.
Lemma lem1698405 (n : real -> nat) (M : real) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term663 n M) : False.
Proof. exact (ex_elim (@lem1696877 n M h5) (fun n' : real -> nat => fun h0 : term662 n M n' => @lem1698404 n n' M h1 h2 h3 h4 h0)). Qed.
Lemma lem1698406 (n : real -> nat) (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term665 n) : False.
Proof. exact (ex_elim (@lem1696876 n h5) (fun M : real => fun h0 : term664 n M => @lem1698405 n M h1 h2 h3 h4 h0)). Qed.
Lemma lem1698407 (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term356) : False.
Proof. exact (ex_elim (@lem1696337 h5) (fun n : real -> nat => fun h0 : term666 n => @lem1698406 n h1 h2 h3 h4 h0)). Qed.
Lemma lem1698408 (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term356) : term387 = False.
Proof. exact (prop_ext (fun h6 : term387 => @lem1698407 h1 h2 h3 h4 h5) (fun h6 : False => @lem1696438 h1)). Qed.
Lemma lem1698409 (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term356) : False.
Proof. exact (EQ_MP (@lem1698408 h1 h2 h3 h4 h5) (@lem1696438 h1)). Qed.
Lemma lem1698410 (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term356) : term392 = False.
Proof. exact (prop_ext (fun h6 : term392 => @lem1698409 h1 h2 h3 h4 h5) (fun h6 : False => @lem1696418 h3)). Qed.
Lemma lem1698411 (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term356) : False.
Proof. exact (EQ_MP (@lem1698410 h1 h2 h3 h4 h5) (@lem1696418 h3)). Qed.
Lemma lem1698412 (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term356) : term290 = False.
Proof. exact (prop_ext (fun h6 : term290 => @lem1698411 h1 h2 h3 h4 h5) (fun h6 : False => @lem1696350 h4)). Qed.
Lemma lem1698413 (h1 : term387) (h2 : term363) (h3 : term392) (h4 : term290) (h5 : term356) : False.
Proof. exact (EQ_MP (@lem1698412 h1 h2 h3 h4 h5) (@lem1696350 h4)). Qed.
Lemma lem1698414 (h1 : term387) (h2 : term392) (h3 : term290) (h4 : term356) : term361.
Proof. exact (fun h0 : term363 => @lem1698413 h1 h0 h2 h3 h4). Qed.
Lemma lem1698415 : term361 = term362.
Proof. exact (@lem69 term363). Qed.
Lemma lem1698416 (h1 : term387) (h2 : term392) (h3 : term290) (h4 : term356) : term362.
Proof. exact (EQ_MP (@lem1698415) (@lem1698414 h1 h2 h3 h4)). Qed.
Lemma lem1698417 (h1 : term392) (h2 : term290) (h3 : term356) : term366.
Proof. exact (fun h0 : term387 => @lem1698416 h0 h1 h2 h3). Qed.
Lemma lem1698418 (h1 : term290) (h2 : term356) : term369.
Proof. exact (fun h0 : term392 => @lem1698417 h0 h1 h2). Qed.
Lemma lem1698419 (h1 : term356) : term372.
Proof. exact (fun h0 : term290 => @lem1698418 h0 h1). Qed.
Lemma lem1698420 : term374.
Proof. exact (fun h0 : term356 => @lem1698419 h0). Qed.
Lemma lem1698421 : term357.
Proof. exact (EQ_MP (@lem1695768) (@lem1698420)). Qed.
Lemma lem1698423 : term357.
Proof. exact (@lem1695328 (@lem1698421)). Qed.
Lemma lem1698424 (h1 : term356) : term371.
Proof. exact (@lem1698423 (@lem1695313 h1)). Qed.
Lemma lem1698425 (h1 : term356) : term368.
Proof. exact (@lem1698424 h1 (@lem1695028)). Qed.
Lemma lem1698426 (h1 : term356) : term365.
Proof. exact (@lem1698425 h1 (@lem1339697)). Qed.
Lemma lem1698427 (h1 : term356) : term361.
Proof. exact (@lem1698426 h1 (@lem1340339)). Qed.
Lemma lem1698428 (h1 : term356) : False.
Proof. exact (@lem1698427 h1 (@lem1516197)). Qed.
Lemma lem1698429 (h1 : term356) : term356 = False.
Proof. exact (prop_ext (fun h2 : term356 => @lem1698428 h1) (fun h2 : False => @lem1695313 h1)). Qed.
Lemma lem1698430 (h1 : term356) : False.
Proof. exact (EQ_MP (@lem1698429 h1) (@lem1695313 h1)). Qed.
Lemma lem1698431 : term355.
Proof. exact (fun h0 : term356 => @lem1698430 h0). Qed.
Lemma lem1698432 : term354.
Proof. exact (EQ_MP (@lem1695312) (@lem1698431)). Qed.
Lemma lem1698433 : term353.
Proof. exact (EQ_MP (@lem1695308) (@lem1698432)). Qed.
Lemma lem1698434 : term352.
Proof. exact (@lem1698433 (@lem1695031)). Qed.
