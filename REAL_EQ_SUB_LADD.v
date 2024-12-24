Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_SUB_LADD_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1520149 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 (x = (real_sub y z)) ((real_add x z) = y)). Qed.
Lemma lem1520150 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1520151 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (@lem1520150 (term6 x y)). Qed.
Lemma lem1520152 (x : real) (z : real) (y : real) : (term7 x y z) = ((x = (real_sub y z)) = ((real_add x z) = y)).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1520153 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1520154 (x : real) (z : real) (y : real) : (term8 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1520153) (@lem1520152 x z y)). Qed.
Lemma lem1520155 (x : real) (z : real) (y : real) : (term8 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1520154 x z y) (@lem1520149 x z y)). Qed.
Lemma lem1520156 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (fun_ext (fun z : real => @lem1520155 x z y)). Qed.
Lemma lem1520157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520158 (x : real) (y : real) : (term5 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1520157) (@lem1520156 x y)). Qed.
Lemma lem1520159 (x : real) (y : real) : (term4 x y) = (term11 x y).
Proof. exact (TRANS (@lem1520151 x y) (@lem1520158 x y)). Qed.
Lemma lem1520160 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1520161 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1520160 (term14 x)). Qed.
Lemma lem1520162 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1520163 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1520164 (x : real) (y : real) : (term17 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1520163) (@lem1520162 x y)). Qed.
Lemma lem1520165 (x : real) (y : real) : (term17 x y) = (term11 x y).
Proof. exact (TRANS (@lem1520164 x y) (@lem1520159 x y)). Qed.
Lemma lem1520166 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1520165 x y)). Qed.
Lemma lem1520167 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520168 (x : real) : (term13 x) = (term20 x).
Proof. exact (MK_COMB (@lem1520167) (@lem1520166 x)). Qed.
Lemma lem1520169 (x : real) : (term12 x) = (term20 x).
Proof. exact (TRANS (@lem1520161 x) (@lem1520168 x)). Qed.
Lemma lem1520170 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1520171 : term21 = term22.
Proof. exact (@lem1520170 term23). Qed.
Lemma lem1520172 (x : real) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1520173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1520174 (x : real) : (term26 x) = (term12 x).
Proof. exact (MK_COMB (@lem1520173) (@lem1520172 x)). Qed.
Lemma lem1520175 (x : real) : (term26 x) = (term20 x).
Proof. exact (TRANS (@lem1520174 x) (@lem1520169 x)). Qed.
Lemma lem1520176 : term27 = term28.
Proof. exact (fun_ext (fun x : real => @lem1520175 x)). Qed.
Lemma lem1520177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520178 : term22 = term29.
Proof. exact (MK_COMB (@lem1520177) (@lem1520176)). Qed.
Lemma lem1520180 : term21 = term29.
Proof. exact (TRANS (@lem1520171) (@lem1520178)). Qed.
Lemma lem1520197 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1520198 (x : real) (y : real) : (term10 x y) = (term10 x y).
Proof. exact (fun_ext (fun z : real => @lem1520197 x z y)). Qed.
Lemma lem1520199 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520200 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1520199) (@lem1520198 x y)). Qed.
Lemma lem1520201 (x : real) : (term19 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1520200 x y)). Qed.
Lemma lem1520202 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520203 (x : real) : (term20 x) = (term20 x).
Proof. exact (MK_COMB (@lem1520202) (@lem1520201 x)). Qed.
Lemma lem1520204 : term28 = term28.
Proof. exact (fun_ext (fun x : real => @lem1520203 x)). Qed.
Lemma lem1520205 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520206 : term29 = term29.
Proof. exact (MK_COMB (@lem1520205) (@lem1520204)). Qed.
Lemma lem1520207 : term21 = term29.
Proof. exact (TRANS (@lem1520180) (@lem1520206)). Qed.
Lemma lem1520208 (x : real) (y : real) (z : real) : (x = (real_sub y z)) = ((term30 x y z) = term31).
Proof. exact (@lem1483529 x (real_sub y z)). Qed.
Lemma lem1520221 (y : real) (z : real) : (real_sub y z) = (term32 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1520224 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1520225 (x : real) (y : real) (z : real) : (term30 x y z) = (term33 x y z).
Proof. exact (MK_COMB (@lem1520224 x) (@lem1520221 y z)). Qed.
Lemma lem1520226 (x : real) (y : real) (z : real) : (term33 x y z) = (term34 x y z).
Proof. exact (@lem1483519 x (term32 y z)). Qed.
Lemma lem1520227 (y : real) (z : real) : (term35 y z) = (term36 y z).
Proof. exact (@lem1483508 y term37 (term38 z)). Qed.
Lemma lem1520228 (z : real) : (term39 z) = (term40 z).
Proof. exact (@lem1483476 term37 term37 z). Qed.
Lemma lem1520230 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1520231 : term43 = term44.
Proof. exact (@lem1520230 term45 term45). Qed.
Lemma lem1520232 : (term46 = (BIT1 0)) = (term47 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1520233 : term47 = term45.
Proof. exact (EQ_MP (@lem1520232) (@lem940073)). Qed.
Lemma lem1520234 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1520235 : term44 = term48.
Proof. exact (MK_COMB (@lem1520234) (@lem1520233)). Qed.
Lemma lem1520236 : term43 = term48.
Proof. exact (TRANS (@lem1520231) (@lem1520235)). Qed.
Lemma lem1520237 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1520238 : term49 = term50.
Proof. exact (MK_COMB (@lem1520237) (@lem1520236)). Qed.
Lemma lem1520239 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1520240 (z : real) : (term40 z) = (term51 z).
Proof. exact (MK_COMB (@lem1520238) (@lem1520239 z)). Qed.
Lemma lem1520241 (z : real) : (term39 z) = (term51 z).
Proof. exact (TRANS (@lem1520228 z) (@lem1520240 z)). Qed.
Lemma lem1520242 (z : real) : (term51 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1520243 (z : real) : (term39 z) = z.
Proof. exact (TRANS (@lem1520241 z) (@lem1520242 z)). Qed.
Lemma lem1520246 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1520247 (y : real) (z : real) : (term36 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1520246 y) (@lem1520243 z)). Qed.
Lemma lem1520248 (y : real) (z : real) : (term35 y z) = (term53 y z).
Proof. exact (TRANS (@lem1520227 y z) (@lem1520247 y z)). Qed.
Lemma lem1520249 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1520252 (x : real) (y : real) (z : real) : (term34 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1520249 x) (@lem1520248 y z)). Qed.
Lemma lem1520253 (x : real) (y : real) (z : real) : (term33 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1520226 x y z) (@lem1520252 x y z)). Qed.
Lemma lem1520254 (x : real) (y : real) (z : real) : (term30 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1520225 x y z) (@lem1520253 x y z)). Qed.
Lemma lem1520255 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1520256 (x : real) (y : real) (z : real) : (term55 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1520255) (@lem1520254 x y z)). Qed.
Lemma lem1520257 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1520258 (x : real) (y : real) (z : real) : ((term30 x y z) = term31) = ((term54 x y z) = term31).
Proof. exact (MK_COMB (@lem1520256 x y z) (@lem1520257)). Qed.
Lemma lem1520259 (x : real) (y : real) (z : real) : (x = (real_sub y z)) = ((term54 x y z) = term31).
Proof. exact (TRANS (@lem1520208 x y z) (@lem1520258 x y z)). Qed.
Lemma lem1520260 (x : real) (z : real) (y : real) : (term57 x z y) = (term58 x z y).
Proof. exact (@lem1483554 (real_add x z) y). Qed.
Lemma lem1520272 (x : real) (z : real) (y : real) : (term59 x z y) = (term60 x z y).
Proof. exact (@lem1483519 (real_add x z) y). Qed.
Lemma lem1520276 (x : real) (z : real) (y : real) : (term60 x z y) = (term61 x z y).
Proof. exact (@lem1483482 x z (term38 y)). Qed.
Lemma lem1520277 (y : real) (z : real) : (term32 z y) = (term53 y z).
Proof. exact (@lem1483488 (term38 y) z). Qed.
Lemma lem1520278 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1520279 (x : real) (y : real) (z : real) : (term61 x z y) = (term54 x y z).
Proof. exact (MK_COMB (@lem1520278 x) (@lem1520277 y z)). Qed.
Lemma lem1520281 (x : real) (y : real) (z : real) : (term60 x z y) = (term54 x y z).
Proof. exact (TRANS (@lem1520276 x z y) (@lem1520279 x y z)). Qed.
Lemma lem1520283 (x : real) (y : real) (z : real) : (term59 x z y) = (term54 x y z).
Proof. exact (TRANS (@lem1520272 x z y) (@lem1520281 x y z)). Qed.
Lemma lem1520284 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1520285 (x : real) (y : real) (z : real) : (term62 x z y) = (term63 x y z).
Proof. exact (MK_COMB (@lem1520284) (@lem1520283 x y z)). Qed.
Lemma lem1520286 (x : real) (y : real) (z : real) : (term63 x y z) = (term64 x y z).
Proof. exact (@lem1483512 (term54 x y z)). Qed.
Lemma lem1520287 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem1483508 x term37 (term53 y z)). Qed.
Lemma lem1520288 (y : real) (z : real) : (term66 y z) = (term67 y z).
Proof. exact (@lem1483508 (term38 y) term37 z). Qed.
Lemma lem1520289 (z : real) : (term38 z) = (term38 z).
Proof. exact (eq_refl (term38 z)). Qed.
Lemma lem1520290 (y : real) : (term39 y) = (term40 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1520292 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1520293 : term43 = term44.
Proof. exact (@lem1520292 term45 term45). Qed.
Lemma lem1520294 : (term46 = (BIT1 0)) = (term47 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1520295 : term47 = term45.
Proof. exact (EQ_MP (@lem1520294) (@lem940073)). Qed.
Lemma lem1520296 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1520297 : term44 = term48.
Proof. exact (MK_COMB (@lem1520296) (@lem1520295)). Qed.
Lemma lem1520298 : term43 = term48.
Proof. exact (TRANS (@lem1520293) (@lem1520297)). Qed.
Lemma lem1520299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1520300 : term49 = term50.
Proof. exact (MK_COMB (@lem1520299) (@lem1520298)). Qed.
Lemma lem1520301 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1520302 (y : real) : (term40 y) = (term51 y).
Proof. exact (MK_COMB (@lem1520300) (@lem1520301 y)). Qed.
Lemma lem1520303 (y : real) : (term39 y) = (term51 y).
Proof. exact (TRANS (@lem1520290 y) (@lem1520302 y)). Qed.
Lemma lem1520304 (y : real) : (term51 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1520305 (y : real) : (term39 y) = y.
Proof. exact (TRANS (@lem1520303 y) (@lem1520304 y)). Qed.
Lemma lem1520306 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1520307 (y : real) : (term68 y) = (real_add y).
Proof. exact (MK_COMB (@lem1520306) (@lem1520305 y)). Qed.
Lemma lem1520308 (y : real) (z : real) : (term67 y z) = (term32 y z).
Proof. exact (MK_COMB (@lem1520307 y) (@lem1520289 z)). Qed.
Lemma lem1520309 (y : real) (z : real) : (term66 y z) = (term32 y z).
Proof. exact (TRANS (@lem1520288 y z) (@lem1520308 y z)). Qed.
Lemma lem1520312 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1520313 (x : real) (y : real) (z : real) : (term65 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1520312 x) (@lem1520309 y z)). Qed.
Lemma lem1520314 (x : real) (y : real) (z : real) : (term64 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1520287 x y z) (@lem1520313 x y z)). Qed.
Lemma lem1520315 (x : real) (y : real) (z : real) : (term63 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1520286 x y z) (@lem1520314 x y z)). Qed.
Lemma lem1520316 (x : real) (z : real) (y : real) : (term70 x z y) = (term70 x z y).
Proof. exact (eq_refl (term70 x z y)). Qed.
Lemma lem1520317 (x : real) (y : real) (z : real) : ((term62 x z y) = (term63 x y z)) = ((term62 x z y) = (term69 x y z)).
Proof. exact (MK_COMB (@lem1520316 x z y) (@lem1520315 x y z)). Qed.
Lemma lem1520318 (x : real) (y : real) (z : real) : (term62 x z y) = (term69 x y z).
Proof. exact (EQ_MP (@lem1520317 x y z) (@lem1520285 x y z)). Qed.
Lemma lem1520319 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1520320 (x : real) (y : real) (z : real) : (term71 x z y) = (term72 x y z).
Proof. exact (MK_COMB (@lem1520319) (@lem1520318 x y z)). Qed.
Lemma lem1520321 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1520322 (x : real) (y : real) (z : real) : (term73 x z y) = (term74 x y z).
Proof. exact (MK_COMB (@lem1520320 x y z) (@lem1520321)). Qed.
Lemma lem1520323 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1520324 (x : real) (y : real) (z : real) : (term75 x z y) = (term76 x y z).
Proof. exact (MK_COMB (@lem1520323) (@lem1520283 x y z)). Qed.
Lemma lem1520325 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1520326 (x : real) (y : real) (z : real) : (term77 x z y) = (term78 x y z).
Proof. exact (MK_COMB (@lem1520324 x y z) (@lem1520325)). Qed.
Lemma lem1520327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520328 (x : real) (y : real) (z : real) : (term79 x z y) = (term80 x y z).
Proof. exact (MK_COMB (@lem1520327) (@lem1520326 x y z)). Qed.
Lemma lem1520329 (x : real) (y : real) (z : real) : (term58 x z y) = (term81 x y z).
Proof. exact (MK_COMB (@lem1520328 x y z) (@lem1520322 x y z)). Qed.
Lemma lem1520330 (x : real) (y : real) (z : real) : (term57 x z y) = (term81 x y z).
Proof. exact (TRANS (@lem1520260 x z y) (@lem1520329 x y z)). Qed.
Lemma lem1520331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1520332 (x : real) (y : real) (z : real) : (term82 x y z) = (term83 x y z).
Proof. exact (MK_COMB (@lem1520331) (@lem1520259 x y z)). Qed.
Lemma lem1520333 (x : real) (y : real) (z : real) : (term84 x z y) = (term85 x y z).
Proof. exact (MK_COMB (@lem1520332 x y z) (@lem1520330 x y z)). Qed.
Lemma lem1520334 (x : real) (y : real) (z : real) : (term86 x y z) = (term87 x y z).
Proof. exact (@lem1483554 x (real_sub y z)). Qed.
Lemma lem1520347 (y : real) (z : real) : (real_sub y z) = (term32 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1520350 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1520351 (x : real) (y : real) (z : real) : (term30 x y z) = (term33 x y z).
Proof. exact (MK_COMB (@lem1520350 x) (@lem1520347 y z)). Qed.
Lemma lem1520352 (x : real) (y : real) (z : real) : (term33 x y z) = (term34 x y z).
Proof. exact (@lem1483519 x (term32 y z)). Qed.
Lemma lem1520353 (y : real) (z : real) : (term35 y z) = (term36 y z).
Proof. exact (@lem1483508 y term37 (term38 z)). Qed.
Lemma lem1520354 (z : real) : (term39 z) = (term40 z).
Proof. exact (@lem1483476 term37 term37 z). Qed.
Lemma lem1520356 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1520357 : term43 = term44.
Proof. exact (@lem1520356 term45 term45). Qed.
Lemma lem1520358 : (term46 = (BIT1 0)) = (term47 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1520359 : term47 = term45.
Proof. exact (EQ_MP (@lem1520358) (@lem940073)). Qed.
Lemma lem1520360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1520361 : term44 = term48.
Proof. exact (MK_COMB (@lem1520360) (@lem1520359)). Qed.
Lemma lem1520362 : term43 = term48.
Proof. exact (TRANS (@lem1520357) (@lem1520361)). Qed.
Lemma lem1520363 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1520364 : term49 = term50.
Proof. exact (MK_COMB (@lem1520363) (@lem1520362)). Qed.
Lemma lem1520365 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1520366 (z : real) : (term40 z) = (term51 z).
Proof. exact (MK_COMB (@lem1520364) (@lem1520365 z)). Qed.
Lemma lem1520367 (z : real) : (term39 z) = (term51 z).
Proof. exact (TRANS (@lem1520354 z) (@lem1520366 z)). Qed.
Lemma lem1520368 (z : real) : (term51 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1520369 (z : real) : (term39 z) = z.
Proof. exact (TRANS (@lem1520367 z) (@lem1520368 z)). Qed.
Lemma lem1520372 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1520373 (y : real) (z : real) : (term36 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1520372 y) (@lem1520369 z)). Qed.
Lemma lem1520374 (y : real) (z : real) : (term35 y z) = (term53 y z).
Proof. exact (TRANS (@lem1520353 y z) (@lem1520373 y z)). Qed.
Lemma lem1520375 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1520378 (x : real) (y : real) (z : real) : (term34 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1520375 x) (@lem1520374 y z)). Qed.
Lemma lem1520379 (x : real) (y : real) (z : real) : (term33 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1520352 x y z) (@lem1520378 x y z)). Qed.
Lemma lem1520380 (x : real) (y : real) (z : real) : (term30 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1520351 x y z) (@lem1520379 x y z)). Qed.
Lemma lem1520381 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1520382 (x : real) (y : real) (z : real) : (term88 x y z) = (term63 x y z).
Proof. exact (MK_COMB (@lem1520381) (@lem1520380 x y z)). Qed.
Lemma lem1520383 (x : real) (y : real) (z : real) : (term63 x y z) = (term64 x y z).
Proof. exact (@lem1483512 (term54 x y z)). Qed.
Lemma lem1520384 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem1483508 x term37 (term53 y z)). Qed.
Lemma lem1520385 (y : real) (z : real) : (term66 y z) = (term67 y z).
Proof. exact (@lem1483508 (term38 y) term37 z). Qed.
Lemma lem1520386 (z : real) : (term38 z) = (term38 z).
Proof. exact (eq_refl (term38 z)). Qed.
Lemma lem1520387 (y : real) : (term39 y) = (term40 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1520389 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1520390 : term43 = term44.
Proof. exact (@lem1520389 term45 term45). Qed.
Lemma lem1520391 : (term46 = (BIT1 0)) = (term47 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1520392 : term47 = term45.
Proof. exact (EQ_MP (@lem1520391) (@lem940073)). Qed.
Lemma lem1520393 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1520394 : term44 = term48.
Proof. exact (MK_COMB (@lem1520393) (@lem1520392)). Qed.
Lemma lem1520395 : term43 = term48.
Proof. exact (TRANS (@lem1520390) (@lem1520394)). Qed.
Lemma lem1520396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1520397 : term49 = term50.
Proof. exact (MK_COMB (@lem1520396) (@lem1520395)). Qed.
Lemma lem1520398 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1520399 (y : real) : (term40 y) = (term51 y).
Proof. exact (MK_COMB (@lem1520397) (@lem1520398 y)). Qed.
Lemma lem1520400 (y : real) : (term39 y) = (term51 y).
Proof. exact (TRANS (@lem1520387 y) (@lem1520399 y)). Qed.
Lemma lem1520401 (y : real) : (term51 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1520402 (y : real) : (term39 y) = y.
Proof. exact (TRANS (@lem1520400 y) (@lem1520401 y)). Qed.
Lemma lem1520403 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1520404 (y : real) : (term68 y) = (real_add y).
Proof. exact (MK_COMB (@lem1520403) (@lem1520402 y)). Qed.
Lemma lem1520405 (y : real) (z : real) : (term67 y z) = (term32 y z).
Proof. exact (MK_COMB (@lem1520404 y) (@lem1520386 z)). Qed.
Lemma lem1520406 (y : real) (z : real) : (term66 y z) = (term32 y z).
Proof. exact (TRANS (@lem1520385 y z) (@lem1520405 y z)). Qed.
Lemma lem1520409 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1520410 (x : real) (y : real) (z : real) : (term65 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1520409 x) (@lem1520406 y z)). Qed.
Lemma lem1520411 (x : real) (y : real) (z : real) : (term64 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1520384 x y z) (@lem1520410 x y z)). Qed.
Lemma lem1520412 (x : real) (y : real) (z : real) : (term63 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1520383 x y z) (@lem1520411 x y z)). Qed.
Lemma lem1520413 (x : real) (y : real) (z : real) : (term89 x y z) = (term89 x y z).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1520414 (x : real) (y : real) (z : real) : ((term88 x y z) = (term63 x y z)) = ((term88 x y z) = (term69 x y z)).
Proof. exact (MK_COMB (@lem1520413 x y z) (@lem1520412 x y z)). Qed.
Lemma lem1520415 (x : real) (y : real) (z : real) : (term88 x y z) = (term69 x y z).
Proof. exact (EQ_MP (@lem1520414 x y z) (@lem1520382 x y z)). Qed.
Lemma lem1520416 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1520417 (x : real) (y : real) (z : real) : (term90 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1520416) (@lem1520415 x y z)). Qed.
Lemma lem1520418 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1520419 (x : real) (y : real) (z : real) : (term91 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1520417 x y z) (@lem1520418)). Qed.
Lemma lem1520420 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1520421 (x : real) (y : real) (z : real) : (term92 x y z) = (term76 x y z).
Proof. exact (MK_COMB (@lem1520420) (@lem1520380 x y z)). Qed.
Lemma lem1520422 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1520423 (x : real) (y : real) (z : real) : (term93 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1520421 x y z) (@lem1520422)). Qed.
Lemma lem1520424 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520425 (x : real) (y : real) (z : real) : (term94 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1520424) (@lem1520423 x y z)). Qed.
Lemma lem1520426 (x : real) (y : real) (z : real) : (term87 x y z) = (term81 x y z).
Proof. exact (MK_COMB (@lem1520425 x y z) (@lem1520419 x y z)). Qed.
Lemma lem1520427 (x : real) (y : real) (z : real) : (term86 x y z) = (term81 x y z).
Proof. exact (TRANS (@lem1520334 x y z) (@lem1520426 x y z)). Qed.
Lemma lem1520428 (x : real) (z : real) (y : real) : ((real_add x z) = y) = ((term59 x z y) = term31).
Proof. exact (@lem1483529 (real_add x z) y). Qed.
Lemma lem1520440 (x : real) (z : real) (y : real) : (term59 x z y) = (term60 x z y).
Proof. exact (@lem1483519 (real_add x z) y). Qed.
Lemma lem1520444 (x : real) (z : real) (y : real) : (term60 x z y) = (term61 x z y).
Proof. exact (@lem1483482 x z (term38 y)). Qed.
Lemma lem1520445 (y : real) (z : real) : (term32 z y) = (term53 y z).
Proof. exact (@lem1483488 (term38 y) z). Qed.
Lemma lem1520446 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1520447 (x : real) (y : real) (z : real) : (term61 x z y) = (term54 x y z).
Proof. exact (MK_COMB (@lem1520446 x) (@lem1520445 y z)). Qed.
Lemma lem1520449 (x : real) (y : real) (z : real) : (term60 x z y) = (term54 x y z).
Proof. exact (TRANS (@lem1520444 x z y) (@lem1520447 x y z)). Qed.
Lemma lem1520451 (x : real) (y : real) (z : real) : (term59 x z y) = (term54 x y z).
Proof. exact (TRANS (@lem1520440 x z y) (@lem1520449 x y z)). Qed.
Lemma lem1520452 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1520453 (x : real) (y : real) (z : real) : (term95 x z y) = (term56 x y z).
Proof. exact (MK_COMB (@lem1520452) (@lem1520451 x y z)). Qed.
Lemma lem1520454 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1520455 (x : real) (y : real) (z : real) : ((term59 x z y) = term31) = ((term54 x y z) = term31).
Proof. exact (MK_COMB (@lem1520453 x y z) (@lem1520454)). Qed.
Lemma lem1520456 (x : real) (y : real) (z : real) : ((real_add x z) = y) = ((term54 x y z) = term31).
Proof. exact (TRANS (@lem1520428 x z y) (@lem1520455 x y z)). Qed.
Lemma lem1520457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1520458 (x : real) (y : real) (z : real) : (term96 x y z) = (term97 x y z).
Proof. exact (MK_COMB (@lem1520457) (@lem1520427 x y z)). Qed.
Lemma lem1520459 (x : real) (y : real) (z : real) : (term98 x z y) = (term99 x y z).
Proof. exact (MK_COMB (@lem1520458 x y z) (@lem1520456 x y z)). Qed.
Lemma lem1520460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520461 (x : real) (y : real) (z : real) : (term100 x z y) = (term101 x y z).
Proof. exact (MK_COMB (@lem1520460) (@lem1520333 x y z)). Qed.
Lemma lem1520462 (x : real) (y : real) (z : real) : (term1 x z y) = (term102 x y z).
Proof. exact (MK_COMB (@lem1520461 x y z) (@lem1520459 x y z)). Qed.
Lemma lem1520463 (x : real) (y : real) : (term10 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1520462 x y z)). Qed.
Lemma lem1520464 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520465 (x : real) (y : real) : (term11 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1520464) (@lem1520463 x y)). Qed.
Lemma lem1520466 (x : real) : (term19 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1520465 x y)). Qed.
Lemma lem1520467 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520468 (x : real) : (term20 x) = (term106 x).
Proof. exact (MK_COMB (@lem1520467) (@lem1520466 x)). Qed.
Lemma lem1520469 : term28 = term107.
Proof. exact (fun_ext (fun x : real => @lem1520468 x)). Qed.
Lemma lem1520470 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520471 : term29 = term108.
Proof. exact (MK_COMB (@lem1520470) (@lem1520469)). Qed.
Lemma lem1520472 : term21 = term108.
Proof. exact (TRANS (@lem1520207) (@lem1520471)). Qed.
Lemma lem1520482 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1520483 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1520482 real P Q). Qed.
Lemma lem1520484 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (@lem1520483 (term115 x y) (term116 x y)). Qed.
Lemma lem1520485 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1520486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520487 (x : real) (y : real) (z : real) : (term118 x y z) = (term101 x y z).
Proof. exact (MK_COMB (@lem1520486) (@lem1520485 x y z)). Qed.
Lemma lem1520488 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1520489 (x : real) (y : real) (z : real) : (term120 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1520487 x y z) (@lem1520488 x y z)). Qed.
Lemma lem1520490 (x : real) (y : real) : (term121 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1520489 x y z)). Qed.
Lemma lem1520491 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520492 (x : real) (y : real) : (term113 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1520491) (@lem1520490 x y)). Qed.
Lemma lem1520493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1520494 (x : real) (y : real) : (term122 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem1520493) (@lem1520492 x y)). Qed.
Lemma lem1520495 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1520496 (x : real) (y : real) : (term124 x y) = (term115 x y).
Proof. exact (fun_ext (fun z : real => @lem1520495 x y z)). Qed.
Lemma lem1520497 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520498 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1520497) (@lem1520496 x y)). Qed.
Lemma lem1520499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520500 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1520499) (@lem1520498 x y)). Qed.
Lemma lem1520501 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1520502 (x : real) (y : real) : (term129 x y) = (term116 x y).
Proof. exact (fun_ext (fun z : real => @lem1520501 x y z)). Qed.
Lemma lem1520503 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520504 (x : real) (y : real) : (term130 x y) = (term131 x y).
Proof. exact (MK_COMB (@lem1520503) (@lem1520502 x y)). Qed.
Lemma lem1520505 (x : real) (y : real) : (term114 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1520500 x y) (@lem1520504 x y)). Qed.
Lemma lem1520506 (x : real) (y : real) : ((term113 x y) = (term114 x y)) = ((term104 x y) = (term132 x y)).
Proof. exact (MK_COMB (@lem1520494 x y) (@lem1520505 x y)). Qed.
Lemma lem1520507 (x : real) (y : real) : (term104 x y) = (term132 x y).
Proof. exact (EQ_MP (@lem1520506 x y) (@lem1520484 x y)). Qed.
Lemma lem1520604 (x : real) : (term105 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1520507 x y)). Qed.
Lemma lem1520605 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520606 (x : real) : (term106 x) = (term134 x).
Proof. exact (MK_COMB (@lem1520605) (@lem1520604 x)). Qed.
Lemma lem1520608 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1520609 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1520608 real P Q). Qed.
Lemma lem1520610 (x : real) : (term135 x) = (term136 x).
Proof. exact (@lem1520609 (term137 x) (term138 x)). Qed.
Lemma lem1520611 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1520612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520613 (x : real) (y : real) : (term140 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1520612) (@lem1520611 x y)). Qed.
Lemma lem1520614 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1520615 (x : real) (y : real) : (term142 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1520613 x y) (@lem1520614 x y)). Qed.
Lemma lem1520616 (x : real) : (term143 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1520615 x y)). Qed.
Lemma lem1520617 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520618 (x : real) : (term135 x) = (term134 x).
Proof. exact (MK_COMB (@lem1520617) (@lem1520616 x)). Qed.
Lemma lem1520619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1520620 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1520619) (@lem1520618 x)). Qed.
Lemma lem1520621 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1520622 (x : real) : (term146 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1520621 x y)). Qed.
Lemma lem1520623 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520624 (x : real) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1520623) (@lem1520622 x)). Qed.
Lemma lem1520625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520626 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1520625) (@lem1520624 x)). Qed.
Lemma lem1520627 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1520628 (x : real) : (term151 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem1520627 x y)). Qed.
Lemma lem1520629 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520630 (x : real) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1520629) (@lem1520628 x)). Qed.
Lemma lem1520631 (x : real) : (term136 x) = (term154 x).
Proof. exact (MK_COMB (@lem1520626 x) (@lem1520630 x)). Qed.
Lemma lem1520632 (x : real) : ((term135 x) = (term136 x)) = ((term134 x) = (term154 x)).
Proof. exact (MK_COMB (@lem1520620 x) (@lem1520631 x)). Qed.
Lemma lem1520633 (x : real) : (term134 x) = (term154 x).
Proof. exact (EQ_MP (@lem1520632 x) (@lem1520610 x)). Qed.
Lemma lem1520738 (x : real) : (term106 x) = (term154 x).
Proof. exact (TRANS (@lem1520606 x) (@lem1520633 x)). Qed.
Lemma lem1520739 : term107 = term155.
Proof. exact (fun_ext (fun x : real => @lem1520738 x)). Qed.
Lemma lem1520740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520741 : term108 = term156.
Proof. exact (MK_COMB (@lem1520740) (@lem1520739)). Qed.
Lemma lem1520743 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1520744 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1520743 real P Q). Qed.
Lemma lem1520745 : term157 = term158.
Proof. exact (@lem1520744 term159 term160). Qed.
Lemma lem1520746 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1520747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520748 (x : real) : (term162 x) = (term150 x).
Proof. exact (MK_COMB (@lem1520747) (@lem1520746 x)). Qed.
Lemma lem1520749 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1520750 (x : real) : (term164 x) = (term154 x).
Proof. exact (MK_COMB (@lem1520748 x) (@lem1520749 x)). Qed.
Lemma lem1520751 : term165 = term155.
Proof. exact (fun_ext (fun x : real => @lem1520750 x)). Qed.
Lemma lem1520752 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520753 : term157 = term156.
Proof. exact (MK_COMB (@lem1520752) (@lem1520751)). Qed.
Lemma lem1520754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1520755 : term166 = term167.
Proof. exact (MK_COMB (@lem1520754) (@lem1520753)). Qed.
Lemma lem1520756 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1520757 : term168 = term159.
Proof. exact (fun_ext (fun x : real => @lem1520756 x)). Qed.
Lemma lem1520758 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520759 : term169 = term170.
Proof. exact (MK_COMB (@lem1520758) (@lem1520757)). Qed.
Lemma lem1520760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520761 : term171 = term172.
Proof. exact (MK_COMB (@lem1520760) (@lem1520759)). Qed.
Lemma lem1520762 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1520763 : term173 = term160.
Proof. exact (fun_ext (fun x : real => @lem1520762 x)). Qed.
Lemma lem1520764 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520765 : term174 = term175.
Proof. exact (MK_COMB (@lem1520764) (@lem1520763)). Qed.
Lemma lem1520766 : term158 = term176.
Proof. exact (MK_COMB (@lem1520761) (@lem1520765)). Qed.
Lemma lem1520767 : (term157 = term158) = (term156 = term176).
Proof. exact (MK_COMB (@lem1520755) (@lem1520766)). Qed.
Lemma lem1520768 : term156 = term176.
Proof. exact (EQ_MP (@lem1520767) (@lem1520745)). Qed.
Lemma lem1520881 : term108 = term176.
Proof. exact (TRANS (@lem1520741) (@lem1520768)). Qed.
Lemma lem1520883 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1520884 (P : real -> Prop) (Q : real -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem1520883 real P Q). Qed.
Lemma lem1520885 : term158 = term157.
Proof. exact (@lem1520884 term159 term160). Qed.
Lemma lem1520886 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1520887 : term168 = term159.
Proof. exact (fun_ext (fun x : real => @lem1520886 x)). Qed.
Lemma lem1520888 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520889 : term169 = term170.
Proof. exact (MK_COMB (@lem1520888) (@lem1520887)). Qed.
Lemma lem1520890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520891 : term171 = term172.
Proof. exact (MK_COMB (@lem1520890) (@lem1520889)). Qed.
Lemma lem1520892 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1520893 : term173 = term160.
Proof. exact (fun_ext (fun x : real => @lem1520892 x)). Qed.
Lemma lem1520894 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520895 : term174 = term175.
Proof. exact (MK_COMB (@lem1520894) (@lem1520893)). Qed.
Lemma lem1520896 : term158 = term176.
Proof. exact (MK_COMB (@lem1520891) (@lem1520895)). Qed.
Lemma lem1520897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1520898 : term177 = term178.
Proof. exact (MK_COMB (@lem1520897) (@lem1520896)). Qed.
Lemma lem1520899 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1520900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520901 (x : real) : (term162 x) = (term150 x).
Proof. exact (MK_COMB (@lem1520900) (@lem1520899 x)). Qed.
Lemma lem1520902 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1520903 (x : real) : (term164 x) = (term154 x).
Proof. exact (MK_COMB (@lem1520901 x) (@lem1520902 x)). Qed.
Lemma lem1520904 : term165 = term155.
Proof. exact (fun_ext (fun x : real => @lem1520903 x)). Qed.
Lemma lem1520905 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520906 : term157 = term156.
Proof. exact (MK_COMB (@lem1520905) (@lem1520904)). Qed.
Lemma lem1520907 : (term158 = term157) = (term176 = term156).
Proof. exact (MK_COMB (@lem1520898) (@lem1520906)). Qed.
Lemma lem1520908 : term176 = term156.
Proof. exact (EQ_MP (@lem1520907) (@lem1520885)). Qed.
Lemma lem1520910 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1520911 (P : real -> Prop) (Q : real -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem1520910 real P Q). Qed.
Lemma lem1520912 (x : real) : (term136 x) = (term135 x).
Proof. exact (@lem1520911 (term137 x) (term138 x)). Qed.
Lemma lem1520913 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1520914 (x : real) : (term146 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1520913 x y)). Qed.
Lemma lem1520915 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520916 (x : real) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1520915) (@lem1520914 x)). Qed.
Lemma lem1520917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520918 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1520917) (@lem1520916 x)). Qed.
Lemma lem1520919 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1520920 (x : real) : (term151 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem1520919 x y)). Qed.
Lemma lem1520921 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520922 (x : real) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1520921) (@lem1520920 x)). Qed.
Lemma lem1520923 (x : real) : (term136 x) = (term154 x).
Proof. exact (MK_COMB (@lem1520918 x) (@lem1520922 x)). Qed.
Lemma lem1520924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1520925 (x : real) : (term179 x) = (term180 x).
Proof. exact (MK_COMB (@lem1520924) (@lem1520923 x)). Qed.
Lemma lem1520926 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1520927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520928 (x : real) (y : real) : (term140 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1520927) (@lem1520926 x y)). Qed.
Lemma lem1520929 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1520930 (x : real) (y : real) : (term142 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1520928 x y) (@lem1520929 x y)). Qed.
Lemma lem1520931 (x : real) : (term143 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1520930 x y)). Qed.
Lemma lem1520932 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520933 (x : real) : (term135 x) = (term134 x).
Proof. exact (MK_COMB (@lem1520932) (@lem1520931 x)). Qed.
Lemma lem1520934 (x : real) : ((term136 x) = (term135 x)) = ((term154 x) = (term134 x)).
Proof. exact (MK_COMB (@lem1520925 x) (@lem1520933 x)). Qed.
Lemma lem1520935 (x : real) : (term154 x) = (term134 x).
Proof. exact (EQ_MP (@lem1520934 x) (@lem1520912 x)). Qed.
Lemma lem1520937 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1520938 (P : real -> Prop) (Q : real -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem1520937 real P Q). Qed.
Lemma lem1520939 (x : real) (y : real) : (term114 x y) = (term113 x y).
Proof. exact (@lem1520938 (term115 x y) (term116 x y)). Qed.
Lemma lem1520940 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1520941 (x : real) (y : real) : (term124 x y) = (term115 x y).
Proof. exact (fun_ext (fun z : real => @lem1520940 x y z)). Qed.
Lemma lem1520942 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520943 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1520942) (@lem1520941 x y)). Qed.
Lemma lem1520944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520945 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1520944) (@lem1520943 x y)). Qed.
Lemma lem1520946 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1520947 (x : real) (y : real) : (term129 x y) = (term116 x y).
Proof. exact (fun_ext (fun z : real => @lem1520946 x y z)). Qed.
Lemma lem1520948 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520949 (x : real) (y : real) : (term130 x y) = (term131 x y).
Proof. exact (MK_COMB (@lem1520948) (@lem1520947 x y)). Qed.
Lemma lem1520950 (x : real) (y : real) : (term114 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1520945 x y) (@lem1520949 x y)). Qed.
Lemma lem1520951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1520952 (x : real) (y : real) : (term181 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1520951) (@lem1520950 x y)). Qed.
Lemma lem1520953 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1520954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1520955 (x : real) (y : real) (z : real) : (term118 x y z) = (term101 x y z).
Proof. exact (MK_COMB (@lem1520954) (@lem1520953 x y z)). Qed.
Lemma lem1520956 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1520957 (x : real) (y : real) (z : real) : (term120 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1520955 x y z) (@lem1520956 x y z)). Qed.
Lemma lem1520958 (x : real) (y : real) : (term121 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1520957 x y z)). Qed.
Lemma lem1520959 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520960 (x : real) (y : real) : (term113 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1520959) (@lem1520958 x y)). Qed.
Lemma lem1520961 (x : real) (y : real) : ((term114 x y) = (term113 x y)) = ((term132 x y) = (term104 x y)).
Proof. exact (MK_COMB (@lem1520952 x y) (@lem1520960 x y)). Qed.
Lemma lem1520962 (x : real) (y : real) : (term132 x y) = (term104 x y).
Proof. exact (EQ_MP (@lem1520961 x y) (@lem1520939 x y)). Qed.
Lemma lem1520963 (x : real) : (term133 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1520962 x y)). Qed.
Lemma lem1520964 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520965 (x : real) : (term134 x) = (term106 x).
Proof. exact (MK_COMB (@lem1520964) (@lem1520963 x)). Qed.
Lemma lem1520966 (x : real) : (term154 x) = (term106 x).
Proof. exact (TRANS (@lem1520935 x) (@lem1520965 x)). Qed.
Lemma lem1520967 : term155 = term107.
Proof. exact (fun_ext (fun x : real => @lem1520966 x)). Qed.
Lemma lem1520968 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1520969 : term156 = term108.
Proof. exact (MK_COMB (@lem1520968) (@lem1520967)). Qed.
Lemma lem1520970 : term176 = term108.
Proof. exact (TRANS (@lem1520908) (@lem1520969)). Qed.
Lemma lem1520971 : term108 = term108.
Proof. exact (TRANS (@lem1520881) (@lem1520970)). Qed.
Lemma lem1520974 : term21 = term108.
Proof. exact (TRANS (@lem1520472) (@lem1520971)). Qed.
Lemma lem1520991 (x : real) (y : real) (z : real) : (term99 x y z) = (term183 x y z).
Proof. exact (@lem19367 (term78 x y z) (term74 x y z) ((term54 x y z) = term31)). Qed.
Lemma lem1521008 (x : real) (y : real) (z : real) : (term85 x y z) = (term184 x y z).
Proof. exact (@lem19158 (term78 x y z) ((term54 x y z) = term31) (term74 x y z)). Qed.
Lemma lem1521009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1521010 (x : real) (y : real) (z : real) : (term101 x y z) = (term185 x y z).
Proof. exact (MK_COMB (@lem1521009) (@lem1521008 x y z)). Qed.
Lemma lem1521011 (x : real) (y : real) (z : real) : (term102 x y z) = (term186 x y z).
Proof. exact (MK_COMB (@lem1521010 x y z) (@lem1520991 x y z)). Qed.
Lemma lem1521012 (x : real) (y : real) : (term103 x y) = (term187 x y).
Proof. exact (fun_ext (fun z : real => @lem1521011 x y z)). Qed.
Lemma lem1521013 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521014 (x : real) (y : real) : (term104 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1521013) (@lem1521012 x y)). Qed.
Lemma lem1521015 (x : real) : (term105 x) = (term189 x).
Proof. exact (fun_ext (fun y : real => @lem1521014 x y)). Qed.
Lemma lem1521016 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521017 (x : real) : (term106 x) = (term190 x).
Proof. exact (MK_COMB (@lem1521016) (@lem1521015 x)). Qed.
Lemma lem1521018 : term107 = term191.
Proof. exact (fun_ext (fun x : real => @lem1521017 x)). Qed.
Lemma lem1521019 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521020 : term108 = term192.
Proof. exact (MK_COMB (@lem1521019) (@lem1521018)). Qed.
Lemma lem1521021 : term21 = term192.
Proof. exact (TRANS (@lem1520974) (@lem1521020)). Qed.
Lemma lem1521043 (x : real) (y : real) (z : real) (h1 : term186 x y z) : term186 x y z.
Proof. exact (h1). Qed.
Lemma lem1521044 (x : real) (y : real) (z : real) (h1 : term184 x y z) : term184 x y z.
Proof. exact (h1). Qed.
Lemma lem1521045 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term193 x y z.
Proof. exact (h1). Qed.
Lemma lem1521046 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term78 x y z.
Proof. exact (proj2 (@lem1521045 x y z h1)). Qed.
Lemma lem1521047 (x : real) (y : real) (z : real) (h1 : term193 x y z) : (term54 x y z) = term31.
Proof. exact (proj1 (@lem1521045 x y z h1)). Qed.
Lemma lem1521049 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521050 : term195 = term196.
Proof. exact (@lem1521049 (NUMERAL 0) term45). Qed.
Lemma lem1521051 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1521052 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1521053 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1521052 h1) (fun h1 : term196 = True => @lem1521051)). Qed.
Lemma lem1521054 : term196 = True.
Proof. exact (EQ_MP (@lem1521053) (@lem1521051)). Qed.
Lemma lem1521055 : term195 = True.
Proof. exact (TRANS (@lem1521050) (@lem1521054)). Qed.
Lemma lem1521056 : True = term195.
Proof. exact (SYM (@lem1521055)). Qed.
Lemma lem1521057 : term195.
Proof. exact (EQ_MP (@lem1521056) (@lem0)). Qed.
Lemma lem1521058 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term198 x y z.
Proof. exact (conj (@lem1521057) (@lem1521046 x y z h1)). Qed.
Lemma lem1521060 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1521061 (x : real) (y : real) (z : real) : term200 x y z.
Proof. exact (@lem1521060 term48 (term54 x y z)). Qed.
Lemma lem1521062 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term201 x y z.
Proof. exact (@lem1521061 x y z (@lem1521058 x y z h1)). Qed.
Lemma lem1521063 (x : real) (y : real) (z : real) : (term202 x y z) = (term54 x y z).
Proof. exact (@lem1483460 (term54 x y z)). Qed.
Lemma lem1521064 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521065 (x : real) (y : real) (z : real) : (term203 x y z) = (term76 x y z).
Proof. exact (MK_COMB (@lem1521064) (@lem1521063 x y z)). Qed.
Lemma lem1521066 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521067 (x : real) (y : real) (z : real) : (term201 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1521065 x y z) (@lem1521066)). Qed.
Lemma lem1521068 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term78 x y z.
Proof. exact (EQ_MP (@lem1521067 x y z) (@lem1521062 x y z h1)). Qed.
Lemma lem1521070 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1521071 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1521070 (term54 x y z)). Qed.
Lemma lem1521072 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term206 x y z.
Proof. exact (@lem1521071 x y z (@lem1521047 x y z h1)). Qed.
Lemma lem1521073 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term207 x y z.
Proof. exact (@lem1521072 x y z h1 term37). Qed.
Lemma lem1521074 (x : real) (y : real) (z : real) : (term207 x y z) = ((term64 x y z) = term31).
Proof. exact (eq_refl (term207 x y z)). Qed.
Lemma lem1521075 (x : real) (y : real) (z : real) (h1 : term193 x y z) : (term64 x y z) = term31.
Proof. exact (EQ_MP (@lem1521074 x y z) (@lem1521073 x y z h1)). Qed.
Lemma lem1521076 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem1483508 x term37 (term53 y z)). Qed.
Lemma lem1521077 (y : real) (z : real) : (term66 y z) = (term67 y z).
Proof. exact (@lem1483508 (term38 y) term37 z). Qed.
Lemma lem1521078 (z : real) : (term38 z) = (term38 z).
Proof. exact (eq_refl (term38 z)). Qed.
Lemma lem1521079 (y : real) : (term39 y) = (term40 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1521081 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1521082 : term43 = term44.
Proof. exact (@lem1521081 term45 term45). Qed.
Lemma lem1521083 : (term46 = (BIT1 0)) = (term47 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1521084 : term47 = term45.
Proof. exact (EQ_MP (@lem1521083) (@lem940073)). Qed.
Lemma lem1521085 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1521086 : term44 = term48.
Proof. exact (MK_COMB (@lem1521085) (@lem1521084)). Qed.
Lemma lem1521087 : term43 = term48.
Proof. exact (TRANS (@lem1521082) (@lem1521086)). Qed.
Lemma lem1521088 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521089 : term49 = term50.
Proof. exact (MK_COMB (@lem1521088) (@lem1521087)). Qed.
Lemma lem1521090 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521091 (y : real) : (term40 y) = (term51 y).
Proof. exact (MK_COMB (@lem1521089) (@lem1521090 y)). Qed.
Lemma lem1521092 (y : real) : (term39 y) = (term51 y).
Proof. exact (TRANS (@lem1521079 y) (@lem1521091 y)). Qed.
Lemma lem1521093 (y : real) : (term51 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1521094 (y : real) : (term39 y) = y.
Proof. exact (TRANS (@lem1521092 y) (@lem1521093 y)). Qed.
Lemma lem1521095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521096 (y : real) : (term68 y) = (real_add y).
Proof. exact (MK_COMB (@lem1521095) (@lem1521094 y)). Qed.
Lemma lem1521097 (y : real) (z : real) : (term67 y z) = (term32 y z).
Proof. exact (MK_COMB (@lem1521096 y) (@lem1521078 z)). Qed.
Lemma lem1521098 (y : real) (z : real) : (term66 y z) = (term32 y z).
Proof. exact (TRANS (@lem1521077 y z) (@lem1521097 y z)). Qed.
Lemma lem1521101 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1521102 (x : real) (y : real) (z : real) : (term65 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1521101 x) (@lem1521098 y z)). Qed.
Lemma lem1521103 (x : real) (y : real) (z : real) : (term64 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1521076 x y z) (@lem1521102 x y z)). Qed.
Lemma lem1521104 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1521105 (x : real) (y : real) (z : real) : (term208 x y z) = (term209 x y z).
Proof. exact (MK_COMB (@lem1521104) (@lem1521103 x y z)). Qed.
Lemma lem1521106 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521107 (x : real) (y : real) (z : real) : ((term64 x y z) = term31) = ((term69 x y z) = term31).
Proof. exact (MK_COMB (@lem1521105 x y z) (@lem1521106)). Qed.
Lemma lem1521108 (x : real) (y : real) (z : real) (h1 : term193 x y z) : (term69 x y z) = term31.
Proof. exact (EQ_MP (@lem1521107 x y z) (@lem1521075 x y z h1)). Qed.
Lemma lem1521109 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term210 x y z.
Proof. exact (conj (@lem1521108 x y z h1) (@lem1521068 x y z h1)). Qed.
Lemma lem1521111 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1521112 (x : real) (y : real) (z : real) : term212 x y z.
Proof. exact (@lem1521111 (term69 x y z) (term54 x y z)). Qed.
Lemma lem1521113 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term213 x y z.
Proof. exact (@lem1521112 x y z (@lem1521109 x y z h1)). Qed.
Lemma lem1521114 (x : real) (y : real) (z : real) : (term214 x y z) = (term215 x y z).
Proof. exact (@lem1483480 (term38 x) x (term32 y z) (term53 y z)). Qed.
Lemma lem1521115 (x : real) : (term216 x) = (term217 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1521117 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521118 : term219 = term31.
Proof. exact (@lem1521117 term45). Qed.
Lemma lem1521119 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521120 : term220 = term221.
Proof. exact (MK_COMB (@lem1521119) (@lem1521118)). Qed.
Lemma lem1521121 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1521122 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1521120) (@lem1521121 x)). Qed.
Lemma lem1521123 (x : real) : (term216 x) = (term222 x).
Proof. exact (TRANS (@lem1521115 x) (@lem1521122 x)). Qed.
Lemma lem1521124 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1521125 (x : real) : (term216 x) = term31.
Proof. exact (TRANS (@lem1521123 x) (@lem1521124 x)). Qed.
Lemma lem1521126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521127 (x : real) : (term223 x) = term224.
Proof. exact (MK_COMB (@lem1521126) (@lem1521125 x)). Qed.
Lemma lem1521128 (y : real) (z : real) : (term225 y z) = (term226 y z).
Proof. exact (@lem1483480 y (term38 y) (term38 z) z). Qed.
Lemma lem1521129 (y : real) : (term227 y) = (term217 y).
Proof. exact (@lem1483442 term37 y). Qed.
Lemma lem1521131 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521132 : term219 = term31.
Proof. exact (@lem1521131 term45). Qed.
Lemma lem1521133 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521134 : term220 = term221.
Proof. exact (MK_COMB (@lem1521133) (@lem1521132)). Qed.
Lemma lem1521135 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521136 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1521134) (@lem1521135 y)). Qed.
Lemma lem1521137 (y : real) : (term227 y) = (term222 y).
Proof. exact (TRANS (@lem1521129 y) (@lem1521136 y)). Qed.
Lemma lem1521138 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1521139 (y : real) : (term227 y) = term31.
Proof. exact (TRANS (@lem1521137 y) (@lem1521138 y)). Qed.
Lemma lem1521140 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521141 (y : real) : (term228 y) = term224.
Proof. exact (MK_COMB (@lem1521140) (@lem1521139 y)). Qed.
Lemma lem1521142 (z : real) : (term216 z) = (term217 z).
Proof. exact (@lem1483440 term37 z). Qed.
Lemma lem1521144 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521145 : term219 = term31.
Proof. exact (@lem1521144 term45). Qed.
Lemma lem1521146 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521147 : term220 = term221.
Proof. exact (MK_COMB (@lem1521146) (@lem1521145)). Qed.
Lemma lem1521148 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521149 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1521147) (@lem1521148 z)). Qed.
Lemma lem1521150 (z : real) : (term216 z) = (term222 z).
Proof. exact (TRANS (@lem1521142 z) (@lem1521149 z)). Qed.
Lemma lem1521151 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1521152 (z : real) : (term216 z) = term31.
Proof. exact (TRANS (@lem1521150 z) (@lem1521151 z)). Qed.
Lemma lem1521153 (y : real) (z : real) : (term226 y z) = term229.
Proof. exact (MK_COMB (@lem1521141 y) (@lem1521152 z)). Qed.
Lemma lem1521154 (y : real) (z : real) : (term225 y z) = term229.
Proof. exact (TRANS (@lem1521128 y z) (@lem1521153 y z)). Qed.
Lemma lem1521155 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521156 (y : real) (z : real) : (term225 y z) = term31.
Proof. exact (TRANS (@lem1521154 y z) (@lem1521155)). Qed.
Lemma lem1521157 (x : real) (y : real) (z : real) : (term215 x y z) = term229.
Proof. exact (MK_COMB (@lem1521127 x) (@lem1521156 y z)). Qed.
Lemma lem1521158 (x : real) (y : real) (z : real) : (term214 x y z) = term229.
Proof. exact (TRANS (@lem1521114 x y z) (@lem1521157 x y z)). Qed.
Lemma lem1521159 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521160 (x : real) (y : real) (z : real) : (term214 x y z) = term31.
Proof. exact (TRANS (@lem1521158 x y z) (@lem1521159)). Qed.
Lemma lem1521161 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521162 (x : real) (y : real) (z : real) : (term230 x y z) = term231.
Proof. exact (MK_COMB (@lem1521161) (@lem1521160 x y z)). Qed.
Lemma lem1521163 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521164 (x : real) (y : real) (z : real) : (term213 x y z) = term232.
Proof. exact (MK_COMB (@lem1521162 x y z) (@lem1521163)). Qed.
Lemma lem1521165 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term232.
Proof. exact (EQ_MP (@lem1521164 x y z) (@lem1521113 x y z h1)). Qed.
Lemma lem1521167 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521168 : term232 = term233.
Proof. exact (@lem1521167 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1521169 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1521170 : term232 = False.
Proof. exact (TRANS (@lem1521168) (@lem1521169)). Qed.
Lemma lem1521171 (x : real) (y : real) (z : real) (h1 : term193 x y z) : False.
Proof. exact (EQ_MP (@lem1521170) (@lem1521165 x y z h1)). Qed.
Lemma lem1521172 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term234 x y z.
Proof. exact (h1). Qed.
Lemma lem1521173 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term74 x y z.
Proof. exact (proj2 (@lem1521172 x y z h1)). Qed.
Lemma lem1521174 (x : real) (y : real) (z : real) (h1 : term234 x y z) : (term54 x y z) = term31.
Proof. exact (proj1 (@lem1521172 x y z h1)). Qed.
Lemma lem1521176 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521177 : term195 = term196.
Proof. exact (@lem1521176 (NUMERAL 0) term45). Qed.
Lemma lem1521178 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1521179 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1521180 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1521179 h1) (fun h1 : term196 = True => @lem1521178)). Qed.
Lemma lem1521181 : term196 = True.
Proof. exact (EQ_MP (@lem1521180) (@lem1521178)). Qed.
Lemma lem1521182 : term195 = True.
Proof. exact (TRANS (@lem1521177) (@lem1521181)). Qed.
Lemma lem1521183 : True = term195.
Proof. exact (SYM (@lem1521182)). Qed.
Lemma lem1521184 : term195.
Proof. exact (EQ_MP (@lem1521183) (@lem0)). Qed.
Lemma lem1521185 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term235 x y z.
Proof. exact (conj (@lem1521184) (@lem1521173 x y z h1)). Qed.
Lemma lem1521187 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1521188 (x : real) (y : real) (z : real) : term236 x y z.
Proof. exact (@lem1521187 term48 (term69 x y z)). Qed.
Lemma lem1521189 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term237 x y z.
Proof. exact (@lem1521188 x y z (@lem1521185 x y z h1)). Qed.
Lemma lem1521190 (x : real) (y : real) (z : real) : (term238 x y z) = (term69 x y z).
Proof. exact (@lem1483460 (term69 x y z)). Qed.
Lemma lem1521191 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521192 (x : real) (y : real) (z : real) : (term239 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1521191) (@lem1521190 x y z)). Qed.
Lemma lem1521193 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521194 (x : real) (y : real) (z : real) : (term237 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1521192 x y z) (@lem1521193)). Qed.
Lemma lem1521195 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term74 x y z.
Proof. exact (EQ_MP (@lem1521194 x y z) (@lem1521189 x y z h1)). Qed.
Lemma lem1521197 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1521198 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1521197 (term54 x y z)). Qed.
Lemma lem1521199 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term206 x y z.
Proof. exact (@lem1521198 x y z (@lem1521174 x y z h1)). Qed.
Lemma lem1521200 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term240 x y z.
Proof. exact (@lem1521199 x y z h1 term48). Qed.
Lemma lem1521201 (x : real) (y : real) (z : real) : (term240 x y z) = ((term202 x y z) = term31).
Proof. exact (eq_refl (term240 x y z)). Qed.
Lemma lem1521202 (x : real) (y : real) (z : real) (h1 : term234 x y z) : (term202 x y z) = term31.
Proof. exact (EQ_MP (@lem1521201 x y z) (@lem1521200 x y z h1)). Qed.
Lemma lem1521203 (x : real) (y : real) (z : real) : (term202 x y z) = (term54 x y z).
Proof. exact (@lem1483460 (term54 x y z)). Qed.
Lemma lem1521204 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1521205 (x : real) (y : real) (z : real) : (term241 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1521204) (@lem1521203 x y z)). Qed.
Lemma lem1521206 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521207 (x : real) (y : real) (z : real) : ((term202 x y z) = term31) = ((term54 x y z) = term31).
Proof. exact (MK_COMB (@lem1521205 x y z) (@lem1521206)). Qed.
Lemma lem1521208 (x : real) (y : real) (z : real) (h1 : term234 x y z) : (term54 x y z) = term31.
Proof. exact (EQ_MP (@lem1521207 x y z) (@lem1521202 x y z h1)). Qed.
Lemma lem1521209 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term234 x y z.
Proof. exact (conj (@lem1521208 x y z h1) (@lem1521195 x y z h1)). Qed.
Lemma lem1521211 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1521212 (x : real) (y : real) (z : real) : term242 x y z.
Proof. exact (@lem1521211 (term54 x y z) (term69 x y z)). Qed.
Lemma lem1521213 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term243 x y z.
Proof. exact (@lem1521212 x y z (@lem1521209 x y z h1)). Qed.
Lemma lem1521214 (x : real) (y : real) (z : real) : (term244 x y z) = (term245 x y z).
Proof. exact (@lem1483480 x (term38 x) (term53 y z) (term32 y z)). Qed.
Lemma lem1521215 (x : real) : (term227 x) = (term217 x).
Proof. exact (@lem1483442 term37 x). Qed.
Lemma lem1521217 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521218 : term219 = term31.
Proof. exact (@lem1521217 term45). Qed.
Lemma lem1521219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521220 : term220 = term221.
Proof. exact (MK_COMB (@lem1521219) (@lem1521218)). Qed.
Lemma lem1521221 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1521222 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1521220) (@lem1521221 x)). Qed.
Lemma lem1521223 (x : real) : (term227 x) = (term222 x).
Proof. exact (TRANS (@lem1521215 x) (@lem1521222 x)). Qed.
Lemma lem1521224 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1521225 (x : real) : (term227 x) = term31.
Proof. exact (TRANS (@lem1521223 x) (@lem1521224 x)). Qed.
Lemma lem1521226 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521227 (x : real) : (term228 x) = term224.
Proof. exact (MK_COMB (@lem1521226) (@lem1521225 x)). Qed.
Lemma lem1521228 (y : real) (z : real) : (term246 y z) = (term247 y z).
Proof. exact (@lem1483480 (term38 y) y z (term38 z)). Qed.
Lemma lem1521229 (y : real) : (term216 y) = (term217 y).
Proof. exact (@lem1483440 term37 y). Qed.
Lemma lem1521231 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521232 : term219 = term31.
Proof. exact (@lem1521231 term45). Qed.
Lemma lem1521233 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521234 : term220 = term221.
Proof. exact (MK_COMB (@lem1521233) (@lem1521232)). Qed.
Lemma lem1521235 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521236 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1521234) (@lem1521235 y)). Qed.
Lemma lem1521237 (y : real) : (term216 y) = (term222 y).
Proof. exact (TRANS (@lem1521229 y) (@lem1521236 y)). Qed.
Lemma lem1521238 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1521239 (y : real) : (term216 y) = term31.
Proof. exact (TRANS (@lem1521237 y) (@lem1521238 y)). Qed.
Lemma lem1521240 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521241 (y : real) : (term223 y) = term224.
Proof. exact (MK_COMB (@lem1521240) (@lem1521239 y)). Qed.
Lemma lem1521242 (z : real) : (term227 z) = (term217 z).
Proof. exact (@lem1483442 term37 z). Qed.
Lemma lem1521244 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521245 : term219 = term31.
Proof. exact (@lem1521244 term45). Qed.
Lemma lem1521246 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521247 : term220 = term221.
Proof. exact (MK_COMB (@lem1521246) (@lem1521245)). Qed.
Lemma lem1521248 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521249 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1521247) (@lem1521248 z)). Qed.
Lemma lem1521250 (z : real) : (term227 z) = (term222 z).
Proof. exact (TRANS (@lem1521242 z) (@lem1521249 z)). Qed.
Lemma lem1521251 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1521252 (z : real) : (term227 z) = term31.
Proof. exact (TRANS (@lem1521250 z) (@lem1521251 z)). Qed.
Lemma lem1521253 (y : real) (z : real) : (term247 y z) = term229.
Proof. exact (MK_COMB (@lem1521241 y) (@lem1521252 z)). Qed.
Lemma lem1521254 (y : real) (z : real) : (term246 y z) = term229.
Proof. exact (TRANS (@lem1521228 y z) (@lem1521253 y z)). Qed.
Lemma lem1521255 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521256 (y : real) (z : real) : (term246 y z) = term31.
Proof. exact (TRANS (@lem1521254 y z) (@lem1521255)). Qed.
Lemma lem1521257 (x : real) (y : real) (z : real) : (term245 x y z) = term229.
Proof. exact (MK_COMB (@lem1521227 x) (@lem1521256 y z)). Qed.
Lemma lem1521258 (x : real) (y : real) (z : real) : (term244 x y z) = term229.
Proof. exact (TRANS (@lem1521214 x y z) (@lem1521257 x y z)). Qed.
Lemma lem1521259 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521260 (x : real) (y : real) (z : real) : (term244 x y z) = term31.
Proof. exact (TRANS (@lem1521258 x y z) (@lem1521259)). Qed.
Lemma lem1521261 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521262 (x : real) (y : real) (z : real) : (term248 x y z) = term231.
Proof. exact (MK_COMB (@lem1521261) (@lem1521260 x y z)). Qed.
Lemma lem1521263 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521264 (x : real) (y : real) (z : real) : (term243 x y z) = term232.
Proof. exact (MK_COMB (@lem1521262 x y z) (@lem1521263)). Qed.
Lemma lem1521265 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term232.
Proof. exact (EQ_MP (@lem1521264 x y z) (@lem1521213 x y z h1)). Qed.
Lemma lem1521267 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521268 : term232 = term233.
Proof. exact (@lem1521267 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1521269 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1521270 : term232 = False.
Proof. exact (TRANS (@lem1521268) (@lem1521269)). Qed.
Lemma lem1521271 (x : real) (y : real) (z : real) (h1 : term234 x y z) : False.
Proof. exact (EQ_MP (@lem1521270) (@lem1521265 x y z h1)). Qed.
Lemma lem1521272 (x : real) (y : real) (z : real) (h1 : term184 x y z) : False.
Proof. exact (or_elim (@lem1521044 x y z h1) (fun h0 : term193 x y z => @lem1521171 x y z h0) (fun h0 : term234 x y z => @lem1521271 x y z h0)). Qed.
Lemma lem1521273 (x : real) (y : real) (z : real) (h1 : term183 x y z) : term183 x y z.
Proof. exact (h1). Qed.
Lemma lem1521274 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term249 x y z.
Proof. exact (h1). Qed.
Lemma lem1521275 (x : real) (y : real) (z : real) (h1 : term249 x y z) : (term54 x y z) = term31.
Proof. exact (proj2 (@lem1521274 x y z h1)). Qed.
Lemma lem1521276 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term78 x y z.
Proof. exact (proj1 (@lem1521274 x y z h1)). Qed.
Lemma lem1521278 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521279 : term195 = term196.
Proof. exact (@lem1521278 (NUMERAL 0) term45). Qed.
Lemma lem1521280 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1521281 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1521282 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1521281 h1) (fun h1 : term196 = True => @lem1521280)). Qed.
Lemma lem1521283 : term196 = True.
Proof. exact (EQ_MP (@lem1521282) (@lem1521280)). Qed.
Lemma lem1521284 : term195 = True.
Proof. exact (TRANS (@lem1521279) (@lem1521283)). Qed.
Lemma lem1521285 : True = term195.
Proof. exact (SYM (@lem1521284)). Qed.
Lemma lem1521286 : term195.
Proof. exact (EQ_MP (@lem1521285) (@lem0)). Qed.
Lemma lem1521287 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term198 x y z.
Proof. exact (conj (@lem1521286) (@lem1521276 x y z h1)). Qed.
Lemma lem1521289 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1521290 (x : real) (y : real) (z : real) : term200 x y z.
Proof. exact (@lem1521289 term48 (term54 x y z)). Qed.
Lemma lem1521291 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term201 x y z.
Proof. exact (@lem1521290 x y z (@lem1521287 x y z h1)). Qed.
Lemma lem1521292 (x : real) (y : real) (z : real) : (term202 x y z) = (term54 x y z).
Proof. exact (@lem1483460 (term54 x y z)). Qed.
Lemma lem1521293 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521294 (x : real) (y : real) (z : real) : (term203 x y z) = (term76 x y z).
Proof. exact (MK_COMB (@lem1521293) (@lem1521292 x y z)). Qed.
Lemma lem1521295 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521296 (x : real) (y : real) (z : real) : (term201 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1521294 x y z) (@lem1521295)). Qed.
Lemma lem1521297 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term78 x y z.
Proof. exact (EQ_MP (@lem1521296 x y z) (@lem1521291 x y z h1)). Qed.
Lemma lem1521299 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1521300 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1521299 (term54 x y z)). Qed.
Lemma lem1521301 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term206 x y z.
Proof. exact (@lem1521300 x y z (@lem1521275 x y z h1)). Qed.
Lemma lem1521302 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term207 x y z.
Proof. exact (@lem1521301 x y z h1 term37). Qed.
Lemma lem1521303 (x : real) (y : real) (z : real) : (term207 x y z) = ((term64 x y z) = term31).
Proof. exact (eq_refl (term207 x y z)). Qed.
Lemma lem1521304 (x : real) (y : real) (z : real) (h1 : term249 x y z) : (term64 x y z) = term31.
Proof. exact (EQ_MP (@lem1521303 x y z) (@lem1521302 x y z h1)). Qed.
Lemma lem1521305 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (@lem1483508 x term37 (term53 y z)). Qed.
Lemma lem1521306 (y : real) (z : real) : (term66 y z) = (term67 y z).
Proof. exact (@lem1483508 (term38 y) term37 z). Qed.
Lemma lem1521307 (z : real) : (term38 z) = (term38 z).
Proof. exact (eq_refl (term38 z)). Qed.
Lemma lem1521308 (y : real) : (term39 y) = (term40 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1521310 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1521311 : term43 = term44.
Proof. exact (@lem1521310 term45 term45). Qed.
Lemma lem1521312 : (term46 = (BIT1 0)) = (term47 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1521313 : term47 = term45.
Proof. exact (EQ_MP (@lem1521312) (@lem940073)). Qed.
Lemma lem1521314 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1521315 : term44 = term48.
Proof. exact (MK_COMB (@lem1521314) (@lem1521313)). Qed.
Lemma lem1521316 : term43 = term48.
Proof. exact (TRANS (@lem1521311) (@lem1521315)). Qed.
Lemma lem1521317 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521318 : term49 = term50.
Proof. exact (MK_COMB (@lem1521317) (@lem1521316)). Qed.
Lemma lem1521319 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521320 (y : real) : (term40 y) = (term51 y).
Proof. exact (MK_COMB (@lem1521318) (@lem1521319 y)). Qed.
Lemma lem1521321 (y : real) : (term39 y) = (term51 y).
Proof. exact (TRANS (@lem1521308 y) (@lem1521320 y)). Qed.
Lemma lem1521322 (y : real) : (term51 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1521323 (y : real) : (term39 y) = y.
Proof. exact (TRANS (@lem1521321 y) (@lem1521322 y)). Qed.
Lemma lem1521324 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521325 (y : real) : (term68 y) = (real_add y).
Proof. exact (MK_COMB (@lem1521324) (@lem1521323 y)). Qed.
Lemma lem1521326 (y : real) (z : real) : (term67 y z) = (term32 y z).
Proof. exact (MK_COMB (@lem1521325 y) (@lem1521307 z)). Qed.
Lemma lem1521327 (y : real) (z : real) : (term66 y z) = (term32 y z).
Proof. exact (TRANS (@lem1521306 y z) (@lem1521326 y z)). Qed.
Lemma lem1521330 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1521331 (x : real) (y : real) (z : real) : (term65 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1521330 x) (@lem1521327 y z)). Qed.
Lemma lem1521332 (x : real) (y : real) (z : real) : (term64 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1521305 x y z) (@lem1521331 x y z)). Qed.
Lemma lem1521333 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1521334 (x : real) (y : real) (z : real) : (term208 x y z) = (term209 x y z).
Proof. exact (MK_COMB (@lem1521333) (@lem1521332 x y z)). Qed.
Lemma lem1521335 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521336 (x : real) (y : real) (z : real) : ((term64 x y z) = term31) = ((term69 x y z) = term31).
Proof. exact (MK_COMB (@lem1521334 x y z) (@lem1521335)). Qed.
Lemma lem1521337 (x : real) (y : real) (z : real) (h1 : term249 x y z) : (term69 x y z) = term31.
Proof. exact (EQ_MP (@lem1521336 x y z) (@lem1521304 x y z h1)). Qed.
Lemma lem1521338 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term210 x y z.
Proof. exact (conj (@lem1521337 x y z h1) (@lem1521297 x y z h1)). Qed.
Lemma lem1521340 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1521341 (x : real) (y : real) (z : real) : term212 x y z.
Proof. exact (@lem1521340 (term69 x y z) (term54 x y z)). Qed.
Lemma lem1521342 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term213 x y z.
Proof. exact (@lem1521341 x y z (@lem1521338 x y z h1)). Qed.
Lemma lem1521343 (x : real) (y : real) (z : real) : (term214 x y z) = (term215 x y z).
Proof. exact (@lem1483480 (term38 x) x (term32 y z) (term53 y z)). Qed.
Lemma lem1521344 (x : real) : (term216 x) = (term217 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1521346 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521347 : term219 = term31.
Proof. exact (@lem1521346 term45). Qed.
Lemma lem1521348 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521349 : term220 = term221.
Proof. exact (MK_COMB (@lem1521348) (@lem1521347)). Qed.
Lemma lem1521350 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1521351 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1521349) (@lem1521350 x)). Qed.
Lemma lem1521352 (x : real) : (term216 x) = (term222 x).
Proof. exact (TRANS (@lem1521344 x) (@lem1521351 x)). Qed.
Lemma lem1521353 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1521354 (x : real) : (term216 x) = term31.
Proof. exact (TRANS (@lem1521352 x) (@lem1521353 x)). Qed.
Lemma lem1521355 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521356 (x : real) : (term223 x) = term224.
Proof. exact (MK_COMB (@lem1521355) (@lem1521354 x)). Qed.
Lemma lem1521357 (y : real) (z : real) : (term225 y z) = (term226 y z).
Proof. exact (@lem1483480 y (term38 y) (term38 z) z). Qed.
Lemma lem1521358 (y : real) : (term227 y) = (term217 y).
Proof. exact (@lem1483442 term37 y). Qed.
Lemma lem1521360 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521361 : term219 = term31.
Proof. exact (@lem1521360 term45). Qed.
Lemma lem1521362 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521363 : term220 = term221.
Proof. exact (MK_COMB (@lem1521362) (@lem1521361)). Qed.
Lemma lem1521364 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521365 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1521363) (@lem1521364 y)). Qed.
Lemma lem1521366 (y : real) : (term227 y) = (term222 y).
Proof. exact (TRANS (@lem1521358 y) (@lem1521365 y)). Qed.
Lemma lem1521367 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1521368 (y : real) : (term227 y) = term31.
Proof. exact (TRANS (@lem1521366 y) (@lem1521367 y)). Qed.
Lemma lem1521369 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521370 (y : real) : (term228 y) = term224.
Proof. exact (MK_COMB (@lem1521369) (@lem1521368 y)). Qed.
Lemma lem1521371 (z : real) : (term216 z) = (term217 z).
Proof. exact (@lem1483440 term37 z). Qed.
Lemma lem1521373 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521374 : term219 = term31.
Proof. exact (@lem1521373 term45). Qed.
Lemma lem1521375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521376 : term220 = term221.
Proof. exact (MK_COMB (@lem1521375) (@lem1521374)). Qed.
Lemma lem1521377 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521378 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1521376) (@lem1521377 z)). Qed.
Lemma lem1521379 (z : real) : (term216 z) = (term222 z).
Proof. exact (TRANS (@lem1521371 z) (@lem1521378 z)). Qed.
Lemma lem1521380 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1521381 (z : real) : (term216 z) = term31.
Proof. exact (TRANS (@lem1521379 z) (@lem1521380 z)). Qed.
Lemma lem1521382 (y : real) (z : real) : (term226 y z) = term229.
Proof. exact (MK_COMB (@lem1521370 y) (@lem1521381 z)). Qed.
Lemma lem1521383 (y : real) (z : real) : (term225 y z) = term229.
Proof. exact (TRANS (@lem1521357 y z) (@lem1521382 y z)). Qed.
Lemma lem1521384 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521385 (y : real) (z : real) : (term225 y z) = term31.
Proof. exact (TRANS (@lem1521383 y z) (@lem1521384)). Qed.
Lemma lem1521386 (x : real) (y : real) (z : real) : (term215 x y z) = term229.
Proof. exact (MK_COMB (@lem1521356 x) (@lem1521385 y z)). Qed.
Lemma lem1521387 (x : real) (y : real) (z : real) : (term214 x y z) = term229.
Proof. exact (TRANS (@lem1521343 x y z) (@lem1521386 x y z)). Qed.
Lemma lem1521388 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521389 (x : real) (y : real) (z : real) : (term214 x y z) = term31.
Proof. exact (TRANS (@lem1521387 x y z) (@lem1521388)). Qed.
Lemma lem1521390 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521391 (x : real) (y : real) (z : real) : (term230 x y z) = term231.
Proof. exact (MK_COMB (@lem1521390) (@lem1521389 x y z)). Qed.
Lemma lem1521392 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521393 (x : real) (y : real) (z : real) : (term213 x y z) = term232.
Proof. exact (MK_COMB (@lem1521391 x y z) (@lem1521392)). Qed.
Lemma lem1521394 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term232.
Proof. exact (EQ_MP (@lem1521393 x y z) (@lem1521342 x y z h1)). Qed.
Lemma lem1521396 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521397 : term232 = term233.
Proof. exact (@lem1521396 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1521398 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1521399 : term232 = False.
Proof. exact (TRANS (@lem1521397) (@lem1521398)). Qed.
Lemma lem1521400 (x : real) (y : real) (z : real) (h1 : term249 x y z) : False.
Proof. exact (EQ_MP (@lem1521399) (@lem1521394 x y z h1)). Qed.
Lemma lem1521401 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term250 x y z.
Proof. exact (h1). Qed.
Lemma lem1521402 (x : real) (y : real) (z : real) (h1 : term250 x y z) : (term54 x y z) = term31.
Proof. exact (proj2 (@lem1521401 x y z h1)). Qed.
Lemma lem1521403 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term74 x y z.
Proof. exact (proj1 (@lem1521401 x y z h1)). Qed.
Lemma lem1521405 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521406 : term195 = term196.
Proof. exact (@lem1521405 (NUMERAL 0) term45). Qed.
Lemma lem1521407 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1521408 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1521409 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1521408 h1) (fun h1 : term196 = True => @lem1521407)). Qed.
Lemma lem1521410 : term196 = True.
Proof. exact (EQ_MP (@lem1521409) (@lem1521407)). Qed.
Lemma lem1521411 : term195 = True.
Proof. exact (TRANS (@lem1521406) (@lem1521410)). Qed.
Lemma lem1521412 : True = term195.
Proof. exact (SYM (@lem1521411)). Qed.
Lemma lem1521413 : term195.
Proof. exact (EQ_MP (@lem1521412) (@lem0)). Qed.
Lemma lem1521414 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term235 x y z.
Proof. exact (conj (@lem1521413) (@lem1521403 x y z h1)). Qed.
Lemma lem1521416 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1521417 (x : real) (y : real) (z : real) : term236 x y z.
Proof. exact (@lem1521416 term48 (term69 x y z)). Qed.
Lemma lem1521418 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term237 x y z.
Proof. exact (@lem1521417 x y z (@lem1521414 x y z h1)). Qed.
Lemma lem1521419 (x : real) (y : real) (z : real) : (term238 x y z) = (term69 x y z).
Proof. exact (@lem1483460 (term69 x y z)). Qed.
Lemma lem1521420 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521421 (x : real) (y : real) (z : real) : (term239 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1521420) (@lem1521419 x y z)). Qed.
Lemma lem1521422 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521423 (x : real) (y : real) (z : real) : (term237 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1521421 x y z) (@lem1521422)). Qed.
Lemma lem1521424 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term74 x y z.
Proof. exact (EQ_MP (@lem1521423 x y z) (@lem1521418 x y z h1)). Qed.
Lemma lem1521426 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1521427 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1521426 (term54 x y z)). Qed.
Lemma lem1521428 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term206 x y z.
Proof. exact (@lem1521427 x y z (@lem1521402 x y z h1)). Qed.
Lemma lem1521429 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term240 x y z.
Proof. exact (@lem1521428 x y z h1 term48). Qed.
Lemma lem1521430 (x : real) (y : real) (z : real) : (term240 x y z) = ((term202 x y z) = term31).
Proof. exact (eq_refl (term240 x y z)). Qed.
Lemma lem1521431 (x : real) (y : real) (z : real) (h1 : term250 x y z) : (term202 x y z) = term31.
Proof. exact (EQ_MP (@lem1521430 x y z) (@lem1521429 x y z h1)). Qed.
Lemma lem1521432 (x : real) (y : real) (z : real) : (term202 x y z) = (term54 x y z).
Proof. exact (@lem1483460 (term54 x y z)). Qed.
Lemma lem1521433 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1521434 (x : real) (y : real) (z : real) : (term241 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1521433) (@lem1521432 x y z)). Qed.
Lemma lem1521435 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521436 (x : real) (y : real) (z : real) : ((term202 x y z) = term31) = ((term54 x y z) = term31).
Proof. exact (MK_COMB (@lem1521434 x y z) (@lem1521435)). Qed.
Lemma lem1521437 (x : real) (y : real) (z : real) (h1 : term250 x y z) : (term54 x y z) = term31.
Proof. exact (EQ_MP (@lem1521436 x y z) (@lem1521431 x y z h1)). Qed.
Lemma lem1521438 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term234 x y z.
Proof. exact (conj (@lem1521437 x y z h1) (@lem1521424 x y z h1)). Qed.
Lemma lem1521440 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1521441 (x : real) (y : real) (z : real) : term242 x y z.
Proof. exact (@lem1521440 (term54 x y z) (term69 x y z)). Qed.
Lemma lem1521442 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term243 x y z.
Proof. exact (@lem1521441 x y z (@lem1521438 x y z h1)). Qed.
Lemma lem1521443 (x : real) (y : real) (z : real) : (term244 x y z) = (term245 x y z).
Proof. exact (@lem1483480 x (term38 x) (term53 y z) (term32 y z)). Qed.
Lemma lem1521444 (x : real) : (term227 x) = (term217 x).
Proof. exact (@lem1483442 term37 x). Qed.
Lemma lem1521446 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521447 : term219 = term31.
Proof. exact (@lem1521446 term45). Qed.
Lemma lem1521448 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521449 : term220 = term221.
Proof. exact (MK_COMB (@lem1521448) (@lem1521447)). Qed.
Lemma lem1521450 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1521451 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1521449) (@lem1521450 x)). Qed.
Lemma lem1521452 (x : real) : (term227 x) = (term222 x).
Proof. exact (TRANS (@lem1521444 x) (@lem1521451 x)). Qed.
Lemma lem1521453 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1521454 (x : real) : (term227 x) = term31.
Proof. exact (TRANS (@lem1521452 x) (@lem1521453 x)). Qed.
Lemma lem1521455 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521456 (x : real) : (term228 x) = term224.
Proof. exact (MK_COMB (@lem1521455) (@lem1521454 x)). Qed.
Lemma lem1521457 (y : real) (z : real) : (term246 y z) = (term247 y z).
Proof. exact (@lem1483480 (term38 y) y z (term38 z)). Qed.
Lemma lem1521458 (y : real) : (term216 y) = (term217 y).
Proof. exact (@lem1483440 term37 y). Qed.
Lemma lem1521460 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521461 : term219 = term31.
Proof. exact (@lem1521460 term45). Qed.
Lemma lem1521462 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521463 : term220 = term221.
Proof. exact (MK_COMB (@lem1521462) (@lem1521461)). Qed.
Lemma lem1521464 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521465 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1521463) (@lem1521464 y)). Qed.
Lemma lem1521466 (y : real) : (term216 y) = (term222 y).
Proof. exact (TRANS (@lem1521458 y) (@lem1521465 y)). Qed.
Lemma lem1521467 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1521468 (y : real) : (term216 y) = term31.
Proof. exact (TRANS (@lem1521466 y) (@lem1521467 y)). Qed.
Lemma lem1521469 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521470 (y : real) : (term223 y) = term224.
Proof. exact (MK_COMB (@lem1521469) (@lem1521468 y)). Qed.
Lemma lem1521471 (z : real) : (term227 z) = (term217 z).
Proof. exact (@lem1483442 term37 z). Qed.
Lemma lem1521473 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1521474 : term219 = term31.
Proof. exact (@lem1521473 term45). Qed.
Lemma lem1521475 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521476 : term220 = term221.
Proof. exact (MK_COMB (@lem1521475) (@lem1521474)). Qed.
Lemma lem1521477 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521478 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1521476) (@lem1521477 z)). Qed.
Lemma lem1521479 (z : real) : (term227 z) = (term222 z).
Proof. exact (TRANS (@lem1521471 z) (@lem1521478 z)). Qed.
Lemma lem1521480 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1521481 (z : real) : (term227 z) = term31.
Proof. exact (TRANS (@lem1521479 z) (@lem1521480 z)). Qed.
Lemma lem1521482 (y : real) (z : real) : (term247 y z) = term229.
Proof. exact (MK_COMB (@lem1521470 y) (@lem1521481 z)). Qed.
Lemma lem1521483 (y : real) (z : real) : (term246 y z) = term229.
Proof. exact (TRANS (@lem1521457 y z) (@lem1521482 y z)). Qed.
Lemma lem1521484 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521485 (y : real) (z : real) : (term246 y z) = term31.
Proof. exact (TRANS (@lem1521483 y z) (@lem1521484)). Qed.
Lemma lem1521486 (x : real) (y : real) (z : real) : (term245 x y z) = term229.
Proof. exact (MK_COMB (@lem1521456 x) (@lem1521485 y z)). Qed.
Lemma lem1521487 (x : real) (y : real) (z : real) : (term244 x y z) = term229.
Proof. exact (TRANS (@lem1521443 x y z) (@lem1521486 x y z)). Qed.
Lemma lem1521488 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1521489 (x : real) (y : real) (z : real) : (term244 x y z) = term31.
Proof. exact (TRANS (@lem1521487 x y z) (@lem1521488)). Qed.
Lemma lem1521490 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521491 (x : real) (y : real) (z : real) : (term248 x y z) = term231.
Proof. exact (MK_COMB (@lem1521490) (@lem1521489 x y z)). Qed.
Lemma lem1521492 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521493 (x : real) (y : real) (z : real) : (term243 x y z) = term232.
Proof. exact (MK_COMB (@lem1521491 x y z) (@lem1521492)). Qed.
Lemma lem1521494 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term232.
Proof. exact (EQ_MP (@lem1521493 x y z) (@lem1521442 x y z h1)). Qed.
Lemma lem1521496 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1521497 : term232 = term233.
Proof. exact (@lem1521496 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1521498 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1521499 : term232 = False.
Proof. exact (TRANS (@lem1521497) (@lem1521498)). Qed.
Lemma lem1521500 (x : real) (y : real) (z : real) (h1 : term250 x y z) : False.
Proof. exact (EQ_MP (@lem1521499) (@lem1521494 x y z h1)). Qed.
Lemma lem1521501 (x : real) (y : real) (z : real) (h1 : term183 x y z) : False.
Proof. exact (or_elim (@lem1521273 x y z h1) (fun h0 : term249 x y z => @lem1521400 x y z h0) (fun h0 : term250 x y z => @lem1521500 x y z h0)). Qed.
Lemma lem1521502 (x : real) (y : real) (z : real) (h1 : term186 x y z) : False.
Proof. exact (or_elim (@lem1521043 x y z h1) (fun h0 : term184 x y z => @lem1521272 x y z h0) (fun h0 : term183 x y z => @lem1521501 x y z h0)). Qed.
Lemma lem1521504 (x : real) (y : real) (z : real) (h1 : term186 x y z) : term186 x y z.
Proof. exact (h1). Qed.
Lemma lem1521505 (x : real) (y : real) (z : real) (h1 : term186 x y z) : (term186 x y z) = False.
Proof. exact (prop_ext (fun h2 : term186 x y z => @lem1521502 x y z h1) (fun h2 : False => @lem1521504 x y z h1)). Qed.
Lemma lem1521506 (x : real) (y : real) (z : real) (h1 : term186 x y z) : False.
Proof. exact (EQ_MP (@lem1521505 x y z h1) (@lem1521504 x y z h1)). Qed.
Lemma lem1521507 (x : real) (y : real) (h1 : term188 x y) : term188 x y.
Proof. exact (h1). Qed.
Lemma lem1521508 (x : real) (y : real) (h1 : term188 x y) : False.
Proof. exact (ex_elim (@lem1521507 x y h1) (fun z : real => fun h0 : term187 x y z => @lem1521506 x y z h0)). Qed.
Lemma lem1521509 (x : real) (h1 : term190 x) : term190 x.
Proof. exact (h1). Qed.
Lemma lem1521510 (x : real) (h1 : term190 x) : False.
Proof. exact (ex_elim (@lem1521509 x h1) (fun y : real => fun h0 : term189 x y => @lem1521508 x y h0)). Qed.
Lemma lem1521511 (h1 : term192) : term192.
Proof. exact (h1). Qed.
Lemma lem1521512 (h1 : term192) : False.
Proof. exact (ex_elim (@lem1521511 h1) (fun x : real => fun h0 : term191 x => @lem1521510 x h0)). Qed.
Lemma lem1521513 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1521514 (h1 : term21) : term192.
Proof. exact (EQ_MP (@lem1521021) (@lem1521513 h1)). Qed.
Lemma lem1521515 (h1 : term21) : term192 = False.
Proof. exact (prop_ext (fun h2 : term192 => @lem1521512 h2) (fun h2 : False => @lem1521514 h1)). Qed.
Lemma lem1521516 (h1 : term21) : False.
Proof. exact (EQ_MP (@lem1521515 h1) (@lem1521514 h1)). Qed.
Lemma lem1521517 : term251.
Proof. exact (fun h0 : term21 => @lem1521516 h0). Qed.
Lemma lem1521518 : term252.
Proof. exact (@lem1386578 term253). Qed.
Lemma lem1521519 : term253.
Proof. exact (@lem1521518 (@lem1521517)). Qed.
