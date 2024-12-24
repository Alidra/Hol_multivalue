Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POLYFUN_EQ_0_term_abbrevs.
Require Import DE_MORGAN_THM_spec.
Require Import INFINITE_spec.
Require Import IN_NUMSEG_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_POLYFUN_ROOTBOUND_spec.
Require Import SUM_0_spec.
Require Import real_INFINITE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm7261461_spec.
Require Import thm7261462_spec.
Lemma lem7539139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7539140 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term1 s t).
Proof. exact (@lem7539139 real s t). Qed.
Lemma lem7539141 : (term2 = (@UNIV real)) = term3.
Proof. exact (@lem7539140 term2 (@UNIV real)). Qed.
Lemma lem7539154 : term3 = (term2 = (@UNIV real)).
Proof. exact (SYM (@lem7539141)). Qed.
Lemma lem7539162 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7539163 (p : real -> Prop) (x : real) : (term5 x p) = (p x).
Proof. exact (@lem7539162 real p x). Qed.
Lemma lem7539164 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem7539163 term8 x). Qed.
Lemma lem7539165 (x : real) : (term7 x) = True.
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7539166 (GEN_PVAR_349 : real) : (@SETSPEC real GEN_PVAR_349) = (@SETSPEC real GEN_PVAR_349).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_349)). Qed.
Lemma lem7539167 (x : real) (GEN_PVAR_349 : real) : (term9 GEN_PVAR_349 x) = (@SETSPEC real GEN_PVAR_349 True).
Proof. exact (MK_COMB (@lem7539166 GEN_PVAR_349) (@lem7539165 x)). Qed.
Lemma lem7539168 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7539169 (GEN_PVAR_349 : real) (x : real) : (term10 GEN_PVAR_349 x) = (@SETSPEC real GEN_PVAR_349 True x).
Proof. exact (MK_COMB (@lem7539167 x GEN_PVAR_349) (@lem7539168 x)). Qed.
Lemma lem7539170 (GEN_PVAR_349 : real) : (term11 GEN_PVAR_349) = (term12 GEN_PVAR_349).
Proof. exact (fun_ext (fun x : real => @lem7539169 GEN_PVAR_349 x)). Qed.
Lemma lem7539171 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7539172 (GEN_PVAR_349 : real) : (term13 GEN_PVAR_349) = (term14 GEN_PVAR_349).
Proof. exact (MK_COMB (@lem7539171) (@lem7539170 GEN_PVAR_349)). Qed.
Lemma lem7539173 : term15 = term16.
Proof. exact (fun_ext (fun GEN_PVAR_349 : real => @lem7539172 GEN_PVAR_349)). Qed.
Lemma lem7539174 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7539175 : term17 = term2.
Proof. exact (MK_COMB (@lem7539174) (@lem7539173)). Qed.
Lemma lem7539176 (x : real) : (@IN real x) = (@IN real x).
Proof. exact (eq_refl (@IN real x)). Qed.
Lemma lem7539177 (x : real) : (term6 x) = (term18 x).
Proof. exact (MK_COMB (@lem7539176 x) (@lem7539175)). Qed.
Lemma lem7539178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7539179 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem7539178) (@lem7539177 x)). Qed.
Lemma lem7539180 (x : real) : (term7 x) = True.
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7539181 (x : real) : ((term6 x) = (term7 x)) = ((term18 x) = True).
Proof. exact (MK_COMB (@lem7539179 x) (@lem7539180 x)). Qed.
Lemma lem7539182 (x : real) : (term18 x) = True.
Proof. exact (EQ_MP (@lem7539181 x) (@lem7539164 x)). Qed.
Lemma lem7539183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7539184 (x : real) : (term20 x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7539183) (@lem7539182 x)). Qed.
Lemma lem7539186 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem7539187 (x : real) : (@IN real x (@UNIV real)) = True.
Proof. exact (@lem7539186 real x). Qed.
Lemma lem7539188 (x : real) : ((term18 x) = (@IN real x (@UNIV real))) = (True = True).
Proof. exact (MK_COMB (@lem7539184 x) (@lem7539187 x)). Qed.
Lemma lem7539190 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7539191 : (True = True) = True.
Proof. exact (@lem7539190 True). Qed.
Lemma lem7539192 (x : real) : ((term18 x) = (@IN real x (@UNIV real))) = True.
Proof. exact (TRANS (@lem7539188 x) (@lem7539191)). Qed.
Lemma lem7539193 : term21 = term8.
Proof. exact (fun_ext (fun x : real => @lem7539192 x)). Qed.
Lemma lem7539194 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7539195 : term3 = term22.
Proof. exact (MK_COMB (@lem7539194) (@lem7539193)). Qed.
Lemma lem7539197 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7539198 (t : Prop) : (term24 t) = t.
Proof. exact (@lem7539197 real t). Qed.
Lemma lem7539199 : term22 = True.
Proof. exact (@lem7539198 True). Qed.
Lemma lem7539200 : term3 = True.
Proof. exact (TRANS (@lem7539195) (@lem7539199)). Qed.
Lemma lem7539201 : True = term3.
Proof. exact (SYM (@lem7539200)). Qed.
Lemma lem7539202 : term3.
Proof. exact (EQ_MP (@lem7539201) (@lem0)). Qed.
Lemma lem7539205 {A : Type'} (s : A -> Prop) (h1 : (@INFINITE A s) = (term25 A s)) : (@INFINITE A s) = (term25 A s).
Proof. exact (h1). Qed.
Lemma lem7539206 {A : Type'} (s : A -> Prop) (h1 : (@INFINITE A s) = (term25 A s)) : (term25 A s) = (@INFINITE A s).
Proof. exact (SYM (@lem7539205 A s h1)). Qed.
Lemma lem7539207 {A : Type'} (s : A -> Prop) (h1 : (term25 A s) = (@INFINITE A s)) : (term25 A s) = (@INFINITE A s).
Proof. exact (h1). Qed.
Lemma lem7539208 {A : Type'} (s : A -> Prop) (h1 : (term25 A s) = (@INFINITE A s)) : (@INFINITE A s) = (term25 A s).
Proof. exact (SYM (@lem7539207 A s h1)). Qed.
Lemma lem7539209 {A : Type'} (s : A -> Prop) : ((@INFINITE A s) = (term25 A s)) = ((term25 A s) = (@INFINITE A s)).
Proof. exact (prop_ext (fun h1 : (@INFINITE A s) = (term25 A s) => @lem7539206 A s h1) (fun h1 : (term25 A s) = (@INFINITE A s) => @lem7539208 A s h1)). Qed.
Lemma lem7539210 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7539209 A s)). Qed.
Lemma lem7539211 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7539212 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem7539211 A) (@lem7539210 A)). Qed.
Lemma lem7539213 {A : Type'} : term29 A.
Proof. exact (EQ_MP (@lem7539212 A) (@lem3198543 A)). Qed.
Lemma lem7539214 (n : nat) : term30 n.
Proof. exact (@lem7537923 n). Qed.
Lemma lem7539215 (n : nat) : (term30 n) = (term31 n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem7539216 (n : nat) : term31 n.
Proof. exact (EQ_MP (@lem7539215 n) (@lem7539214 n)). Qed.
Lemma lem7539217 (n : nat) (c : nat -> real) : term32 n c.
Proof. exact (@lem7539216 n c). Qed.
Lemma lem7539218 (c : nat -> real) (n : nat) : (term32 n c) = (term33 c n).
Proof. exact (eq_refl (term32 n c)). Qed.
Lemma lem7539223 (t : Prop) : (term34 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem7539224 (p : Prop) : (term34 p) = p.
Proof. exact (@lem7539223 p). Qed.
Lemma lem7539225 (p : Prop) : (@eq Prop p) = (@eq Prop p).
Proof. exact (eq_refl (@eq Prop p)). Qed.
Lemma lem7539226 (p : Prop) : (p = (term34 p)) = (p = p).
Proof. exact (MK_COMB (@lem7539225 p) (@lem7539224 p)). Qed.
Lemma lem7539228 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7539229 (x : Prop) : (x = x) = True.
Proof. exact (@lem7539228 Prop x). Qed.
Lemma lem7539230 (p : Prop) : (p = p) = True.
Proof. exact (@lem7539229 p). Qed.
Lemma lem7539231 (p : Prop) : (p = (term34 p)) = True.
Proof. exact (TRANS (@lem7539226 p) (@lem7539230 p)). Qed.
Lemma lem7539232 (p : Prop) : True = (p = (term34 p)).
Proof. exact (SYM (@lem7539231 p)). Qed.
Lemma lem7539234 (n : nat) (c : nat -> real) (h1 : term35 n c) : term35 n c.
Proof. exact (h1). Qed.
Lemma lem7539235 (n : nat) (c : nat -> real) (h1 : term36 n c) : term36 n c.
Proof. exact (h1). Qed.
Lemma lem7539237 (p : Prop) : p = (term34 p).
Proof. exact (EQ_MP (@lem7539232 p) (@lem0)). Qed.
Lemma lem7539238 (n : nat) (c : nat -> real) : (term36 n c) = (term37 n c).
Proof. exact (@lem7539237 (term36 n c)). Qed.
Lemma lem7539239 (n : nat) (c : nat -> real) : (term37 n c) = (term36 n c).
Proof. exact (SYM (@lem7539238 n c)). Qed.
Lemma lem7539240 (n : nat) (c : nat -> real) (h1 : term38 n c) : term38 n c.
Proof. exact (h1). Qed.
Lemma lem7539242 (c : nat -> real) (n : nat) : term33 c n.
Proof. exact (EQ_MP (@lem7539218 c n) (@lem7539217 n c)). Qed.
Lemma lem7539243 (n : nat) (c : nat -> real) (h1 : term38 n c) : term39 c n.
Proof. exact (@lem7539242 c n (@lem7539240 n c h1)). Qed.
Lemma lem7539244 (t1 : Prop) : term40 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem7539245 (t1 : Prop) : (term40 t1) = (term41 t1).
Proof. exact (eq_refl (term40 t1)). Qed.
Lemma lem7539246 (t1 : Prop) : term41 t1.
Proof. exact (EQ_MP (@lem7539245 t1) (@lem7539244 t1)). Qed.
Lemma lem7539247 (t1 : Prop) (t2 : Prop) : term42 t1 t2.
Proof. exact (@lem7539246 t1 t2). Qed.
Lemma lem7539248 (t1 : Prop) (t2 : Prop) : (term42 t1 t2) = (term43 t1 t2).
Proof. exact (eq_refl (term42 t1 t2)). Qed.
Lemma lem7539249 (t1 : Prop) (t2 : Prop) : term43 t1 t2.
Proof. exact (EQ_MP (@lem7539248 t1 t2) (@lem7539247 t1 t2)). Qed.
Lemma lem7539252 {A : Type'} (s : A -> Prop) : term44 A s.
Proof. exact (@lem7539213 A s). Qed.
Lemma lem7539253 {A : Type'} (s : A -> Prop) : (term44 A s) = ((term25 A s) = (@INFINITE A s)).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem7539255 : (@INFINITE real (@UNIV real)) = ((@INFINITE real (@UNIV real)) = True).
Proof. exact (@lem7 (@INFINITE real (@UNIV real))). Qed.
Lemma lem7539257 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : term45 n c x.
Proof. exact (@lem7539234 n c h1 x). Qed.
Lemma lem7539258 (n : nat) (c : nat -> real) (x : real) : (term45 n c x) = ((term46 n c x) = term47).
Proof. exact (eq_refl (term45 n c x)). Qed.
Lemma lem7539261 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem7539262 (c : nat -> real) (n : nat) : (term48 c n) = (term49 c n).
Proof. exact (@lem7539261 (term39 c n)). Qed.
Lemma lem7539264 (t1 : Prop) (t2 : Prop) : (term50 t1 t2) = (term51 t1 t2).
Proof. exact (proj1 (@lem7539249 t1 t2)). Qed.
Lemma lem7539265 (c : nat -> real) (n : nat) : (term49 c n) = (term52 c n).
Proof. exact (@lem7539264 (term53 n c) (term54 c n)). Qed.
Lemma lem7539268 (c : nat -> real) (n : nat) : (term48 c n) = (term52 c n).
Proof. exact (TRANS (@lem7539262 c n) (@lem7539265 c n)). Qed.
Lemma lem7539270 {A : Type'} (s : A -> Prop) : (term25 A s) = (@INFINITE A s).
Proof. exact (EQ_MP (@lem7539253 A s) (@lem7539252 A s)). Qed.
Lemma lem7539271 (s : real -> Prop) : (term55 s) = (@INFINITE real s).
Proof. exact (@lem7539270 real s). Qed.
Lemma lem7539272 (n : nat) (c : nat -> real) : (term56 n c) = (term57 n c).
Proof. exact (@lem7539271 (term58 n c)). Qed.
Lemma lem7539280 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term46 n c x) = term47.
Proof. exact (EQ_MP (@lem7539258 n c x) (@lem7539257 x n c h1)). Qed.
Lemma lem7539281 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7539282 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term59 n c x) = term60.
Proof. exact (MK_COMB (@lem7539281) (@lem7539280 x n c h1)). Qed.
Lemma lem7539283 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem7539284 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : ((term46 n c x) = term47) = (term47 = term47).
Proof. exact (MK_COMB (@lem7539282 x n c h1) (@lem7539283)). Qed.
Lemma lem7539286 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7539287 (x : real) : (x = x) = True.
Proof. exact (@lem7539286 real x). Qed.
Lemma lem7539288 : (term47 = term47) = True.
Proof. exact (@lem7539287 term47). Qed.
Lemma lem7539289 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : ((term46 n c x) = term47) = True.
Proof. exact (TRANS (@lem7539284 x n c h1) (@lem7539288)). Qed.
Lemma lem7539290 (GEN_PVAR_345 : real) : (@SETSPEC real GEN_PVAR_345) = (@SETSPEC real GEN_PVAR_345).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_345)). Qed.
Lemma lem7539291 (x : real) (GEN_PVAR_345 : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term61 GEN_PVAR_345 n c x) = (@SETSPEC real GEN_PVAR_345 True).
Proof. exact (MK_COMB (@lem7539290 GEN_PVAR_345) (@lem7539289 x n c h1)). Qed.
Lemma lem7539292 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7539293 (GEN_PVAR_345 : real) (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term62 GEN_PVAR_345 n c x) = (@SETSPEC real GEN_PVAR_345 True x).
Proof. exact (MK_COMB (@lem7539291 x GEN_PVAR_345 n c h1) (@lem7539292 x)). Qed.
Lemma lem7539294 (GEN_PVAR_345 : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term63 GEN_PVAR_345 n c) = (term12 GEN_PVAR_345).
Proof. exact (fun_ext (fun x : real => @lem7539293 GEN_PVAR_345 x n c h1)). Qed.
Lemma lem7539295 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7539296 (GEN_PVAR_345 : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term64 GEN_PVAR_345 n c) = (term14 GEN_PVAR_345).
Proof. exact (MK_COMB (@lem7539295) (@lem7539294 GEN_PVAR_345 n c h1)). Qed.
Lemma lem7539301 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term65 n c) = term16.
Proof. exact (fun_ext (fun GEN_PVAR_345 : real => @lem7539296 GEN_PVAR_345 n c h1)). Qed.
Lemma lem7539302 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7539303 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term58 n c) = term2.
Proof. exact (MK_COMB (@lem7539302) (@lem7539301 n c h1)). Qed.
Lemma lem7539305 : term2 = (@UNIV real).
Proof. exact (EQ_MP (@lem7539154) (@lem7539202)). Qed.
Lemma lem7539306 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term58 n c) = (@UNIV real).
Proof. exact (TRANS (@lem7539303 n c h1) (@lem7539305)). Qed.
Lemma lem7539307 : (@INFINITE real) = (@INFINITE real).
Proof. exact (eq_refl (@INFINITE real)). Qed.
Lemma lem7539308 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term57 n c) = (@INFINITE real (@UNIV real)).
Proof. exact (MK_COMB (@lem7539307) (@lem7539306 n c h1)). Qed.
Lemma lem7539310 : (@INFINITE real (@UNIV real)) = True.
Proof. exact (EQ_MP (@lem7539255) (@lem4713723)). Qed.
Lemma lem7539311 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term57 n c) = True.
Proof. exact (TRANS (@lem7539308 n c h1) (@lem7539310)). Qed.
Lemma lem7539312 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term56 n c) = True.
Proof. exact (TRANS (@lem7539272 n c) (@lem7539311 n c h1)). Qed.
Lemma lem7539313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7539314 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term66 n c) = (or True).
Proof. exact (MK_COMB (@lem7539313) (@lem7539312 n c h1)). Qed.
Lemma lem7539322 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term46 n c x) = term47.
Proof. exact (EQ_MP (@lem7539258 n c x) (@lem7539257 x n c h1)). Qed.
Lemma lem7539323 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7539324 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term59 n c x) = term60.
Proof. exact (MK_COMB (@lem7539323) (@lem7539322 x n c h1)). Qed.
Lemma lem7539325 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem7539326 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : ((term46 n c x) = term47) = (term47 = term47).
Proof. exact (MK_COMB (@lem7539324 x n c h1) (@lem7539325)). Qed.
Lemma lem7539328 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7539329 (x : real) : (x = x) = True.
Proof. exact (@lem7539328 real x). Qed.
Lemma lem7539330 : (term47 = term47) = True.
Proof. exact (@lem7539329 term47). Qed.
Lemma lem7539331 (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : ((term46 n c x) = term47) = True.
Proof. exact (TRANS (@lem7539326 x n c h1) (@lem7539330)). Qed.
Lemma lem7539332 (GEN_PVAR_346 : real) : (@SETSPEC real GEN_PVAR_346) = (@SETSPEC real GEN_PVAR_346).
Proof. exact (eq_refl (@SETSPEC real GEN_PVAR_346)). Qed.
Lemma lem7539333 (x : real) (GEN_PVAR_346 : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term61 GEN_PVAR_346 n c x) = (@SETSPEC real GEN_PVAR_346 True).
Proof. exact (MK_COMB (@lem7539332 GEN_PVAR_346) (@lem7539331 x n c h1)). Qed.
Lemma lem7539334 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7539335 (GEN_PVAR_346 : real) (x : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term62 GEN_PVAR_346 n c x) = (@SETSPEC real GEN_PVAR_346 True x).
Proof. exact (MK_COMB (@lem7539333 x GEN_PVAR_346 n c h1) (@lem7539334 x)). Qed.
Lemma lem7539336 (GEN_PVAR_346 : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term63 GEN_PVAR_346 n c) = (term12 GEN_PVAR_346).
Proof. exact (fun_ext (fun x : real => @lem7539335 GEN_PVAR_346 x n c h1)). Qed.
Lemma lem7539337 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7539338 (GEN_PVAR_346 : real) (n : nat) (c : nat -> real) (h1 : term35 n c) : (term64 GEN_PVAR_346 n c) = (term14 GEN_PVAR_346).
Proof. exact (MK_COMB (@lem7539337) (@lem7539336 GEN_PVAR_346 n c h1)). Qed.
Lemma lem7539343 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term65 n c) = term16.
Proof. exact (fun_ext (fun GEN_PVAR_346 : real => @lem7539338 GEN_PVAR_346 n c h1)). Qed.
Lemma lem7539344 : (@GSPEC real) = (@GSPEC real).
Proof. exact (eq_refl (@GSPEC real)). Qed.
Lemma lem7539345 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term58 n c) = term2.
Proof. exact (MK_COMB (@lem7539344) (@lem7539343 n c h1)). Qed.
Lemma lem7539347 : term2 = (@UNIV real).
Proof. exact (EQ_MP (@lem7539154) (@lem7539202)). Qed.
Lemma lem7539348 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term58 n c) = (@UNIV real).
Proof. exact (TRANS (@lem7539345 n c h1) (@lem7539347)). Qed.
Lemma lem7539349 : (@CARD real) = (@CARD real).
Proof. exact (eq_refl (@CARD real)). Qed.
Lemma lem7539350 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term67 n c) = (@CARD real (@UNIV real)).
Proof. exact (MK_COMB (@lem7539349) (@lem7539348 n c h1)). Qed.
Lemma lem7539351 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7539352 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term68 n c) = term69.
Proof. exact (MK_COMB (@lem7539351) (@lem7539350 n c h1)). Qed.
Lemma lem7539353 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7539354 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term54 c n) = (term70 n).
Proof. exact (MK_COMB (@lem7539352 n c h1) (@lem7539353 n)). Qed.
Lemma lem7539355 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7539356 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term71 c n) = (term72 n).
Proof. exact (MK_COMB (@lem7539355) (@lem7539354 n c h1)). Qed.
Lemma lem7539357 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term52 c n) = (term73 n).
Proof. exact (MK_COMB (@lem7539314 n c h1) (@lem7539356 n c h1)). Qed.
Lemma lem7539359 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7539360 (n : nat) : (term73 n) = True.
Proof. exact (@lem7539359 (term72 n)). Qed.
Lemma lem7539361 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term52 c n) = True.
Proof. exact (TRANS (@lem7539357 n c h1) (@lem7539360 n)). Qed.
Lemma lem7539362 (n : nat) (c : nat -> real) (h1 : term35 n c) : (term48 c n) = True.
Proof. exact (TRANS (@lem7539268 c n) (@lem7539361 n c h1)). Qed.
Lemma lem7539363 (n : nat) (c : nat -> real) (h1 : term35 n c) : True = (term48 c n).
Proof. exact (SYM (@lem7539362 n c h1)). Qed.
Lemma lem7539364 (n : nat) (c : nat -> real) (h1 : term35 n c) : term48 c n.
Proof. exact (EQ_MP (@lem7539363 n c h1) (@lem0)). Qed.
Lemma lem7539365 (n : nat) (c : nat -> real) (h1 : term35 n c) (h2 : term38 n c) : False.
Proof. exact (@lem7539364 n c h1 (@lem7539243 n c h2)). Qed.
Lemma lem7539366 (n : nat) (c : nat -> real) (h1 : term35 n c) : term74 n c.
Proof. exact (fun h0 : term38 n c => @lem7539365 n c h1 h0). Qed.
Lemma lem7539367 (n : nat) (c : nat -> real) : (term74 n c) = (term37 n c).
Proof. exact (@lem69 (term38 n c)). Qed.
Lemma lem7539368 (n : nat) (c : nat -> real) (h1 : term35 n c) : term37 n c.
Proof. exact (EQ_MP (@lem7539367 n c) (@lem7539366 n c h1)). Qed.
Lemma lem7539369 (n : nat) (c : nat -> real) (h1 : term35 n c) : term36 n c.
Proof. exact (EQ_MP (@lem7539239 n c) (@lem7539368 n c h1)). Qed.
Lemma lem7539370 {A : Type'} (s : A -> Prop) : term75 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7539371 {A : Type'} (s : A -> Prop) : (term75 A s) = ((term76 A s) = term47).
Proof. exact (eq_refl (term75 A s)). Qed.
Lemma lem7539373 (x : real) : term77 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem7539374 (x : real) : (term77 x) = ((term78 x) = term47).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem7539381 (m : nat) : term79 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7539382 (m : nat) : (term79 m) = (term80 m).
Proof. exact (eq_refl (term79 m)). Qed.
Lemma lem7539383 (m : nat) : term80 m.
Proof. exact (EQ_MP (@lem7539382 m) (@lem7539381 m)). Qed.
Lemma lem7539384 (m : nat) (n : nat) : term81 m n.
Proof. exact (@lem7539383 m n). Qed.
Lemma lem7539385 (m : nat) (n : nat) : (term81 m n) = (term82 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem7539386 (m : nat) (n : nat) : term82 m n.
Proof. exact (EQ_MP (@lem7539385 m n) (@lem7539384 m n)). Qed.
Lemma lem7539387 (m : nat) (n : nat) (p : nat) : term83 m n p.
Proof. exact (@lem7539386 m n p). Qed.
Lemma lem7539388 (m : nat) (p : nat) (n : nat) : (term83 m n p) = ((term84 p m n) = (term85 m p n)).
Proof. exact (eq_refl (term83 m n p)). Qed.
Lemma lem7539390 (i : nat) (n : nat) (c : nat -> real) (h1 : term36 n c) : term86 n c i.
Proof. exact (@lem7539235 n c h1 i). Qed.
Lemma lem7539391 (n : nat) (c : nat -> real) (i : nat) : (term86 n c i) = (term87 n c i).
Proof. exact (eq_refl (term86 n c i)). Qed.
Lemma lem7539392 (i : nat) (n : nat) (c : nat -> real) (h1 : term36 n c) : term87 n c i.
Proof. exact (EQ_MP (@lem7539391 n c i) (@lem7539390 i n c h1)). Qed.
Lemma lem7539393 (i : nat) (n : nat) (h1 : term88 i n) : term88 i n.
Proof. exact (h1). Qed.
Lemma lem7539394 (c : nat -> real) (i : nat) (n : nat) (h1 : term36 n c) (h2 : term88 i n) : (c i) = term47.
Proof. exact (@lem7539392 i n c h1 (@lem7539393 i n h2)). Qed.
Lemma lem7539407 (f : nat -> real) (a : nat) (b : nat) (g : nat -> real) : term89 f a b g.
Proof. exact (EQ_MP (@lem7261462 f a b g) (@lem7261461 f a g b)). Qed.
Lemma lem7539408 (f : nat -> real) (a : nat) (b : nat) : term90 f a b.
Proof. exact (fun g : nat -> real => @lem7539407 f a b g). Qed.
Lemma lem7539409 (c : nat -> real) (x : real) (n : nat) : term91 c x n.
Proof. exact (@lem7539408 (term92 c x) (NUMERAL 0) n). Qed.
Lemma lem7539410 (c : nat -> real) (x : real) (i : nat) : (term93 c x i) = (term94 c x i).
Proof. exact (eq_refl (term93 c x i)). Qed.
Lemma lem7539411 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7539412 (c : nat -> real) (x : real) (i : nat) : (term95 c x i) = (term96 c x i).
Proof. exact (MK_COMB (@lem7539411) (@lem7539410 c x i)). Qed.
Lemma lem7539413 (g : nat -> real) (i : nat) : (g i) = (g i).
Proof. exact (eq_refl (g i)). Qed.
Lemma lem7539414 (c : nat -> real) (x : real) (g : nat -> real) (i : nat) : ((term93 c x i) = (g i)) = ((term94 c x i) = (g i)).
Proof. exact (MK_COMB (@lem7539412 c x i) (@lem7539413 g i)). Qed.
Lemma lem7539415 (i : nat) (n : nat) : (term97 i n) = (term97 i n).
Proof. exact (eq_refl (term97 i n)). Qed.
Lemma lem7539416 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) (i : nat) : (term98 n c x g i) = (term99 n c x g i).
Proof. exact (MK_COMB (@lem7539415 i n) (@lem7539414 c x g i)). Qed.
Lemma lem7539417 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term100 n c x g) = (term101 n c x g).
Proof. exact (fun_ext (fun i : nat => @lem7539416 n c x g i)). Qed.
Lemma lem7539418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539419 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term102 n c x g) = (term103 n c x g).
Proof. exact (MK_COMB (@lem7539418) (@lem7539417 n c x g)). Qed.
Lemma lem7539420 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7539421 (n : nat) (c : nat -> real) (x : real) (g : nat -> real) : (term104 n c x g) = (term105 n c x g).
Proof. exact (MK_COMB (@lem7539420) (@lem7539419 n c x g)). Qed.
Lemma lem7539422 (c : nat -> real) (x : real) (i : nat) : (term93 c x i) = (term94 c x i).
Proof. exact (eq_refl (term93 c x i)). Qed.
Lemma lem7539423 (c : nat -> real) (x : real) : (term106 c x) = (term92 c x).
Proof. exact (fun_ext (fun i : nat => @lem7539422 c x i)). Qed.
Lemma lem7539424 (n : nat) : (term107 n) = (term107 n).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem7539425 (n : nat) (c : nat -> real) (x : real) : (term108 n c x) = (term46 n c x).
Proof. exact (MK_COMB (@lem7539424 n) (@lem7539423 c x)). Qed.
Lemma lem7539426 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7539427 (n : nat) (c : nat -> real) (x : real) : (term109 n c x) = (term59 n c x).
Proof. exact (MK_COMB (@lem7539426) (@lem7539425 n c x)). Qed.
Lemma lem7539428 (n : nat) (g : nat -> real) : (term110 n g) = (term110 n g).
Proof. exact (eq_refl (term110 n g)). Qed.
Lemma lem7539429 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : ((term108 n c x) = (term110 n g)) = ((term46 n c x) = (term110 n g)).
Proof. exact (MK_COMB (@lem7539427 n c x) (@lem7539428 n g)). Qed.
Lemma lem7539430 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : (term111 c x n g) = (term112 c x n g).
Proof. exact (MK_COMB (@lem7539421 n c x g) (@lem7539429 c x n g)). Qed.
Lemma lem7539431 (c : nat -> real) (x : real) (n : nat) : (term113 c x n) = (term114 c x n).
Proof. exact (fun_ext (fun g : nat -> real => @lem7539430 c x n g)). Qed.
Lemma lem7539432 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7539433 (c : nat -> real) (x : real) (n : nat) : (term91 c x n) = (term115 c x n).
Proof. exact (MK_COMB (@lem7539432) (@lem7539431 c x n)). Qed.
Lemma lem7539434 (c : nat -> real) (x : real) (n : nat) : term115 c x n.
Proof. exact (EQ_MP (@lem7539433 c x n) (@lem7539409 c x n)). Qed.
Lemma lem7539435 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : term116 c x n g.
Proof. exact (@lem7539434 c x n g). Qed.
Lemma lem7539436 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : (term116 c x n g) = (term112 c x n g).
Proof. exact (eq_refl (term116 c x n g)). Qed.
Lemma lem7539438 (i : nat) (n : nat) (h1 : term117 i n) : term117 i n.
Proof. exact (h1). Qed.
Lemma lem7539439 (i : nat) (n : nat) (h1 : term117 i n) : Peano.le i n.
Proof. exact (proj2 (@lem7539438 i n h1)). Qed.
Lemma lem7539440 (i : nat) (n : nat) : (Peano.le i n) = ((Peano.le i n) = True).
Proof. exact (@lem7 (Peano.le i n)). Qed.
Lemma lem7539442 (i : nat) (n : nat) (h1 : term117 i n) : term118 i.
Proof. exact (proj1 (@lem7539438 i n h1)). Qed.
Lemma lem7539443 (i : nat) : (term118 i) = ((term118 i) = True).
Proof. exact (@lem7 (term118 i)). Qed.
Lemma lem7539446 (i : nat) (n : nat) (c : nat -> real) (h1 : term36 n c) : term87 n c i.
Proof. exact (fun h0 : term88 i n => @lem7539394 c i n h1 h0). Qed.
Lemma lem7539448 (m : nat) (p : nat) (n : nat) : (term84 p m n) = (term85 m p n).
Proof. exact (EQ_MP (@lem7539388 m p n) (@lem7539387 m n p)). Qed.
Lemma lem7539449 (i : nat) (n : nat) : (term88 i n) = (term117 i n).
Proof. exact (@lem7539448 (NUMERAL 0) i n). Qed.
Lemma lem7539453 (i : nat) (n : nat) (h1 : term117 i n) : (term118 i) = True.
Proof. exact (EQ_MP (@lem7539443 i) (@lem7539442 i n h1)). Qed.
Lemma lem7539454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7539455 (i : nat) (n : nat) (h1 : term117 i n) : (term119 i) = (and True).
Proof. exact (MK_COMB (@lem7539454) (@lem7539453 i n h1)). Qed.
Lemma lem7539457 (i : nat) (n : nat) (h1 : term117 i n) : (Peano.le i n) = True.
Proof. exact (EQ_MP (@lem7539440 i n) (@lem7539439 i n h1)). Qed.
Lemma lem7539458 (i : nat) (n : nat) (h1 : term117 i n) : (term117 i n) = (True /\ True).
Proof. exact (MK_COMB (@lem7539455 i n h1) (@lem7539457 i n h1)). Qed.
Lemma lem7539460 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7539461 : (True /\ True) = True.
Proof. exact (@lem7539460 True). Qed.
Lemma lem7539462 (i : nat) (n : nat) (h1 : term117 i n) : (term117 i n) = True.
Proof. exact (TRANS (@lem7539458 i n h1) (@lem7539461)). Qed.
Lemma lem7539463 (i : nat) (n : nat) (h1 : term117 i n) : (term88 i n) = True.
Proof. exact (TRANS (@lem7539449 i n) (@lem7539462 i n h1)). Qed.
Lemma lem7539464 (i : nat) (n : nat) (h1 : term117 i n) : True = (term88 i n).
Proof. exact (SYM (@lem7539463 i n h1)). Qed.
Lemma lem7539465 (i : nat) (n : nat) (h1 : term117 i n) : term88 i n.
Proof. exact (EQ_MP (@lem7539464 i n h1) (@lem0)). Qed.
Lemma lem7539466 (c : nat -> real) (i : nat) (n : nat) (h1 : term36 n c) (h2 : term117 i n) : (c i) = term47.
Proof. exact (@lem7539446 i n c h1 (@lem7539465 i n h2)). Qed.
Lemma lem7539467 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7539468 (c : nat -> real) (i : nat) (n : nat) (h1 : term36 n c) (h2 : term117 i n) : (term120 c i) = term121.
Proof. exact (MK_COMB (@lem7539467) (@lem7539466 c i n h1 h2)). Qed.
Lemma lem7539469 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7539470 (x : real) (c : nat -> real) (i : nat) (n : nat) (h1 : term36 n c) (h2 : term117 i n) : (term94 c x i) = (term122 x i).
Proof. exact (MK_COMB (@lem7539468 c i n h1 h2) (@lem7539469 x i)). Qed.
Lemma lem7539472 (x : real) : (term78 x) = term47.
Proof. exact (EQ_MP (@lem7539374 x) (@lem7539373 x)). Qed.
Lemma lem7539473 (x : real) (i : nat) : (term122 x i) = term47.
Proof. exact (@lem7539472 (real_pow x i)). Qed.
Lemma lem7539474 (x : real) (c : nat -> real) (i : nat) (n : nat) (h1 : term36 n c) (h2 : term117 i n) : (term94 c x i) = term47.
Proof. exact (TRANS (@lem7539470 x c i n h1 h2) (@lem7539473 x i)). Qed.
Lemma lem7539475 (x : real) (i : nat) (n : nat) (c : nat -> real) (h1 : term36 n c) : term123 n c x i.
Proof. exact (fun h0 : term117 i n => @lem7539474 x c i n h1 h0). Qed.
Lemma lem7539476 (x : real) (n : nat) (c : nat -> real) (h1 : term36 n c) : term124 n c x.
Proof. exact (fun i : nat => @lem7539475 x i n c h1). Qed.
Lemma lem7539478 (c : nat -> real) (x : real) (n : nat) (g : nat -> real) : term112 c x n g.
Proof. exact (EQ_MP (@lem7539436 c x n g) (@lem7539435 c x n g)). Qed.
Lemma lem7539479 (c : nat -> real) (x : real) (n : nat) : term125 c x n.
Proof. exact (@lem7539478 c x n term126). Qed.
Lemma lem7539480 (i : nat) : (term127 i) = term47.
Proof. exact (eq_refl (term127 i)). Qed.
Lemma lem7539481 (c : nat -> real) (x : real) (i : nat) : (term96 c x i) = (term96 c x i).
Proof. exact (eq_refl (term96 c x i)). Qed.
Lemma lem7539482 (c : nat -> real) (x : real) (i : nat) : ((term94 c x i) = (term127 i)) = ((term94 c x i) = term47).
Proof. exact (MK_COMB (@lem7539481 c x i) (@lem7539480 i)). Qed.
Lemma lem7539483 (i : nat) (n : nat) : (term97 i n) = (term97 i n).
Proof. exact (eq_refl (term97 i n)). Qed.
Lemma lem7539484 (n : nat) (c : nat -> real) (x : real) (i : nat) : (term128 n c x i) = (term123 n c x i).
Proof. exact (MK_COMB (@lem7539483 i n) (@lem7539482 c x i)). Qed.
Lemma lem7539485 (n : nat) (c : nat -> real) (x : real) : (term129 n c x) = (term130 n c x).
Proof. exact (fun_ext (fun i : nat => @lem7539484 n c x i)). Qed.
Lemma lem7539486 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7539487 (n : nat) (c : nat -> real) (x : real) : (term131 n c x) = (term124 n c x).
Proof. exact (MK_COMB (@lem7539486) (@lem7539485 n c x)). Qed.
Lemma lem7539488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7539489 (n : nat) (c : nat -> real) (x : real) : (term132 n c x) = (term133 n c x).
Proof. exact (MK_COMB (@lem7539488) (@lem7539487 n c x)). Qed.
Lemma lem7539490 (c : nat -> real) (x : real) (n : nat) : ((term46 n c x) = (term134 n)) = ((term46 n c x) = (term134 n)).
Proof. exact (eq_refl ((term46 n c x) = (term134 n))). Qed.
Lemma lem7539491 (c : nat -> real) (x : real) (n : nat) : (term125 c x n) = (term135 c x n).
Proof. exact (MK_COMB (@lem7539489 n c x) (@lem7539490 c x n)). Qed.
Lemma lem7539492 (c : nat -> real) (x : real) (n : nat) : term135 c x n.
Proof. exact (EQ_MP (@lem7539491 c x n) (@lem7539479 c x n)). Qed.
Lemma lem7539493 (x : real) (n : nat) (c : nat -> real) (h1 : term36 n c) : (term46 n c x) = (term134 n).
Proof. exact (@lem7539492 c x n (@lem7539476 x n c h1)). Qed.
Lemma lem7539495 {A : Type'} (s : A -> Prop) : (term76 A s) = term47.
Proof. exact (EQ_MP (@lem7539371 A s) (@lem7539370 A s)). Qed.
Lemma lem7539496 (s : nat -> Prop) : (term136 s) = term47.
Proof. exact (@lem7539495 nat s). Qed.
Lemma lem7539497 (n : nat) : (term134 n) = term47.
Proof. exact (@lem7539496 (term137 n)). Qed.
Lemma lem7539498 (x : real) (n : nat) (c : nat -> real) (h1 : term36 n c) : (term46 n c x) = term47.
Proof. exact (TRANS (@lem7539493 x n c h1) (@lem7539497 n)). Qed.
Lemma lem7539499 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7539500 (x : real) (n : nat) (c : nat -> real) (h1 : term36 n c) : (term59 n c x) = term60.
Proof. exact (MK_COMB (@lem7539499) (@lem7539498 x n c h1)). Qed.
Lemma lem7539501 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem7539502 (x : real) (n : nat) (c : nat -> real) (h1 : term36 n c) : ((term46 n c x) = term47) = (term47 = term47).
Proof. exact (MK_COMB (@lem7539500 x n c h1) (@lem7539501)). Qed.
Lemma lem7539504 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7539505 (x : real) : (x = x) = True.
Proof. exact (@lem7539504 real x). Qed.
Lemma lem7539506 : (term47 = term47) = True.
Proof. exact (@lem7539505 term47). Qed.
Lemma lem7539507 (x : real) (n : nat) (c : nat -> real) (h1 : term36 n c) : ((term46 n c x) = term47) = True.
Proof. exact (TRANS (@lem7539502 x n c h1) (@lem7539506)). Qed.
Lemma lem7539508 (n : nat) (c : nat -> real) (h1 : term36 n c) : (term138 n c) = term8.
Proof. exact (fun_ext (fun x : real => @lem7539507 x n c h1)). Qed.
Lemma lem7539509 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7539510 (n : nat) (c : nat -> real) (h1 : term36 n c) : (term35 n c) = term22.
Proof. exact (MK_COMB (@lem7539509) (@lem7539508 n c h1)). Qed.
Lemma lem7539512 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7539513 (t : Prop) : (term24 t) = t.
Proof. exact (@lem7539512 real t). Qed.
Lemma lem7539514 : term22 = True.
Proof. exact (@lem7539513 True). Qed.
Lemma lem7539515 (n : nat) (c : nat -> real) (h1 : term36 n c) : (term35 n c) = True.
Proof. exact (TRANS (@lem7539510 n c h1) (@lem7539514)). Qed.
Lemma lem7539516 (n : nat) (c : nat -> real) (h1 : term36 n c) : True = (term35 n c).
Proof. exact (SYM (@lem7539515 n c h1)). Qed.
Lemma lem7539517 (n : nat) (c : nat -> real) (h1 : term36 n c) : term35 n c.
Proof. exact (EQ_MP (@lem7539516 n c h1) (@lem0)). Qed.
Lemma lem7539518 (n : nat) (c : nat -> real) : term139 n c.
Proof. exact (fun h0 : term36 n c => @lem7539517 n c h0). Qed.
Lemma lem7539519 (n : nat) (c : nat -> real) : term140 n c.
Proof. exact (fun h0 : term35 n c => @lem7539369 n c h0). Qed.
Lemma lem7539520 (n : nat) (c : nat -> real) : term141 n c.
Proof. exact (conj (@lem7539519 n c) (@lem7539518 n c)). Qed.
Lemma lem7539521 (n : nat) (c : nat -> real) : (term141 n c) = ((term35 n c) = (term36 n c)).
Proof. exact (@lem32 (term35 n c) (term36 n c)). Qed.
Lemma lem7539522 (n : nat) (c : nat -> real) : (term35 n c) = (term36 n c).
Proof. exact (EQ_MP (@lem7539521 n c) (@lem7539520 n c)). Qed.
Lemma lem7539527 (n : nat) : term142 n.
Proof. exact (fun c : nat -> real => @lem7539522 n c). Qed.
Lemma lem7539532 : term143.
Proof. exact (fun n : nat => @lem7539527 n). Qed.
