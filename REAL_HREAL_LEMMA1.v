Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_HREAL_LEMMA1_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import HREAL_ADD_RID_spec.
Require Import HREAL_EQ_ADD_LCANCEL_spec.
Require Import PAIR_spec.
Require Import thm0_spec.
Require Import thm1319607_spec.
Require Import thm1319802_spec.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import thm1320277_spec.
Require Import thm1337493_spec.
Require Import thm1337537_spec.
Require Import thm1337991_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import treal_eq_spec.
Require Import treal_le_spec.
Require Import treal_of_num_spec.
Lemma lem1346201 (x : hreal) : term0 x.
Proof. exact (@lem1319607 x). Qed.
Lemma lem1346202 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1346203 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1346202 x) (@lem1346201 x)). Qed.
Lemma lem1346204 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1346203 x y). Qed.
Lemma lem1346205 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1346206 (x : hreal) (y : hreal) : term3 x y.
Proof. exact (EQ_MP (@lem1346205 x y) (@lem1346204 x y)). Qed.
Lemma lem1346207 (x : hreal) (y : hreal) : (term3 x y) = ((term3 x y) = True).
Proof. exact (@lem7 (term3 x y)). Qed.
Lemma lem1346210 (x : hreal) (h1 : (term4 x) = x) : (term4 x) = x.
Proof. exact (h1). Qed.
Lemma lem1346211 (x : hreal) (h1 : (term4 x) = x) : x = (term4 x).
Proof. exact (SYM (@lem1346210 x h1)). Qed.
Lemma lem1346212 (x : hreal) (h1 : x = (term4 x)) : x = (term4 x).
Proof. exact (h1). Qed.
Lemma lem1346213 (x : hreal) (h1 : x = (term4 x)) : (term4 x) = x.
Proof. exact (SYM (@lem1346212 x h1)). Qed.
Lemma lem1346214 (x : hreal) : ((term4 x) = x) = (x = (term4 x)).
Proof. exact (prop_ext (fun h1 : (term4 x) = x => @lem1346211 x h1) (fun h1 : x = (term4 x) => @lem1346213 x h1)). Qed.
Lemma lem1346215 : term5 = term6.
Proof. exact (fun_ext (fun x : hreal => @lem1346214 x)). Qed.
Lemma lem1346216 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346217 : term7 = term8.
Proof. exact (MK_COMB (@lem1346216) (@lem1346215)). Qed.
Lemma lem1346218 : term8.
Proof. exact (EQ_MP (@lem1346217) (@lem1320277)). Qed.
Lemma lem1346219 (x : hreal) : term9 x.
Proof. exact (@lem1346218 x). Qed.
Lemma lem1346220 (x : hreal) : (term9 x) = (x = (term4 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1346222 (n : hreal) : term10 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1346223 (n : hreal) : (term10 n) = ((term11 n) = n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1346225 (x : hreal) : term12 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1346226 (x : hreal) : (term12 x) = ((term4 x) = x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1346228 (x1 : hreal) : term13 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1346229 (x1 : hreal) : (term13 x1) = (term14 x1).
Proof. exact (eq_refl (term13 x1)). Qed.
Lemma lem1346230 (x1 : hreal) : term14 x1.
Proof. exact (EQ_MP (@lem1346229 x1) (@lem1346228 x1)). Qed.
Lemma lem1346231 (x1 : hreal) (y2 : hreal) : term15 x1 y2.
Proof. exact (@lem1346230 x1 y2). Qed.
Lemma lem1346232 (x1 : hreal) (y2 : hreal) : (term15 x1 y2) = (term16 x1 y2).
Proof. exact (eq_refl (term15 x1 y2)). Qed.
Lemma lem1346233 (x1 : hreal) (y2 : hreal) : term16 x1 y2.
Proof. exact (EQ_MP (@lem1346232 x1 y2) (@lem1346231 x1 y2)). Qed.
Lemma lem1346234 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term17 x1 y2 x2.
Proof. exact (@lem1346233 x1 y2 x2). Qed.
Lemma lem1346235 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term17 x1 y2 x2) = (term18 x1 y2 x2).
Proof. exact (eq_refl (term17 x1 y2 x2)). Qed.
Lemma lem1346236 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term18 x1 y2 x2.
Proof. exact (EQ_MP (@lem1346235 x1 y2 x2) (@lem1346234 x1 y2 x2)). Qed.
Lemma lem1346237 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term19 x1 y2 x2 y1.
Proof. exact (@lem1346236 x1 y2 x2 y1). Qed.
Lemma lem1346238 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term19 x1 y2 x2 y1) = ((term20 x1 y1 x2 y2) = (term21 x1 y2 x2 y1)).
Proof. exact (eq_refl (term19 x1 y2 x2 y1)). Qed.
Lemma lem1346240 (n : nat) : term22 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1346241 (n : nat) : (term22 n) = ((treal_of_num n) = (term23 n)).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem1346243 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term24 x1 y1)) : (treal_le x1 y1) = (term24 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1346244 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term24 x1 y1)) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (SYM (@lem1346243 x1 y1 h1)). Qed.
Lemma lem1346245 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term24 x1 y1) = (treal_le x1 y1)) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (h1). Qed.
Lemma lem1346246 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term24 x1 y1) = (treal_le x1 y1)) : (treal_le x1 y1) = (term24 x1 y1).
Proof. exact (SYM (@lem1346245 x1 y1 h1)). Qed.
Lemma lem1346247 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((treal_le x1 y1) = (term24 x1 y1)) = ((term24 x1 y1) = (treal_le x1 y1)).
Proof. exact (prop_ext (fun h1 : (treal_le x1 y1) = (term24 x1 y1) => @lem1346244 x1 y1 h1) (fun h1 : (term24 x1 y1) = (treal_le x1 y1) => @lem1346246 x1 y1 h1)). Qed.
Lemma lem1346249 (m : nat) (h1 : (term25 m) = (real_of_num m)) : (term25 m) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem1346250 (m : nat) (h1 : (term25 m) = (real_of_num m)) : (real_of_num m) = (term25 m).
Proof. exact (SYM (@lem1346249 m h1)). Qed.
Lemma lem1346251 (m : nat) (h1 : (real_of_num m) = (term25 m)) : (real_of_num m) = (term25 m).
Proof. exact (h1). Qed.
Lemma lem1346252 (m : nat) (h1 : (real_of_num m) = (term25 m)) : (term25 m) = (real_of_num m).
Proof. exact (SYM (@lem1346251 m h1)). Qed.
Lemma lem1346253 (m : nat) : ((term25 m) = (real_of_num m)) = ((real_of_num m) = (term25 m)).
Proof. exact (prop_ext (fun h1 : (term25 m) = (real_of_num m) => @lem1346250 m h1) (fun h1 : (real_of_num m) = (term25 m) => @lem1346252 m h1)). Qed.
Lemma lem1346255 (n : hreal) : term10 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1346256 (n : hreal) : (term10 n) = ((term11 n) = n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1346261 (x : hreal) (y : hreal) (z : hreal) (h1 : (term26 x y z) = (term27 x y z)) : (term26 x y z) = (term27 x y z).
Proof. exact (h1). Qed.
Lemma lem1346262 (x : hreal) (y : hreal) (z : hreal) (h1 : (term26 x y z) = (term27 x y z)) : (term27 x y z) = (term26 x y z).
Proof. exact (SYM (@lem1346261 x y z h1)). Qed.
Lemma lem1346263 (x : hreal) (y : hreal) (z : hreal) (h1 : (term27 x y z) = (term26 x y z)) : (term27 x y z) = (term26 x y z).
Proof. exact (h1). Qed.
Lemma lem1346264 (x : hreal) (y : hreal) (z : hreal) (h1 : (term27 x y z) = (term26 x y z)) : (term26 x y z) = (term27 x y z).
Proof. exact (SYM (@lem1346263 x y z h1)). Qed.
Lemma lem1346265 (x : hreal) (y : hreal) (z : hreal) : ((term26 x y z) = (term27 x y z)) = ((term27 x y z) = (term26 x y z)).
Proof. exact (prop_ext (fun h1 : (term26 x y z) = (term27 x y z) => @lem1346262 x y z h1) (fun h1 : (term27 x y z) = (term26 x y z) => @lem1346264 x y z h1)). Qed.
Lemma lem1346266 (x : hreal) (y : hreal) : (term28 x y) = (term29 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1346265 x y z)). Qed.
Lemma lem1346267 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346268 (x : hreal) (y : hreal) : (term30 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1346267) (@lem1346266 x y)). Qed.
Lemma lem1346269 (x : hreal) : (term32 x) = (term33 x).
Proof. exact (fun_ext (fun y : hreal => @lem1346268 x y)). Qed.
Lemma lem1346270 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346271 (x : hreal) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem1346270) (@lem1346269 x)). Qed.
Lemma lem1346272 : term36 = term37.
Proof. exact (fun_ext (fun x : hreal => @lem1346271 x)). Qed.
Lemma lem1346273 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346274 : term38 = term39.
Proof. exact (MK_COMB (@lem1346273) (@lem1346272)). Qed.
Lemma lem1346275 : term39.
Proof. exact (EQ_MP (@lem1346274) (@lem1320203)). Qed.
Lemma lem1346276 (m : hreal) : term40 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1346277 (m : hreal) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem1346278 (m : hreal) : term41 m.
Proof. exact (EQ_MP (@lem1346277 m) (@lem1346276 m)). Qed.
Lemma lem1346279 (m : hreal) (n : hreal) : term42 m n.
Proof. exact (@lem1346278 m n). Qed.
Lemma lem1346280 (m : hreal) (n : hreal) : (term42 m n) = (term43 m n).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem1346281 (m : hreal) (n : hreal) : term43 m n.
Proof. exact (EQ_MP (@lem1346280 m n) (@lem1346279 m n)). Qed.
Lemma lem1346282 (m : hreal) (n : hreal) (p : hreal) : term44 m n p.
Proof. exact (@lem1346281 m n p). Qed.
Lemma lem1346283 (m : hreal) (n : hreal) (p : hreal) : (term44 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term44 m n p)). Qed.
Lemma lem1346285 (x : hreal) : term45 x.
Proof. exact (@lem1346275 x). Qed.
Lemma lem1346286 (x : hreal) : (term45 x) = (term35 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1346287 (x : hreal) : term35 x.
Proof. exact (EQ_MP (@lem1346286 x) (@lem1346285 x)). Qed.
Lemma lem1346288 (x : hreal) (y : hreal) : term46 x y.
Proof. exact (@lem1346287 x y). Qed.
Lemma lem1346289 (x : hreal) (y : hreal) : (term46 x y) = (term31 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1346290 (x : hreal) (y : hreal) : term31 x y.
Proof. exact (EQ_MP (@lem1346289 x y) (@lem1346288 x y)). Qed.
Lemma lem1346291 (x : hreal) (y : hreal) (z : hreal) : term47 x y z.
Proof. exact (@lem1346290 x y z). Qed.
Lemma lem1346292 (x : hreal) (y : hreal) (z : hreal) : (term47 x y z) = ((term27 x y z) = (term26 x y z)).
Proof. exact (eq_refl (term47 x y z)). Qed.
Lemma lem1346294 (x : hreal) : term48 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1346295 (x : hreal) : (term48 x) = (term49 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1346296 (x : hreal) : term49 x.
Proof. exact (EQ_MP (@lem1346295 x) (@lem1346294 x)). Qed.
Lemma lem1346297 (x : hreal) (y : hreal) : term50 x y.
Proof. exact (@lem1346296 x y). Qed.
Lemma lem1346298 (y : hreal) (x : hreal) : (term50 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term50 x y)). Qed.
Lemma lem1346300 (x1 : hreal) : term51 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1346301 (x1 : hreal) : (term51 x1) = (term52 x1).
Proof. exact (eq_refl (term51 x1)). Qed.
Lemma lem1346302 (x1 : hreal) : term52 x1.
Proof. exact (EQ_MP (@lem1346301 x1) (@lem1346300 x1)). Qed.
Lemma lem1346303 (x1 : hreal) (y2 : hreal) : term53 x1 y2.
Proof. exact (@lem1346302 x1 y2). Qed.
Lemma lem1346304 (x1 : hreal) (y2 : hreal) : (term53 x1 y2) = (term54 x1 y2).
Proof. exact (eq_refl (term53 x1 y2)). Qed.
Lemma lem1346305 (x1 : hreal) (y2 : hreal) : term54 x1 y2.
Proof. exact (EQ_MP (@lem1346304 x1 y2) (@lem1346303 x1 y2)). Qed.
Lemma lem1346306 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term55 x1 y2 x2.
Proof. exact (@lem1346305 x1 y2 x2). Qed.
Lemma lem1346307 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term55 x1 y2 x2) = (term56 x1 y2 x2).
Proof. exact (eq_refl (term55 x1 y2 x2)). Qed.
Lemma lem1346308 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term56 x1 y2 x2.
Proof. exact (EQ_MP (@lem1346307 x1 y2 x2) (@lem1346306 x1 y2 x2)). Qed.
Lemma lem1346309 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term57 x1 y2 x2 y1.
Proof. exact (@lem1346308 x1 y2 x2 y1). Qed.
Lemma lem1346310 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term57 x1 y2 x2 y1) = ((term58 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term57 x1 y2 x2 y1)). Qed.
Lemma lem1346312 : term59.
Proof. exact (@lem48081 hreal hreal). Qed.
Lemma lem1346313 (q : prod hreal hreal) : term60 q.
Proof. exact (@lem1346312 q). Qed.
Lemma lem1346314 (q : prod hreal hreal) : (term60 q) = ((term61 q) = q).
Proof. exact (eq_refl (term60 q)). Qed.
Lemma lem1346315 (q : prod hreal hreal) : (term61 q) = q.
Proof. exact (EQ_MP (@lem1346314 q) (@lem1346313 q)). Qed.
Lemma lem1346316 (q : prod hreal hreal) (h1 : (term61 q) = q) : (term61 q) = q.
Proof. exact (h1). Qed.
Lemma lem1346317 (q : prod hreal hreal) (h1 : (term61 q) = q) : q = (term61 q).
Proof. exact (SYM (@lem1346316 q h1)). Qed.
Lemma lem1346318 (q : prod hreal hreal) (h1 : q = (term61 q)) : q = (term61 q).
Proof. exact (h1). Qed.
Lemma lem1346319 (q : prod hreal hreal) (h1 : q = (term61 q)) : (term61 q) = q.
Proof. exact (SYM (@lem1346318 q h1)). Qed.
Lemma lem1346320 (q : prod hreal hreal) : ((term61 q) = q) = (q = (term61 q)).
Proof. exact (prop_ext (fun h1 : (term61 q) = q => @lem1346317 q h1) (fun h1 : q = (term61 q) => @lem1346319 q h1)). Qed.
Lemma lem1346321 (q : prod hreal hreal) : q = (term61 q).
Proof. exact (EQ_MP (@lem1346320 q) (@lem1346315 q)). Qed.
Lemma lem1346322 {A B : Type'} (f : A -> B) : term62 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1346323 {A B : Type'} (f : A -> B) : (term62 A B f) = (term63 A B f).
Proof. exact (eq_refl (term62 A B f)). Qed.
Lemma lem1346324 {A B : Type'} (f : A -> B) : term63 A B f.
Proof. exact (EQ_MP (@lem1346323 A B f) (@lem1346322 A B f)). Qed.
Lemma lem1346325 {A B : Type'} (f : A -> B) (g : A -> B) : term64 A B f g.
Proof. exact (@lem1346324 A B f g). Qed.
Lemma lem1346326 {A B : Type'} (f : A -> B) (g : A -> B) : (term64 A B f g) = ((f = g) = (term65 A B f g)).
Proof. exact (eq_refl (term64 A B f g)). Qed.
Lemma lem1346328 (x : hreal) : term66 x.
Proof. exact (@lem1319802 x). Qed.
Lemma lem1346329 (x : hreal) : (term66 x) = (term67 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1346330 (x : hreal) : term67 x.
Proof. exact (EQ_MP (@lem1346329 x) (@lem1346328 x)). Qed.
Lemma lem1346331 (x : hreal) (y : hreal) : term68 x y.
Proof. exact (@lem1346330 x y). Qed.
Lemma lem1346332 (y : hreal) (x : hreal) : (term68 x y) = (term69 y x).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem1346334 (n : hreal) : term10 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1346335 (n : hreal) : (term10 n) = ((term11 n) = n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1346337 (x : hreal) : term12 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1346338 (x : hreal) : (term12 x) = ((term4 x) = x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1346340 (x1 : hreal) : term13 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1346341 (x1 : hreal) : (term13 x1) = (term14 x1).
Proof. exact (eq_refl (term13 x1)). Qed.
Lemma lem1346342 (x1 : hreal) : term14 x1.
Proof. exact (EQ_MP (@lem1346341 x1) (@lem1346340 x1)). Qed.
Lemma lem1346343 (x1 : hreal) (y2 : hreal) : term15 x1 y2.
Proof. exact (@lem1346342 x1 y2). Qed.
Lemma lem1346344 (x1 : hreal) (y2 : hreal) : (term15 x1 y2) = (term16 x1 y2).
Proof. exact (eq_refl (term15 x1 y2)). Qed.
Lemma lem1346345 (x1 : hreal) (y2 : hreal) : term16 x1 y2.
Proof. exact (EQ_MP (@lem1346344 x1 y2) (@lem1346343 x1 y2)). Qed.
Lemma lem1346346 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term17 x1 y2 x2.
Proof. exact (@lem1346345 x1 y2 x2). Qed.
Lemma lem1346347 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term17 x1 y2 x2) = (term18 x1 y2 x2).
Proof. exact (eq_refl (term17 x1 y2 x2)). Qed.
Lemma lem1346348 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term18 x1 y2 x2.
Proof. exact (EQ_MP (@lem1346347 x1 y2 x2) (@lem1346346 x1 y2 x2)). Qed.
Lemma lem1346349 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term19 x1 y2 x2 y1.
Proof. exact (@lem1346348 x1 y2 x2 y1). Qed.
Lemma lem1346350 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term19 x1 y2 x2 y1) = ((term20 x1 y1 x2 y2) = (term21 x1 y2 x2 y1)).
Proof. exact (eq_refl (term19 x1 y2 x2 y1)). Qed.
Lemma lem1346352 (n : nat) : term22 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1346353 (n : nat) : (term22 n) = ((treal_of_num n) = (term23 n)).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem1346355 : term59.
Proof. exact (@lem48081 hreal hreal). Qed.
Lemma lem1346356 (p : prod hreal hreal) : term60 p.
Proof. exact (@lem1346355 p). Qed.
Lemma lem1346357 (p : prod hreal hreal) : (term60 p) = ((term61 p) = p).
Proof. exact (eq_refl (term60 p)). Qed.
Lemma lem1346358 (p : prod hreal hreal) : (term61 p) = p.
Proof. exact (EQ_MP (@lem1346357 p) (@lem1346356 p)). Qed.
Lemma lem1346359 (p : prod hreal hreal) (h1 : (term61 p) = p) : (term61 p) = p.
Proof. exact (h1). Qed.
Lemma lem1346360 (p : prod hreal hreal) (h1 : (term61 p) = p) : p = (term61 p).
Proof. exact (SYM (@lem1346359 p h1)). Qed.
Lemma lem1346361 (p : prod hreal hreal) (h1 : p = (term61 p)) : p = (term61 p).
Proof. exact (h1). Qed.
Lemma lem1346362 (p : prod hreal hreal) (h1 : p = (term61 p)) : (term61 p) = p.
Proof. exact (SYM (@lem1346361 p h1)). Qed.
Lemma lem1346363 (p : prod hreal hreal) : ((term61 p) = p) = (p = (term61 p)).
Proof. exact (prop_ext (fun h1 : (term61 p) = p => @lem1346360 p h1) (fun h1 : p = (term61 p) => @lem1346362 p h1)). Qed.
Lemma lem1346364 (p : prod hreal hreal) : p = (term61 p).
Proof. exact (EQ_MP (@lem1346363 p) (@lem1346358 p)). Qed.
Lemma lem1346365 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term24 x1 y1)) : (treal_le x1 y1) = (term24 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1346366 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term24 x1 y1)) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (SYM (@lem1346365 x1 y1 h1)). Qed.
Lemma lem1346367 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term24 x1 y1) = (treal_le x1 y1)) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (h1). Qed.
Lemma lem1346368 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term24 x1 y1) = (treal_le x1 y1)) : (treal_le x1 y1) = (term24 x1 y1).
Proof. exact (SYM (@lem1346367 x1 y1 h1)). Qed.
Lemma lem1346369 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((treal_le x1 y1) = (term24 x1 y1)) = ((term24 x1 y1) = (treal_le x1 y1)).
Proof. exact (prop_ext (fun h1 : (treal_le x1 y1) = (term24 x1 y1) => @lem1346366 x1 y1 h1) (fun h1 : (term24 x1 y1) = (treal_le x1 y1) => @lem1346368 x1 y1 h1)). Qed.
Lemma lem1346371 (m : nat) (h1 : (term25 m) = (real_of_num m)) : (term25 m) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem1346372 (m : nat) (h1 : (term25 m) = (real_of_num m)) : (real_of_num m) = (term25 m).
Proof. exact (SYM (@lem1346371 m h1)). Qed.
Lemma lem1346373 (m : nat) (h1 : (real_of_num m) = (term25 m)) : (real_of_num m) = (term25 m).
Proof. exact (h1). Qed.
Lemma lem1346374 (m : nat) (h1 : (real_of_num m) = (term25 m)) : (term25 m) = (real_of_num m).
Proof. exact (SYM (@lem1346373 m h1)). Qed.
Lemma lem1346375 (m : nat) : ((term25 m) = (real_of_num m)) = ((real_of_num m) = (term25 m)).
Proof. exact (prop_ext (fun h1 : (term25 m) = (real_of_num m) => @lem1346372 m h1) (fun h1 : (real_of_num m) = (term25 m) => @lem1346374 m h1)). Qed.
Lemma lem1346377 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1346378 (x : real) : (term70 x) = ((term71 x) = (dest_real x)).
Proof. exact (@lem1337493 (dest_real x)). Qed.
Lemma lem1346379 (n : hreal) : term10 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1346380 (n : hreal) : (term10 n) = ((term11 n) = n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1346385 (x1 : hreal) : term13 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1346386 (x1 : hreal) : (term13 x1) = (term14 x1).
Proof. exact (eq_refl (term13 x1)). Qed.
Lemma lem1346387 (x1 : hreal) : term14 x1.
Proof. exact (EQ_MP (@lem1346386 x1) (@lem1346385 x1)). Qed.
Lemma lem1346388 (x1 : hreal) (y2 : hreal) : term15 x1 y2.
Proof. exact (@lem1346387 x1 y2). Qed.
Lemma lem1346389 (x1 : hreal) (y2 : hreal) : (term15 x1 y2) = (term16 x1 y2).
Proof. exact (eq_refl (term15 x1 y2)). Qed.
Lemma lem1346390 (x1 : hreal) (y2 : hreal) : term16 x1 y2.
Proof. exact (EQ_MP (@lem1346389 x1 y2) (@lem1346388 x1 y2)). Qed.
Lemma lem1346391 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term17 x1 y2 x2.
Proof. exact (@lem1346390 x1 y2 x2). Qed.
Lemma lem1346392 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term17 x1 y2 x2) = (term18 x1 y2 x2).
Proof. exact (eq_refl (term17 x1 y2 x2)). Qed.
Lemma lem1346393 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term18 x1 y2 x2.
Proof. exact (EQ_MP (@lem1346392 x1 y2 x2) (@lem1346391 x1 y2 x2)). Qed.
Lemma lem1346394 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term19 x1 y2 x2 y1.
Proof. exact (@lem1346393 x1 y2 x2 y1). Qed.
Lemma lem1346395 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term19 x1 y2 x2 y1) = ((term20 x1 y1 x2 y2) = (term21 x1 y2 x2 y1)).
Proof. exact (eq_refl (term19 x1 y2 x2 y1)). Qed.
Lemma lem1346397 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term24 x1 y1)) : (treal_le x1 y1) = (term24 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1346398 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term24 x1 y1)) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (SYM (@lem1346397 x1 y1 h1)). Qed.
Lemma lem1346399 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term24 x1 y1) = (treal_le x1 y1)) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (h1). Qed.
Lemma lem1346400 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term24 x1 y1) = (treal_le x1 y1)) : (treal_le x1 y1) = (term24 x1 y1).
Proof. exact (SYM (@lem1346399 x1 y1 h1)). Qed.
Lemma lem1346401 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((treal_le x1 y1) = (term24 x1 y1)) = ((term24 x1 y1) = (treal_le x1 y1)).
Proof. exact (prop_ext (fun h1 : (treal_le x1 y1) = (term24 x1 y1) => @lem1346398 x1 y1 h1) (fun h1 : (term24 x1 y1) = (treal_le x1 y1) => @lem1346400 x1 y1 h1)). Qed.
Lemma lem1346418 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1346419 (f : hreal -> real) (y : hreal) : (term73 f y) = (f y).
Proof. exact (@lem1346418 hreal real f y). Qed.
Lemma lem1346420 (y : hreal) : (term74 y) = (term75 y).
Proof. exact (@lem1346419 term76 y). Qed.
Lemma lem1346421 (y : hreal) : (term75 y) = (term77 y).
Proof. exact (eq_refl (term75 y)). Qed.
Lemma lem1346422 : term78 = term76.
Proof. exact (fun_ext (fun y : hreal => @lem1346421 y)). Qed.
Lemma lem1346423 (y : hreal) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1346424 (y : hreal) : (term74 y) = (term75 y).
Proof. exact (MK_COMB (@lem1346422) (@lem1346423 y)). Qed.
Lemma lem1346425 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1346426 (y : hreal) : (term79 y) = (term80 y).
Proof. exact (MK_COMB (@lem1346425) (@lem1346424 y)). Qed.
Lemma lem1346427 (y : hreal) : (term75 y) = (term77 y).
Proof. exact (eq_refl (term75 y)). Qed.
Lemma lem1346428 (y : hreal) : ((term74 y) = (term75 y)) = ((term75 y) = (term77 y)).
Proof. exact (MK_COMB (@lem1346426 y) (@lem1346427 y)). Qed.
Lemma lem1346429 (y : hreal) : (term75 y) = (term77 y).
Proof. exact (EQ_MP (@lem1346428 y) (@lem1346420 y)). Qed.
Lemma lem1346430 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem1346431 (x : real) (y : hreal) : (x = (term75 y)) = (x = (term77 y)).
Proof. exact (MK_COMB (@lem1346430 x) (@lem1346429 y)). Qed.
Lemma lem1346434 (x : real) : (term81 x) = (term82 x).
Proof. exact (fun_ext (fun y : hreal => @lem1346431 x y)). Qed.
Lemma lem1346435 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1346436 (x : real) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1346435) (@lem1346434 x)). Qed.
Lemma lem1346441 (x : real) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem1346442 (x : real) : ((term86 x) = (term83 x)) = ((term86 x) = (term84 x)).
Proof. exact (MK_COMB (@lem1346441 x) (@lem1346436 x)). Qed.
Lemma lem1346445 : term87 = term88.
Proof. exact (fun_ext (fun x : real => @lem1346442 x)). Qed.
Lemma lem1346446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1346447 : term89 = term90.
Proof. exact (MK_COMB (@lem1346446) (@lem1346445)). Qed.
Lemma lem1346452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1346453 : term91 = term92.
Proof. exact (MK_COMB (@lem1346452) (@lem1346447)). Qed.
Lemma lem1346465 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1346466 (f : hreal -> real) (y : hreal) : (term73 f y) = (f y).
Proof. exact (@lem1346465 hreal real f y). Qed.
Lemma lem1346467 (y : hreal) : (term74 y) = (term75 y).
Proof. exact (@lem1346466 term76 y). Qed.
Lemma lem1346468 (y : hreal) : (term75 y) = (term77 y).
Proof. exact (eq_refl (term75 y)). Qed.
Lemma lem1346469 : term78 = term76.
Proof. exact (fun_ext (fun y : hreal => @lem1346468 y)). Qed.
Lemma lem1346470 (y : hreal) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1346471 (y : hreal) : (term74 y) = (term75 y).
Proof. exact (MK_COMB (@lem1346469) (@lem1346470 y)). Qed.
Lemma lem1346472 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1346473 (y : hreal) : (term79 y) = (term80 y).
Proof. exact (MK_COMB (@lem1346472) (@lem1346471 y)). Qed.
Lemma lem1346474 (y : hreal) : (term75 y) = (term77 y).
Proof. exact (eq_refl (term75 y)). Qed.
Lemma lem1346475 (y : hreal) : ((term74 y) = (term75 y)) = ((term75 y) = (term77 y)).
Proof. exact (MK_COMB (@lem1346473 y) (@lem1346474 y)). Qed.
Lemma lem1346476 (y : hreal) : (term75 y) = (term77 y).
Proof. exact (EQ_MP (@lem1346475 y) (@lem1346467 y)). Qed.
Lemma lem1346477 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1346478 (y : hreal) : (term93 y) = (term94 y).
Proof. exact (MK_COMB (@lem1346477) (@lem1346476 y)). Qed.
Lemma lem1346480 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1346481 (f : hreal -> real) (y : hreal) : (term73 f y) = (f y).
Proof. exact (@lem1346480 hreal real f y). Qed.
Lemma lem1346482 (z : hreal) : (term74 z) = (term75 z).
Proof. exact (@lem1346481 term76 z). Qed.
Lemma lem1346483 (y : hreal) : (term75 y) = (term77 y).
Proof. exact (eq_refl (term75 y)). Qed.
Lemma lem1346484 : term78 = term76.
Proof. exact (fun_ext (fun y : hreal => @lem1346483 y)). Qed.
Lemma lem1346485 (z : hreal) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1346486 (z : hreal) : (term74 z) = (term75 z).
Proof. exact (MK_COMB (@lem1346484) (@lem1346485 z)). Qed.
Lemma lem1346487 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1346488 (z : hreal) : (term79 z) = (term80 z).
Proof. exact (MK_COMB (@lem1346487) (@lem1346486 z)). Qed.
Lemma lem1346489 (z : hreal) : (term75 z) = (term77 z).
Proof. exact (eq_refl (term75 z)). Qed.
Lemma lem1346490 (z : hreal) : ((term74 z) = (term75 z)) = ((term75 z) = (term77 z)).
Proof. exact (MK_COMB (@lem1346488 z) (@lem1346489 z)). Qed.
Lemma lem1346491 (z : hreal) : (term75 z) = (term77 z).
Proof. exact (EQ_MP (@lem1346490 z) (@lem1346482 z)). Qed.
Lemma lem1346492 (y : hreal) (z : hreal) : (term95 y z) = (term96 y z).
Proof. exact (MK_COMB (@lem1346478 y) (@lem1346491 z)). Qed.
Lemma lem1346494 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (EQ_MP (@lem1346401 x1 y1) (@lem1337991 x1 y1)). Qed.
Lemma lem1346495 (y : hreal) (z : hreal) : (term96 y z) = (term97 y z).
Proof. exact (@lem1346494 (term98 y) (term98 z)). Qed.
Lemma lem1346496 (y : hreal) (z : hreal) : (term95 y z) = (term97 y z).
Proof. exact (TRANS (@lem1346492 y z) (@lem1346495 y z)). Qed.
Lemma lem1346497 (y : hreal) (z : hreal) : (term99 y z) = (term99 y z).
Proof. exact (eq_refl (term99 y z)). Qed.
Lemma lem1346498 (y : hreal) (z : hreal) : ((hreal_le y z) = (term95 y z)) = ((hreal_le y z) = (term97 y z)).
Proof. exact (MK_COMB (@lem1346497 y z) (@lem1346496 y z)). Qed.
Lemma lem1346501 (y : hreal) : (term100 y) = (term101 y).
Proof. exact (fun_ext (fun z : hreal => @lem1346498 y z)). Qed.
Lemma lem1346502 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346503 (y : hreal) : (term102 y) = (term103 y).
Proof. exact (MK_COMB (@lem1346502) (@lem1346501 y)). Qed.
Lemma lem1346508 : term104 = term105.
Proof. exact (fun_ext (fun y : hreal => @lem1346503 y)). Qed.
Lemma lem1346509 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346510 : term106 = term107.
Proof. exact (MK_COMB (@lem1346509) (@lem1346508)). Qed.
Lemma lem1346515 : term108 = term109.
Proof. exact (MK_COMB (@lem1346453) (@lem1346510)). Qed.
Lemma lem1346518 : term109 = term108.
Proof. exact (SYM (@lem1346515)). Qed.
Lemma lem1346544 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term20 x1 y1 x2 y2) = (term21 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1346395 x1 y2 x2 y1) (@lem1346394 x1 y2 x2 y1)). Qed.
Lemma lem1346545 (y : hreal) (z : hreal) : (term97 y z) = (term110 y z).
Proof. exact (@lem1346544 y term111 z term111). Qed.
Lemma lem1346547 (n : hreal) : (term11 n) = n.
Proof. exact (EQ_MP (@lem1346380 n) (@lem1346379 n)). Qed.
Lemma lem1346548 (y : hreal) : (term11 y) = y.
Proof. exact (@lem1346547 y). Qed.
Lemma lem1346549 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1346550 (y : hreal) : (term112 y) = (hreal_le y).
Proof. exact (MK_COMB (@lem1346549) (@lem1346548 y)). Qed.
Lemma lem1346552 (n : hreal) : (term11 n) = n.
Proof. exact (EQ_MP (@lem1346380 n) (@lem1346379 n)). Qed.
Lemma lem1346553 (z : hreal) : (term11 z) = z.
Proof. exact (@lem1346552 z). Qed.
Lemma lem1346554 (y : hreal) (z : hreal) : (term110 y z) = (hreal_le y z).
Proof. exact (MK_COMB (@lem1346550 y) (@lem1346553 z)). Qed.
Lemma lem1346555 (y : hreal) (z : hreal) : (term97 y z) = (hreal_le y z).
Proof. exact (TRANS (@lem1346545 y z) (@lem1346554 y z)). Qed.
Lemma lem1346556 (y : hreal) (z : hreal) : (term99 y z) = (term99 y z).
Proof. exact (eq_refl (term99 y z)). Qed.
Lemma lem1346557 (y : hreal) (z : hreal) : ((hreal_le y z) = (term97 y z)) = ((hreal_le y z) = (hreal_le y z)).
Proof. exact (MK_COMB (@lem1346556 y z) (@lem1346555 y z)). Qed.
Lemma lem1346559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1346560 (x : Prop) : (x = x) = True.
Proof. exact (@lem1346559 Prop x). Qed.
Lemma lem1346561 (y : hreal) (z : hreal) : ((hreal_le y z) = (hreal_le y z)) = True.
Proof. exact (@lem1346560 (hreal_le y z)). Qed.
Lemma lem1346562 (y : hreal) (z : hreal) : ((hreal_le y z) = (term97 y z)) = True.
Proof. exact (TRANS (@lem1346557 y z) (@lem1346561 y z)). Qed.
Lemma lem1346563 (y : hreal) : (term101 y) = term113.
Proof. exact (fun_ext (fun z : hreal => @lem1346562 y z)). Qed.
Lemma lem1346564 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346565 (y : hreal) : (term103 y) = term114.
Proof. exact (MK_COMB (@lem1346564) (@lem1346563 y)). Qed.
Lemma lem1346567 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1346568 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1346567 hreal t). Qed.
Lemma lem1346569 : term114 = True.
Proof. exact (@lem1346568 True). Qed.
Lemma lem1346570 (y : hreal) : (term103 y) = True.
Proof. exact (TRANS (@lem1346565 y) (@lem1346569)). Qed.
Lemma lem1346571 : term105 = term113.
Proof. exact (fun_ext (fun y : hreal => @lem1346570 y)). Qed.
Lemma lem1346572 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1346573 : term107 = term114.
Proof. exact (MK_COMB (@lem1346572) (@lem1346571)). Qed.
Lemma lem1346575 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1346576 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1346575 hreal t). Qed.
Lemma lem1346577 : term114 = True.
Proof. exact (@lem1346576 True). Qed.
Lemma lem1346578 : term107 = True.
Proof. exact (TRANS (@lem1346573) (@lem1346577)). Qed.
Lemma lem1346579 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem1346580 : term109 = term117.
Proof. exact (MK_COMB (@lem1346579) (@lem1346578)). Qed.
Lemma lem1346582 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1346583 : term117 = term90.
Proof. exact (@lem1346582 term90). Qed.
Lemma lem1346596 : term109 = term90.
Proof. exact (TRANS (@lem1346580) (@lem1346583)). Qed.
Lemma lem1346597 : term90 = term109.
Proof. exact (SYM (@lem1346596)). Qed.
Lemma lem1346613 (a : real) : (term118 a) = a.
Proof. exact (@axiom_23 a). Qed.
Lemma lem1346614 (x : real) : (term118 x) = x.
Proof. exact (@lem1346613 x). Qed.
Lemma lem1346615 : dest_real = dest_real.
Proof. exact (eq_refl dest_real). Qed.
Lemma lem1346616 (x : real) : (term71 x) = (dest_real x).
Proof. exact (MK_COMB (@lem1346615) (@lem1346614 x)). Qed.
Lemma lem1346617 : (@eq ((prod hreal hreal) -> Prop)) = (@eq ((prod hreal hreal) -> Prop)).
Proof. exact (eq_refl (@eq ((prod hreal hreal) -> Prop))). Qed.
Lemma lem1346618 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1346617) (@lem1346616 x)). Qed.
Lemma lem1346619 (x : real) : (dest_real x) = (dest_real x).
Proof. exact (eq_refl (dest_real x)). Qed.
Lemma lem1346620 (x : real) : ((term71 x) = (dest_real x)) = ((dest_real x) = (dest_real x)).
Proof. exact (MK_COMB (@lem1346618 x) (@lem1346619 x)). Qed.
Lemma lem1346622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1346623 (x : type1233) : (x = x) = True.
Proof. exact (@lem1346622 type1233 x). Qed.
Lemma lem1346624 (x : real) : ((dest_real x) = (dest_real x)) = True.
Proof. exact (@lem1346623 (dest_real x)). Qed.
Lemma lem1346625 (x : real) : ((term71 x) = (dest_real x)) = True.
Proof. exact (TRANS (@lem1346620 x) (@lem1346624 x)). Qed.
Lemma lem1346626 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1346627 (x : real) : ((term70 x) = ((term71 x) = (dest_real x))) = ((term70 x) = True).
Proof. exact (MK_COMB (@lem1346626 x) (@lem1346625 x)). Qed.
Lemma lem1346629 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1346630 (x : real) : ((term70 x) = True) = (term70 x).
Proof. exact (@lem1346629 (term70 x)). Qed.
Lemma lem1346637 (x : real) : ((term70 x) = ((term71 x) = (dest_real x))) = (term70 x).
Proof. exact (TRANS (@lem1346627 x) (@lem1346630 x)). Qed.
Lemma lem1346638 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1346639 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1346638) (@lem1346637 x)). Qed.
Lemma lem1346648 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1346649 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1346639 x) (@lem1346648 x)). Qed.
Lemma lem1346652 (x : real) : (term126 x) = (term125 x).
Proof. exact (SYM (@lem1346649 x)). Qed.
Lemma lem1346653 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1346654 (x : real) (p : prod hreal hreal) (h1 : (dest_real x) = (treal_eq p)) : (dest_real x) = (treal_eq p).
Proof. exact (h1). Qed.
Lemma lem1346655 (x : real) (p : prod hreal hreal) (h1 : (dest_real x) = (treal_eq p)) : (dest_real x) = (treal_eq p).
Proof. exact (h1). Qed.
Lemma lem1346656 (x : real) (p : prod hreal hreal) (h1 : (dest_real x) = (treal_eq p)) : (term118 x) = (term127 p).
Proof. exact (MK_COMB (@lem1346377) (@lem1346655 x p h1)). Qed.
Lemma lem1346664 (a : real) : (term118 a) = a.
Proof. exact (@axiom_23 a). Qed.
Lemma lem1346665 (x : real) : (term118 x) = x.
Proof. exact (@lem1346664 x). Qed.
Lemma lem1346666 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1346667 (x : real) : (term128 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1346666) (@lem1346665 x)). Qed.
Lemma lem1346668 (p : prod hreal hreal) : (term127 p) = (term127 p).
Proof. exact (eq_refl (term127 p)). Qed.
Lemma lem1346669 (x : real) (p : prod hreal hreal) : ((term118 x) = (term127 p)) = (x = (term127 p)).
Proof. exact (MK_COMB (@lem1346667 x) (@lem1346668 p)). Qed.
Lemma lem1346672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1346673 (x : real) (p : prod hreal hreal) : (term129 x p) = (term130 x p).
Proof. exact (MK_COMB (@lem1346672) (@lem1346669 x p)). Qed.
Lemma lem1346682 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1346683 (p : prod hreal hreal) (x : real) : (term131 p x) = (term132 p x).
Proof. exact (MK_COMB (@lem1346673 x p) (@lem1346682 x)). Qed.
Lemma lem1346688 (p : prod hreal hreal) (x : real) : (term132 p x) = (term131 p x).
Proof. exact (SYM (@lem1346683 p x)). Qed.
Lemma lem1346689 (x : real) (p : prod hreal hreal) (h1 : x = (term127 p)) : x = (term127 p).
Proof. exact (h1). Qed.
Lemma lem1346690 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem1346691 (x : real) (p : prod hreal hreal) (h1 : x = (term127 p)) : (term134 x) = (term135 p).
Proof. exact (MK_COMB (@lem1346690) (@lem1346689 x p h1)). Qed.
Lemma lem1346692 (p : prod hreal hreal) : (term135 p) = (term136 p).
Proof. exact (eq_refl (term135 p)). Qed.
Lemma lem1346693 (x : real) : (term137 x) = (term137 x).
Proof. exact (eq_refl (term137 x)). Qed.
Lemma lem1346694 (x : real) (p : prod hreal hreal) : ((term134 x) = (term135 p)) = ((term134 x) = (term136 p)).
Proof. exact (MK_COMB (@lem1346693 x) (@lem1346692 p)). Qed.
Lemma lem1346695 (x : real) : (term134 x) = (term124 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1346696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346697 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1346696) (@lem1346695 x)). Qed.
Lemma lem1346698 (p : prod hreal hreal) : (term136 p) = (term136 p).
Proof. exact (eq_refl (term136 p)). Qed.
Lemma lem1346699 (x : real) (p : prod hreal hreal) : ((term134 x) = (term136 p)) = ((term124 x) = (term136 p)).
Proof. exact (MK_COMB (@lem1346697 x) (@lem1346698 p)). Qed.
Lemma lem1346700 (x : real) (p : prod hreal hreal) : ((term134 x) = (term135 p)) = ((term124 x) = (term136 p)).
Proof. exact (TRANS (@lem1346694 x p) (@lem1346699 x p)). Qed.
Lemma lem1346701 (x : real) (p : prod hreal hreal) (h1 : x = (term127 p)) : (term124 x) = (term136 p).
Proof. exact (EQ_MP (@lem1346700 x p) (@lem1346691 x p h1)). Qed.
Lemma lem1346702 (x : real) (p : prod hreal hreal) (h1 : x = (term127 p)) : (term136 p) = (term124 x).
Proof. exact (SYM (@lem1346701 x p h1)). Qed.
Lemma lem1346706 (m : nat) : (real_of_num m) = (term25 m).
Proof. exact (EQ_MP (@lem1346375 m) (@lem1337537 m)). Qed.
Lemma lem1346707 : term139 = term140.
Proof. exact (@lem1346706 (NUMERAL 0)). Qed.
Lemma lem1346708 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1346709 : term141 = term142.
Proof. exact (MK_COMB (@lem1346708) (@lem1346707)). Qed.
Lemma lem1346710 (p : prod hreal hreal) : (term127 p) = (term127 p).
Proof. exact (eq_refl (term127 p)). Qed.
Lemma lem1346711 (p : prod hreal hreal) : (term143 p) = (term144 p).
Proof. exact (MK_COMB (@lem1346709) (@lem1346710 p)). Qed.
Lemma lem1346713 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (EQ_MP (@lem1346369 x1 y1) (@lem1337991 x1 y1)). Qed.
Lemma lem1346714 (p : prod hreal hreal) : (term144 p) = (term145 p).
Proof. exact (@lem1346713 term146 p). Qed.
Lemma lem1346715 (p : prod hreal hreal) : (term143 p) = (term145 p).
Proof. exact (TRANS (@lem1346711 p) (@lem1346714 p)). Qed.
Lemma lem1346716 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1346717 (p : prod hreal hreal) : (term147 p) = (term148 p).
Proof. exact (MK_COMB (@lem1346716) (@lem1346715 p)). Qed.
Lemma lem1346724 (p : prod hreal hreal) : (term149 p) = (term149 p).
Proof. exact (eq_refl (term149 p)). Qed.
Lemma lem1346725 (p : prod hreal hreal) : (term136 p) = (term150 p).
Proof. exact (MK_COMB (@lem1346717 p) (@lem1346724 p)). Qed.
Lemma lem1346728 (p : prod hreal hreal) : (term150 p) = (term136 p).
Proof. exact (SYM (@lem1346725 p)). Qed.
Lemma lem1346729 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem1346730 (p : prod hreal hreal) : (term152 p) = (term153 p).
Proof. exact (MK_COMB (@lem1346729) (@lem1346364 p)). Qed.
Lemma lem1346731 (p : prod hreal hreal) : (term153 p) = (term154 p).
Proof. exact (eq_refl (term153 p)). Qed.
Lemma lem1346732 (p : prod hreal hreal) : (term155 p) = (term155 p).
Proof. exact (eq_refl (term155 p)). Qed.
Lemma lem1346733 (p : prod hreal hreal) : ((term152 p) = (term153 p)) = ((term152 p) = (term154 p)).
Proof. exact (MK_COMB (@lem1346732 p) (@lem1346731 p)). Qed.
Lemma lem1346734 (p : prod hreal hreal) : (term152 p) = (term150 p).
Proof. exact (eq_refl (term152 p)). Qed.
Lemma lem1346735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346736 (p : prod hreal hreal) : (term155 p) = (term156 p).
Proof. exact (MK_COMB (@lem1346735) (@lem1346734 p)). Qed.
Lemma lem1346737 (p : prod hreal hreal) : (term154 p) = (term154 p).
Proof. exact (eq_refl (term154 p)). Qed.
Lemma lem1346738 (p : prod hreal hreal) : ((term152 p) = (term154 p)) = ((term150 p) = (term154 p)).
Proof. exact (MK_COMB (@lem1346736 p) (@lem1346737 p)). Qed.
Lemma lem1346739 (p : prod hreal hreal) : ((term152 p) = (term153 p)) = ((term150 p) = (term154 p)).
Proof. exact (TRANS (@lem1346733 p) (@lem1346738 p)). Qed.
Lemma lem1346740 (p : prod hreal hreal) : (term150 p) = (term154 p).
Proof. exact (EQ_MP (@lem1346739 p) (@lem1346730 p)). Qed.
Lemma lem1346741 (p : prod hreal hreal) : (term154 p) = (term150 p).
Proof. exact (SYM (@lem1346740 p)). Qed.
Lemma lem1346743 (n : nat) : (treal_of_num n) = (term23 n).
Proof. exact (EQ_MP (@lem1346353 n) (@lem1346352 n)). Qed.
Lemma lem1346744 : term146 = term157.
Proof. exact (@lem1346743 (NUMERAL 0)). Qed.
Lemma lem1346745 : treal_le = treal_le.
Proof. exact (eq_refl treal_le). Qed.
Lemma lem1346746 : term158 = term159.
Proof. exact (MK_COMB (@lem1346745) (@lem1346744)). Qed.
Lemma lem1346747 (p : prod hreal hreal) : (term61 p) = (term61 p).
Proof. exact (eq_refl (term61 p)). Qed.
Lemma lem1346748 (p : prod hreal hreal) : (term160 p) = (term161 p).
Proof. exact (MK_COMB (@lem1346746) (@lem1346747 p)). Qed.
Lemma lem1346750 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term20 x1 y1 x2 y2) = (term21 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1346350 x1 y2 x2 y1) (@lem1346349 x1 y2 x2 y1)). Qed.
Lemma lem1346751 (p : prod hreal hreal) : (term161 p) = (term162 p).
Proof. exact (@lem1346750 term111 (@snd hreal hreal p) (@fst hreal hreal p) term111). Qed.
Lemma lem1346752 (p : prod hreal hreal) : (term160 p) = (term162 p).
Proof. exact (TRANS (@lem1346748 p) (@lem1346751 p)). Qed.
Lemma lem1346753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1346754 (p : prod hreal hreal) : (term163 p) = (term164 p).
Proof. exact (MK_COMB (@lem1346753) (@lem1346752 p)). Qed.
Lemma lem1346755 (p : prod hreal hreal) : (term165 p) = (term165 p).
Proof. exact (eq_refl (term165 p)). Qed.
Lemma lem1346756 (p : prod hreal hreal) : (term154 p) = (term166 p).
Proof. exact (MK_COMB (@lem1346754 p) (@lem1346755 p)). Qed.
Lemma lem1346757 (p : prod hreal hreal) : (term166 p) = (term154 p).
Proof. exact (SYM (@lem1346756 p)). Qed.
Lemma lem1346759 (x : hreal) : (term4 x) = x.
Proof. exact (EQ_MP (@lem1346338 x) (@lem1346337 x)). Qed.
Lemma lem1346760 (p : prod hreal hreal) : (term167 p) = (@snd hreal hreal p).
Proof. exact (@lem1346759 (@snd hreal hreal p)). Qed.
Lemma lem1346761 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1346762 (p : prod hreal hreal) : (term168 p) = (term169 p).
Proof. exact (MK_COMB (@lem1346761) (@lem1346760 p)). Qed.
Lemma lem1346764 (n : hreal) : (term11 n) = n.
Proof. exact (EQ_MP (@lem1346335 n) (@lem1346334 n)). Qed.
Lemma lem1346765 (p : prod hreal hreal) : (term170 p) = (@fst hreal hreal p).
Proof. exact (@lem1346764 (@fst hreal hreal p)). Qed.
Lemma lem1346766 (p : prod hreal hreal) : (term162 p) = (term171 p).
Proof. exact (MK_COMB (@lem1346762 p) (@lem1346765 p)). Qed.
Lemma lem1346767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1346768 (p : prod hreal hreal) : (term164 p) = (term172 p).
Proof. exact (MK_COMB (@lem1346767) (@lem1346766 p)). Qed.
Lemma lem1346769 (p : prod hreal hreal) : (term165 p) = (term165 p).
Proof. exact (eq_refl (term165 p)). Qed.
Lemma lem1346770 (p : prod hreal hreal) : (term166 p) = (term173 p).
Proof. exact (MK_COMB (@lem1346768 p) (@lem1346769 p)). Qed.
Lemma lem1346771 (p : prod hreal hreal) : (term173 p) = (term166 p).
Proof. exact (SYM (@lem1346770 p)). Qed.
Lemma lem1346772 (p : prod hreal hreal) (h1 : term171 p) : term171 p.
Proof. exact (h1). Qed.
Lemma lem1346774 (y : hreal) (x : hreal) : term69 y x.
Proof. exact (EQ_MP (@lem1346332 y x) (@lem1346331 x y)). Qed.
Lemma lem1346775 (p : prod hreal hreal) : term174 p.
Proof. exact (@lem1346774 (@fst hreal hreal p) (@snd hreal hreal p)). Qed.
Lemma lem1346776 (p : prod hreal hreal) (h1 : term171 p) : term175 p.
Proof. exact (@lem1346775 p (@lem1346772 p h1)). Qed.
Lemma lem1346777 (p : prod hreal hreal) (d : hreal) (h1 : (@fst hreal hreal p) = (term176 p d)) : (@fst hreal hreal p) = (term176 p d).
Proof. exact (h1). Qed.
Lemma lem1346778 (p : prod hreal hreal) : (term177 p) = (term177 p).
Proof. exact (eq_refl (term177 p)). Qed.
Lemma lem1346779 (p : prod hreal hreal) (d : hreal) (h1 : (@fst hreal hreal p) = (term176 p d)) : (term178 p) = (term179 p d).
Proof. exact (MK_COMB (@lem1346778 p) (@lem1346777 p d h1)). Qed.
Lemma lem1346780 (d : hreal) (p : prod hreal hreal) : (term179 p d) = (term180 d p).
Proof. exact (eq_refl (term179 p d)). Qed.
Lemma lem1346781 (p : prod hreal hreal) : (term181 p) = (term181 p).
Proof. exact (eq_refl (term181 p)). Qed.
Lemma lem1346782 (d : hreal) (p : prod hreal hreal) : ((term178 p) = (term179 p d)) = ((term178 p) = (term180 d p)).
Proof. exact (MK_COMB (@lem1346781 p) (@lem1346780 d p)). Qed.
Lemma lem1346783 (p : prod hreal hreal) : (term178 p) = (term165 p).
Proof. exact (eq_refl (term178 p)). Qed.
Lemma lem1346784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346785 (p : prod hreal hreal) : (term181 p) = (term182 p).
Proof. exact (MK_COMB (@lem1346784) (@lem1346783 p)). Qed.
Lemma lem1346786 (d : hreal) (p : prod hreal hreal) : (term180 d p) = (term180 d p).
Proof. exact (eq_refl (term180 d p)). Qed.
Lemma lem1346787 (d : hreal) (p : prod hreal hreal) : ((term178 p) = (term180 d p)) = ((term165 p) = (term180 d p)).
Proof. exact (MK_COMB (@lem1346785 p) (@lem1346786 d p)). Qed.
Lemma lem1346788 (d : hreal) (p : prod hreal hreal) : ((term178 p) = (term179 p d)) = ((term165 p) = (term180 d p)).
Proof. exact (TRANS (@lem1346782 d p) (@lem1346787 d p)). Qed.
Lemma lem1346789 (p : prod hreal hreal) (d : hreal) (h1 : (@fst hreal hreal p) = (term176 p d)) : (term165 p) = (term180 d p).
Proof. exact (EQ_MP (@lem1346788 d p) (@lem1346779 p d h1)). Qed.
Lemma lem1346790 (p : prod hreal hreal) (d : hreal) (h1 : (@fst hreal hreal p) = (term176 p d)) : (term180 d p) = (term165 p).
Proof. exact (SYM (@lem1346789 p d h1)). Qed.
Lemma lem1346791 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1346795 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term65 A B f g).
Proof. exact (EQ_MP (@lem1346326 A B f g) (@lem1346325 A B f g)). Qed.
Lemma lem1346796 (f : type1233) (g : type1233) : (f = g) = (term183 f g).
Proof. exact (@lem1346795 (prod hreal hreal) Prop f g). Qed.
Lemma lem1346797 (p : prod hreal hreal) (d : hreal) : ((term184 d p) = (term185 d)) = (term186 p d).
Proof. exact (@lem1346796 (term184 d p) (term185 d)). Qed.
Lemma lem1346798 (p : prod hreal hreal) (d : hreal) : (term186 p d) = ((term184 d p) = (term185 d)).
Proof. exact (SYM (@lem1346797 p d)). Qed.
Lemma lem1346799 (p : prod hreal hreal) (d : hreal) : (term187 p d) = (term187 p d).
Proof. exact (eq_refl (term187 p d)). Qed.
Lemma lem1346800 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term188 p d q) = (term189 p d q).
Proof. exact (MK_COMB (@lem1346799 p d) (@lem1346321 q)). Qed.
Lemma lem1346801 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term189 p d q) = ((term190 d p q) = (term191 d q)).
Proof. exact (eq_refl (term189 p d q)). Qed.
Lemma lem1346802 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term192 p d q) = (term192 p d q).
Proof. exact (eq_refl (term192 p d q)). Qed.
Lemma lem1346803 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term188 p d q) = (term189 p d q)) = ((term188 p d q) = ((term190 d p q) = (term191 d q))).
Proof. exact (MK_COMB (@lem1346802 p d q) (@lem1346801 p d q)). Qed.
Lemma lem1346804 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term188 p d q) = ((term193 d p q) = (term194 d q)).
Proof. exact (eq_refl (term188 p d q)). Qed.
Lemma lem1346805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346806 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term192 p d q) = (term195 p d q).
Proof. exact (MK_COMB (@lem1346805) (@lem1346804 p d q)). Qed.
Lemma lem1346807 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term190 d p q) = (term191 d q)) = ((term190 d p q) = (term191 d q)).
Proof. exact (eq_refl ((term190 d p q) = (term191 d q))). Qed.
Lemma lem1346808 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term188 p d q) = ((term190 d p q) = (term191 d q))) = (((term193 d p q) = (term194 d q)) = ((term190 d p q) = (term191 d q))).
Proof. exact (MK_COMB (@lem1346806 p d q) (@lem1346807 p d q)). Qed.
Lemma lem1346809 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term188 p d q) = (term189 p d q)) = (((term193 d p q) = (term194 d q)) = ((term190 d p q) = (term191 d q))).
Proof. exact (TRANS (@lem1346803 p d q) (@lem1346808 p d q)). Qed.
Lemma lem1346810 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term193 d p q) = (term194 d q)) = ((term190 d p q) = (term191 d q)).
Proof. exact (EQ_MP (@lem1346809 p d q) (@lem1346800 p d q)). Qed.
Lemma lem1346811 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term190 d p q) = (term191 d q)) = ((term193 d p q) = (term194 d q)).
Proof. exact (SYM (@lem1346810 p d q)). Qed.
Lemma lem1346813 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term58 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1346310 x1 y2 x2 y1) (@lem1346309 x1 y2 x2 y1)). Qed.
Lemma lem1346814 (d : hreal) (q : prod hreal hreal) (p : prod hreal hreal) : (term190 d p q) = ((term196 p d q) = (term197 q p)).
Proof. exact (@lem1346813 (term176 p d) (@snd hreal hreal q) (@fst hreal hreal q) (@snd hreal hreal p)). Qed.
Lemma lem1346815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346816 (d : hreal) (q : prod hreal hreal) (p : prod hreal hreal) : (term198 d p q) = (term199 d q p).
Proof. exact (MK_COMB (@lem1346815) (@lem1346814 d q p)). Qed.
Lemma lem1346818 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term58 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1346310 x1 y2 x2 y1) (@lem1346309 x1 y2 x2 y1)). Qed.
Lemma lem1346819 (d : hreal) (q : prod hreal hreal) : (term191 d q) = ((term200 d q) = (term170 q)).
Proof. exact (@lem1346818 d (@snd hreal hreal q) (@fst hreal hreal q) term111). Qed.
Lemma lem1346820 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term190 d p q) = (term191 d q)) = (((term196 p d q) = (term197 q p)) = ((term200 d q) = (term170 q))).
Proof. exact (MK_COMB (@lem1346816 d q p) (@lem1346819 d q)). Qed.
Lemma lem1346821 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (((term196 p d q) = (term197 q p)) = ((term200 d q) = (term170 q))) = ((term190 d p q) = (term191 d q)).
Proof. exact (SYM (@lem1346820 p d q)). Qed.
Lemma lem1346823 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1346298 y x) (@lem1346297 x y)). Qed.
Lemma lem1346824 (p : prod hreal hreal) (q : prod hreal hreal) : (term197 q p) = (term201 p q).
Proof. exact (@lem1346823 (@snd hreal hreal p) (@fst hreal hreal q)). Qed.
Lemma lem1346825 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term202 p d q) = (term202 p d q).
Proof. exact (eq_refl (term202 p d q)). Qed.
Lemma lem1346826 (d : hreal) (p : prod hreal hreal) (q : prod hreal hreal) : ((term196 p d q) = (term197 q p)) = ((term196 p d q) = (term201 p q)).
Proof. exact (MK_COMB (@lem1346825 p d q) (@lem1346824 p q)). Qed.
Lemma lem1346827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346828 (d : hreal) (p : prod hreal hreal) (q : prod hreal hreal) : (term199 d q p) = (term203 d p q).
Proof. exact (MK_COMB (@lem1346827) (@lem1346826 d p q)). Qed.
Lemma lem1346829 (d : hreal) (q : prod hreal hreal) : ((term200 d q) = (term170 q)) = ((term200 d q) = (term170 q)).
Proof. exact (eq_refl ((term200 d q) = (term170 q))). Qed.
Lemma lem1346830 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (((term196 p d q) = (term197 q p)) = ((term200 d q) = (term170 q))) = (((term196 p d q) = (term201 p q)) = ((term200 d q) = (term170 q))).
Proof. exact (MK_COMB (@lem1346828 d p q) (@lem1346829 d q)). Qed.
Lemma lem1346831 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (((term196 p d q) = (term201 p q)) = ((term200 d q) = (term170 q))) = (((term196 p d q) = (term197 q p)) = ((term200 d q) = (term170 q))).
Proof. exact (SYM (@lem1346830 p d q)). Qed.
Lemma lem1346839 (x : hreal) (y : hreal) (z : hreal) : (term27 x y z) = (term26 x y z).
Proof. exact (EQ_MP (@lem1346292 x y z) (@lem1346291 x y z)). Qed.
Lemma lem1346840 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term196 p d q) = (term204 p d q).
Proof. exact (@lem1346839 (@snd hreal hreal p) d (@snd hreal hreal q)). Qed.
Lemma lem1346841 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1346842 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term202 p d q) = (term205 p d q).
Proof. exact (MK_COMB (@lem1346841) (@lem1346840 p d q)). Qed.
Lemma lem1346843 (p : prod hreal hreal) (q : prod hreal hreal) : (term201 p q) = (term201 p q).
Proof. exact (eq_refl (term201 p q)). Qed.
Lemma lem1346844 (d : hreal) (p : prod hreal hreal) (q : prod hreal hreal) : ((term196 p d q) = (term201 p q)) = ((term204 p d q) = (term201 p q)).
Proof. exact (MK_COMB (@lem1346842 p d q) (@lem1346843 p q)). Qed.
Lemma lem1346846 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1346283 m n p) (@lem1346282 m n p)). Qed.
Lemma lem1346847 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term204 p d q) = (term201 p q)) = ((term200 d q) = (@fst hreal hreal q)).
Proof. exact (@lem1346846 (@snd hreal hreal p) (term200 d q) (@fst hreal hreal q)). Qed.
Lemma lem1346850 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term196 p d q) = (term201 p q)) = ((term200 d q) = (@fst hreal hreal q)).
Proof. exact (TRANS (@lem1346844 d p q) (@lem1346847 p d q)). Qed.
Lemma lem1346851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346852 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term203 d p q) = (term206 d q).
Proof. exact (MK_COMB (@lem1346851) (@lem1346850 p d q)). Qed.
Lemma lem1346857 (d : hreal) (q : prod hreal hreal) : ((term200 d q) = (term170 q)) = ((term200 d q) = (term170 q)).
Proof. exact (eq_refl ((term200 d q) = (term170 q))). Qed.
Lemma lem1346858 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (((term196 p d q) = (term201 p q)) = ((term200 d q) = (term170 q))) = (((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (term170 q))).
Proof. exact (MK_COMB (@lem1346852 p d q) (@lem1346857 d q)). Qed.
Lemma lem1346861 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (term170 q))) = (((term196 p d q) = (term201 p q)) = ((term200 d q) = (term170 q))).
Proof. exact (SYM (@lem1346858 p d q)). Qed.
Lemma lem1346869 (n : hreal) : (term11 n) = n.
Proof. exact (EQ_MP (@lem1346256 n) (@lem1346255 n)). Qed.
Lemma lem1346870 (q : prod hreal hreal) : (term170 q) = (@fst hreal hreal q).
Proof. exact (@lem1346869 (@fst hreal hreal q)). Qed.
Lemma lem1346871 (d : hreal) (q : prod hreal hreal) : (term207 d q) = (term207 d q).
Proof. exact (eq_refl (term207 d q)). Qed.
Lemma lem1346872 (d : hreal) (q : prod hreal hreal) : ((term200 d q) = (term170 q)) = ((term200 d q) = (@fst hreal hreal q)).
Proof. exact (MK_COMB (@lem1346871 d q) (@lem1346870 q)). Qed.
Lemma lem1346875 (d : hreal) (q : prod hreal hreal) : (term206 d q) = (term206 d q).
Proof. exact (eq_refl (term206 d q)). Qed.
Lemma lem1346876 (d : hreal) (q : prod hreal hreal) : (((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (term170 q))) = (((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (@fst hreal hreal q))).
Proof. exact (MK_COMB (@lem1346875 d q) (@lem1346872 d q)). Qed.
Lemma lem1346878 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1346879 (x : Prop) : (x = x) = True.
Proof. exact (@lem1346878 Prop x). Qed.
Lemma lem1346880 (d : hreal) (q : prod hreal hreal) : (((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (@fst hreal hreal q))) = True.
Proof. exact (@lem1346879 ((term200 d q) = (@fst hreal hreal q))). Qed.
Lemma lem1346881 (d : hreal) (q : prod hreal hreal) : (((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (term170 q))) = True.
Proof. exact (TRANS (@lem1346876 d q) (@lem1346880 d q)). Qed.
Lemma lem1346882 (d : hreal) (q : prod hreal hreal) : True = (((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (term170 q))).
Proof. exact (SYM (@lem1346881 d q)). Qed.
Lemma lem1346883 (d : hreal) (q : prod hreal hreal) : ((term200 d q) = (@fst hreal hreal q)) = ((term200 d q) = (term170 q)).
Proof. exact (EQ_MP (@lem1346882 d q) (@lem0)). Qed.
Lemma lem1346884 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term196 p d q) = (term201 p q)) = ((term200 d q) = (term170 q)).
Proof. exact (EQ_MP (@lem1346861 p d q) (@lem1346883 d q)). Qed.
Lemma lem1346885 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : ((term196 p d q) = (term197 q p)) = ((term200 d q) = (term170 q)).
Proof. exact (EQ_MP (@lem1346831 p d q) (@lem1346884 p d q)). Qed.
Lemma lem1346886 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term190 d p q) = (term191 d q).
Proof. exact (EQ_MP (@lem1346821 p d q) (@lem1346885 p d q)). Qed.
Lemma lem1346887 (p : prod hreal hreal) (d : hreal) (q : prod hreal hreal) : (term193 d p q) = (term194 d q).
Proof. exact (EQ_MP (@lem1346811 p d q) (@lem1346886 p d q)). Qed.
Lemma lem1346892 (p : prod hreal hreal) (d : hreal) : term186 p d.
Proof. exact (fun q : prod hreal hreal => @lem1346887 p d q). Qed.
Lemma lem1346893 (p : prod hreal hreal) (d : hreal) : (term184 d p) = (term185 d).
Proof. exact (EQ_MP (@lem1346798 p d) (@lem1346892 p d)). Qed.
Lemma lem1346894 (p : prod hreal hreal) (d : hreal) : (term208 d p) = (term77 d).
Proof. exact (MK_COMB (@lem1346791) (@lem1346893 p d)). Qed.
Lemma lem1346895 (d : hreal) (p : prod hreal hreal) : term180 d p.
Proof. exact (ex_intro (term209 d p) d (@lem1346894 p d)). Qed.
Lemma lem1346896 (p : prod hreal hreal) (d : hreal) (h1 : (@fst hreal hreal p) = (term176 p d)) : term165 p.
Proof. exact (EQ_MP (@lem1346790 p d h1) (@lem1346895 d p)). Qed.
Lemma lem1346897 (p : prod hreal hreal) (h1 : term171 p) : term165 p.
Proof. exact (ex_elim (@lem1346776 p h1) (fun d : hreal => fun h0 : term210 p d => @lem1346896 p d h0)). Qed.
Lemma lem1346898 (p : prod hreal hreal) : term173 p.
Proof. exact (fun h0 : term171 p => @lem1346897 p h0). Qed.
Lemma lem1346899 (p : prod hreal hreal) : term166 p.
Proof. exact (EQ_MP (@lem1346771 p) (@lem1346898 p)). Qed.
Lemma lem1346900 (p : prod hreal hreal) : term154 p.
Proof. exact (EQ_MP (@lem1346757 p) (@lem1346899 p)). Qed.
Lemma lem1346901 (p : prod hreal hreal) : term150 p.
Proof. exact (EQ_MP (@lem1346741 p) (@lem1346900 p)). Qed.
Lemma lem1346902 (p : prod hreal hreal) : term136 p.
Proof. exact (EQ_MP (@lem1346728 p) (@lem1346901 p)). Qed.
Lemma lem1346903 (x : real) (p : prod hreal hreal) (h1 : x = (term127 p)) : term124 x.
Proof. exact (EQ_MP (@lem1346702 x p h1) (@lem1346902 p)). Qed.
Lemma lem1346904 (p : prod hreal hreal) (x : real) : term132 p x.
Proof. exact (fun h0 : x = (term127 p) => @lem1346903 x p h0). Qed.
Lemma lem1346905 (p : prod hreal hreal) (x : real) : term131 p x.
Proof. exact (EQ_MP (@lem1346688 p x) (@lem1346904 p x)). Qed.
Lemma lem1346906 (x : real) (p : prod hreal hreal) (h1 : (dest_real x) = (treal_eq p)) : term124 x.
Proof. exact (@lem1346905 p x (@lem1346656 x p h1)). Qed.
Lemma lem1346907 (p : prod hreal hreal) (x : real) : term211 p x.
Proof. exact (fun h0 : (dest_real x) = (treal_eq p) => @lem1346906 x p h0). Qed.
Lemma lem1346908 (x : real) (p : prod hreal hreal) (h1 : (dest_real x) = (treal_eq p)) : term124 x.
Proof. exact (@lem1346907 p x (@lem1346654 x p h1)). Qed.
Lemma lem1346909 (x : real) (h1 : term70 x) : term124 x.
Proof. exact (ex_elim (@lem1346653 x h1) (fun p : prod hreal hreal => fun h0 : term212 x p => @lem1346908 x p h0)). Qed.
Lemma lem1346910 (x : real) : term126 x.
Proof. exact (fun h0 : term70 x => @lem1346909 x h0). Qed.
Lemma lem1346911 (x : real) : term125 x.
Proof. exact (EQ_MP (@lem1346652 x) (@lem1346910 x)). Qed.
Lemma lem1346912 (x : real) : term124 x.
Proof. exact (@lem1346911 x (@lem1346378 x)). Qed.
Lemma lem1346913 (x : real) (h1 : term84 x) : term84 x.
Proof. exact (h1). Qed.
Lemma lem1346914 (x : real) (y : hreal) (h1 : x = (term77 y)) : x = (term77 y).
Proof. exact (h1). Qed.
Lemma lem1346915 : term213 = term213.
Proof. exact (eq_refl term213). Qed.
Lemma lem1346916 (x : real) (y : hreal) (h1 : x = (term77 y)) : (term214 x) = (term215 y).
Proof. exact (MK_COMB (@lem1346915) (@lem1346914 x y h1)). Qed.
Lemma lem1346917 (y : hreal) : (term215 y) = (term216 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1346918 (x : real) : (term217 x) = (term217 x).
Proof. exact (eq_refl (term217 x)). Qed.
Lemma lem1346919 (x : real) (y : hreal) : ((term214 x) = (term215 y)) = ((term214 x) = (term216 y)).
Proof. exact (MK_COMB (@lem1346918 x) (@lem1346917 y)). Qed.
Lemma lem1346920 (x : real) : (term214 x) = (term86 x).
Proof. exact (eq_refl (term214 x)). Qed.
Lemma lem1346921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1346922 (x : real) : (term217 x) = (term85 x).
Proof. exact (MK_COMB (@lem1346921) (@lem1346920 x)). Qed.
Lemma lem1346923 (y : hreal) : (term216 y) = (term216 y).
Proof. exact (eq_refl (term216 y)). Qed.
Lemma lem1346924 (x : real) (y : hreal) : ((term214 x) = (term216 y)) = ((term86 x) = (term216 y)).
Proof. exact (MK_COMB (@lem1346922 x) (@lem1346923 y)). Qed.
Lemma lem1346925 (x : real) (y : hreal) : ((term214 x) = (term215 y)) = ((term86 x) = (term216 y)).
Proof. exact (TRANS (@lem1346919 x y) (@lem1346924 x y)). Qed.
Lemma lem1346926 (x : real) (y : hreal) (h1 : x = (term77 y)) : (term86 x) = (term216 y).
Proof. exact (EQ_MP (@lem1346925 x y) (@lem1346916 x y h1)). Qed.
Lemma lem1346927 (x : real) (y : hreal) (h1 : x = (term77 y)) : (term216 y) = (term86 x).
Proof. exact (SYM (@lem1346926 x y h1)). Qed.
Lemma lem1346929 (m : nat) : (real_of_num m) = (term25 m).
Proof. exact (EQ_MP (@lem1346253 m) (@lem1337537 m)). Qed.
Lemma lem1346930 : term139 = term140.
Proof. exact (@lem1346929 (NUMERAL 0)). Qed.
Lemma lem1346931 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1346932 : term141 = term142.
Proof. exact (MK_COMB (@lem1346931) (@lem1346930)). Qed.
Lemma lem1346933 (y : hreal) : (term77 y) = (term77 y).
Proof. exact (eq_refl (term77 y)). Qed.
Lemma lem1346934 (y : hreal) : (term216 y) = (term218 y).
Proof. exact (MK_COMB (@lem1346932) (@lem1346933 y)). Qed.
Lemma lem1346936 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term24 x1 y1) = (treal_le x1 y1).
Proof. exact (EQ_MP (@lem1346247 x1 y1) (@lem1337991 x1 y1)). Qed.
Lemma lem1346937 (y : hreal) : (term218 y) = (term219 y).
Proof. exact (@lem1346936 term146 (term98 y)). Qed.
Lemma lem1346938 (y : hreal) : (term216 y) = (term219 y).
Proof. exact (TRANS (@lem1346934 y) (@lem1346937 y)). Qed.
Lemma lem1346939 (y : hreal) : (term219 y) = (term216 y).
Proof. exact (SYM (@lem1346938 y)). Qed.
Lemma lem1346941 (n : nat) : (treal_of_num n) = (term23 n).
Proof. exact (EQ_MP (@lem1346241 n) (@lem1346240 n)). Qed.
Lemma lem1346942 : term146 = term157.
Proof. exact (@lem1346941 (NUMERAL 0)). Qed.
Lemma lem1346943 : treal_le = treal_le.
Proof. exact (eq_refl treal_le). Qed.
Lemma lem1346944 : term158 = term159.
Proof. exact (MK_COMB (@lem1346943) (@lem1346942)). Qed.
Lemma lem1346945 (y : hreal) : (term98 y) = (term98 y).
Proof. exact (eq_refl (term98 y)). Qed.
Lemma lem1346946 (y : hreal) : (term219 y) = (term220 y).
Proof. exact (MK_COMB (@lem1346944) (@lem1346945 y)). Qed.
Lemma lem1346948 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term20 x1 y1 x2 y2) = (term21 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1346238 x1 y2 x2 y1) (@lem1346237 x1 y2 x2 y1)). Qed.
Lemma lem1346949 (y : hreal) : (term220 y) = (term221 y).
Proof. exact (@lem1346948 term111 term111 y term111). Qed.
Lemma lem1346950 (y : hreal) : (term219 y) = (term221 y).
Proof. exact (TRANS (@lem1346946 y) (@lem1346949 y)). Qed.
Lemma lem1346951 (y : hreal) : (term221 y) = (term219 y).
Proof. exact (SYM (@lem1346950 y)). Qed.
Lemma lem1346953 (x : hreal) : (term4 x) = x.
Proof. exact (EQ_MP (@lem1346226 x) (@lem1346225 x)). Qed.
Lemma lem1346954 : term222 = term111.
Proof. exact (@lem1346953 term111). Qed.
Lemma lem1346955 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1346956 : term223 = term224.
Proof. exact (MK_COMB (@lem1346955) (@lem1346954)). Qed.
Lemma lem1346958 (n : hreal) : (term11 n) = n.
Proof. exact (EQ_MP (@lem1346223 n) (@lem1346222 n)). Qed.
Lemma lem1346959 (y : hreal) : (term11 y) = y.
Proof. exact (@lem1346958 y). Qed.
Lemma lem1346960 (y : hreal) : (term221 y) = (term225 y).
Proof. exact (MK_COMB (@lem1346956) (@lem1346959 y)). Qed.
Lemma lem1346961 (y : hreal) : (term225 y) = (term221 y).
Proof. exact (SYM (@lem1346960 y)). Qed.
Lemma lem1346963 (x : hreal) : x = (term4 x).
Proof. exact (EQ_MP (@lem1346220 x) (@lem1346219 x)). Qed.
Lemma lem1346964 (y : hreal) : y = (term4 y).
Proof. exact (@lem1346963 y). Qed.
Lemma lem1346965 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem1346966 (y : hreal) : (term225 y) = (term226 y).
Proof. exact (MK_COMB (@lem1346965) (@lem1346964 y)). Qed.
Lemma lem1346967 (y : hreal) : (term226 y) = (term225 y).
Proof. exact (SYM (@lem1346966 y)). Qed.
Lemma lem1346969 (x : hreal) (y : hreal) : (term3 x y) = True.
Proof. exact (EQ_MP (@lem1346207 x y) (@lem1346206 x y)). Qed.
Lemma lem1346970 (y : hreal) : (term226 y) = True.
Proof. exact (@lem1346969 term111 y). Qed.
Lemma lem1346971 (y : hreal) : True = (term226 y).
Proof. exact (SYM (@lem1346970 y)). Qed.
Lemma lem1346972 (y : hreal) : term226 y.
Proof. exact (EQ_MP (@lem1346971 y) (@lem0)). Qed.
Lemma lem1346973 (y : hreal) : term225 y.
Proof. exact (EQ_MP (@lem1346967 y) (@lem1346972 y)). Qed.
Lemma lem1346974 (y : hreal) : term221 y.
Proof. exact (EQ_MP (@lem1346961 y) (@lem1346973 y)). Qed.
Lemma lem1346975 (y : hreal) : term219 y.
Proof. exact (EQ_MP (@lem1346951 y) (@lem1346974 y)). Qed.
Lemma lem1346976 (y : hreal) : term216 y.
Proof. exact (EQ_MP (@lem1346939 y) (@lem1346975 y)). Qed.
Lemma lem1346977 (x : real) (y : hreal) (h1 : x = (term77 y)) : term86 x.
Proof. exact (EQ_MP (@lem1346927 x y h1) (@lem1346976 y)). Qed.
Lemma lem1346978 (x : real) (h1 : term84 x) : term86 x.
Proof. exact (ex_elim (@lem1346913 x h1) (fun y : hreal => fun h0 : term82 x y => @lem1346977 x y h0)). Qed.
Lemma lem1346979 (x : real) : term227 x.
Proof. exact (fun h0 : term84 x => @lem1346978 x h0). Qed.
Lemma lem1346980 (x : real) : term228 x.
Proof. exact (conj (@lem1346912 x) (@lem1346979 x)). Qed.
Lemma lem1346981 (x : real) : (term228 x) = ((term86 x) = (term84 x)).
Proof. exact (@lem32 (term86 x) (term84 x)). Qed.
Lemma lem1346982 (x : real) : (term86 x) = (term84 x).
Proof. exact (EQ_MP (@lem1346981 x) (@lem1346980 x)). Qed.
Lemma lem1346987 : term90.
Proof. exact (fun x : real => @lem1346982 x). Qed.
Lemma lem1346988 : term109.
Proof. exact (EQ_MP (@lem1346597) (@lem1346987)). Qed.
Lemma lem1346989 : term108.
Proof. exact (EQ_MP (@lem1346518) (@lem1346988)). Qed.
Lemma lem1346990 : term229.
Proof. exact (ex_intro term230 term76 (@lem1346989)). Qed.
