Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm521920_term_abbrevs.
Require Import ARITH_LE_spec.
Require Import LE_ANTISYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem521128 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (term0 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem521129 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (m = n) = (term0 n m).
Proof. exact (SYM (@lem521128 m n h1)). Qed.
Lemma lem521130 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (m = n) = (term0 n m).
Proof. exact (h1). Qed.
Lemma lem521131 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (term0 n m) = (m = n).
Proof. exact (SYM (@lem521130 n m h1)). Qed.
Lemma lem521132 (n : nat) (m : nat) : ((term0 n m) = (m = n)) = ((m = n) = (term0 n m)).
Proof. exact (prop_ext (fun h1 : (term0 n m) = (m = n) => @lem521129 m n h1) (fun h1 : (m = n) = (term0 n m) => @lem521131 n m h1)). Qed.
Lemma lem521133 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem521132 n m)). Qed.
Lemma lem521134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521135 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem521134) (@lem521133 m)). Qed.
Lemma lem521136 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem521135 m)). Qed.
Lemma lem521137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521138 : term7 = term8.
Proof. exact (MK_COMB (@lem521137) (@lem521136)). Qed.
Lemma lem521139 : term8.
Proof. exact (EQ_MP (@lem521138) (@lem92426)). Qed.
Lemma lem521140 : term9.
Proof. exact (proj2 (@lem519780)). Qed.
Lemma lem521141 : term10.
Proof. exact (proj2 (@lem521140)). Qed.
Lemma lem521142 : term11.
Proof. exact (proj2 (@lem521141)). Qed.
Lemma lem521143 : term12.
Proof. exact (proj2 (@lem521142)). Qed.
Lemma lem521144 : term13.
Proof. exact (proj2 (@lem521143)). Qed.
Lemma lem521145 : term14.
Proof. exact (proj2 (@lem521144)). Qed.
Lemma lem521146 : term15.
Proof. exact (proj2 (@lem521145)). Qed.
Lemma lem521147 : term16.
Proof. exact (proj2 (@lem521146)). Qed.
Lemma lem521148 : term17.
Proof. exact (proj2 (@lem521147)). Qed.
Lemma lem521149 (m : nat) : term18 m.
Proof. exact (@lem521148 m). Qed.
Lemma lem521150 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem521151 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem521150 m) (@lem521149 m)). Qed.
Lemma lem521152 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem521151 m n). Qed.
Lemma lem521153 (m : nat) (n : nat) : (term20 m n) = ((term21 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem521155 : term22.
Proof. exact (proj1 (@lem521147)). Qed.
Lemma lem521156 (m : nat) : term23 m.
Proof. exact (@lem521155 m). Qed.
Lemma lem521157 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem521158 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem521157 m) (@lem521156 m)). Qed.
Lemma lem521159 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem521158 m n). Qed.
Lemma lem521160 (m : nat) (n : nat) : (term25 m n) = ((term26 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem521162 : term27.
Proof. exact (proj1 (@lem521146)). Qed.
Lemma lem521163 (m : nat) : term28 m.
Proof. exact (@lem521162 m). Qed.
Lemma lem521164 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem521165 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem521164 m) (@lem521163 m)). Qed.
Lemma lem521166 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem521165 m n). Qed.
Lemma lem521167 (m : nat) (n : nat) : (term30 m n) = ((term31 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem521169 : term32.
Proof. exact (proj1 (@lem521145)). Qed.
Lemma lem521170 (m : nat) : term33 m.
Proof. exact (@lem521169 m). Qed.
Lemma lem521171 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem521172 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem521171 m) (@lem521170 m)). Qed.
Lemma lem521173 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem521172 m n). Qed.
Lemma lem521174 (m : nat) (n : nat) : (term35 m n) = ((term36 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem521176 : term37.
Proof. exact (proj1 (@lem521144)). Qed.
Lemma lem521177 (n : nat) : term38 n.
Proof. exact (@lem521176 n). Qed.
Lemma lem521178 (n : nat) : (term38 n) = ((term39 n) = True).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem521180 : term40.
Proof. exact (proj1 (@lem521143)). Qed.
Lemma lem521181 (n : nat) : term41 n.
Proof. exact (@lem521180 n). Qed.
Lemma lem521182 (n : nat) : (term41 n) = ((term42 n) = True).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem521184 : term43.
Proof. exact (proj1 (@lem521142)). Qed.
Lemma lem521185 (n : nat) : term44 n.
Proof. exact (@lem521184 n). Qed.
Lemma lem521186 (n : nat) : (term44 n) = ((term45 n) = False).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem521188 : term46.
Proof. exact (proj1 (@lem521141)). Qed.
Lemma lem521189 (n : nat) : term47 n.
Proof. exact (@lem521188 n). Qed.
Lemma lem521190 (n : nat) : (term47 n) = ((term48 n) = (Peano.le n 0)).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem521193 : term49.
Proof. exact (proj1 (@lem519780)). Qed.
Lemma lem521194 (m : nat) : term50 m.
Proof. exact (@lem521193 m). Qed.
Lemma lem521195 (m : nat) : (term50 m) = (term51 m).
Proof. exact (eq_refl (term50 m)). Qed.
Lemma lem521196 (m : nat) : term51 m.
Proof. exact (EQ_MP (@lem521195 m) (@lem521194 m)). Qed.
Lemma lem521197 (m : nat) (n : nat) : term52 m n.
Proof. exact (@lem521196 m n). Qed.
Lemma lem521198 (m : nat) (n : nat) : (term52 m n) = ((term53 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem521200 (m : nat) : term54 m.
Proof. exact (@lem521139 m). Qed.
Lemma lem521201 (m : nat) : (term54 m) = (term4 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem521202 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem521201 m) (@lem521200 m)). Qed.
Lemma lem521203 (m : nat) (n : nat) : term55 m n.
Proof. exact (@lem521202 m n). Qed.
Lemma lem521204 (n : nat) (m : nat) : (term55 m n) = ((m = n) = (term0 n m)).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem521226 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521227 (n : nat) (m : nat) : ((NUMERAL m) = (NUMERAL n)) = (term56 n m).
Proof. exact (@lem521226 (NUMERAL n) (NUMERAL m)). Qed.
Lemma lem521231 (m : nat) (n : nat) : (term53 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521198 m n) (@lem521197 m n)). Qed.
Lemma lem521232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521233 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem521232) (@lem521231 m n)). Qed.
Lemma lem521235 (m : nat) (n : nat) : (term53 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521198 m n) (@lem521197 m n)). Qed.
Lemma lem521236 (n : nat) (m : nat) : (term53 n m) = (Peano.le n m).
Proof. exact (@lem521235 n m). Qed.
Lemma lem521237 (n : nat) (m : nat) : (term56 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem521233 m n) (@lem521236 n m)). Qed.
Lemma lem521240 (n : nat) (m : nat) : ((NUMERAL m) = (NUMERAL n)) = (term0 n m).
Proof. exact (TRANS (@lem521227 n m) (@lem521237 n m)). Qed.
Lemma lem521241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem521242 (n : nat) (m : nat) : (term59 m n) = (term60 n m).
Proof. exact (MK_COMB (@lem521241) (@lem521240 n m)). Qed.
Lemma lem521246 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521249 (n : nat) (m : nat) : (((NUMERAL m) = (NUMERAL n)) = (m = n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem521242 n m) (@lem521246 n m)). Qed.
Lemma lem521251 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem521252 (x : Prop) : (x = x) = True.
Proof. exact (@lem521251 Prop x). Qed.
Lemma lem521253 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem521252 (term0 n m)). Qed.
Lemma lem521254 (m : nat) (n : nat) : (((NUMERAL m) = (NUMERAL n)) = (m = n)) = True.
Proof. exact (TRANS (@lem521249 n m) (@lem521253 n m)). Qed.
Lemma lem521255 (m : nat) : (term61 m) = term62.
Proof. exact (fun_ext (fun n : nat => @lem521254 m n)). Qed.
Lemma lem521256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521257 (m : nat) : (term63 m) = term64.
Proof. exact (MK_COMB (@lem521256) (@lem521255 m)). Qed.
Lemma lem521259 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521260 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521259 nat t). Qed.
Lemma lem521261 : term64 = True.
Proof. exact (@lem521260 True). Qed.
Lemma lem521262 (m : nat) : (term63 m) = True.
Proof. exact (TRANS (@lem521257 m) (@lem521261)). Qed.
Lemma lem521263 : term67 = term62.
Proof. exact (fun_ext (fun m : nat => @lem521262 m)). Qed.
Lemma lem521264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521265 : term68 = term64.
Proof. exact (MK_COMB (@lem521264) (@lem521263)). Qed.
Lemma lem521267 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521268 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521267 nat t). Qed.
Lemma lem521269 : term64 = True.
Proof. exact (@lem521268 True). Qed.
Lemma lem521270 : term68 = True.
Proof. exact (TRANS (@lem521265) (@lem521269)). Qed.
Lemma lem521271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521272 : term69 = (and True).
Proof. exact (MK_COMB (@lem521271) (@lem521270)). Qed.
Lemma lem521276 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem521277 : ((0 = 0) = True) = (0 = 0).
Proof. exact (@lem521276 (0 = 0)). Qed.
Lemma lem521279 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem521280 (x : nat) : (x = x) = True.
Proof. exact (@lem521279 nat x). Qed.
Lemma lem521281 : (0 = 0) = True.
Proof. exact (@lem521280 0). Qed.
Lemma lem521282 : ((0 = 0) = True) = True.
Proof. exact (TRANS (@lem521277) (@lem521281)). Qed.
Lemma lem521283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521284 : term70 = (and True).
Proof. exact (MK_COMB (@lem521283) (@lem521282)). Qed.
Lemma lem521298 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521299 (n : nat) : ((BIT0 n) = 0) = (term71 n).
Proof. exact (@lem521298 0 (BIT0 n)). Qed.
Lemma lem521303 (n : nat) : (term48 n) = (Peano.le n 0).
Proof. exact (EQ_MP (@lem521190 n) (@lem521189 n)). Qed.
Lemma lem521304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521305 (n : nat) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem521304) (@lem521303 n)). Qed.
Lemma lem521307 (n : nat) : (term42 n) = True.
Proof. exact (EQ_MP (@lem521182 n) (@lem521181 n)). Qed.
Lemma lem521308 (n : nat) : (term71 n) = (term74 n).
Proof. exact (MK_COMB (@lem521305 n) (@lem521307 n)). Qed.
Lemma lem521310 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem521311 (n : nat) : (term74 n) = (Peano.le n 0).
Proof. exact (@lem521310 (Peano.le n 0)). Qed.
Lemma lem521312 (n : nat) : (term71 n) = (Peano.le n 0).
Proof. exact (TRANS (@lem521308 n) (@lem521311 n)). Qed.
Lemma lem521313 (n : nat) : ((BIT0 n) = 0) = (Peano.le n 0).
Proof. exact (TRANS (@lem521299 n) (@lem521312 n)). Qed.
Lemma lem521314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem521315 (n : nat) : (term75 n) = (term76 n).
Proof. exact (MK_COMB (@lem521314) (@lem521313 n)). Qed.
Lemma lem521319 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521320 (n : nat) : (n = 0) = (term77 n).
Proof. exact (@lem521319 0 n). Qed.
Lemma lem521323 (n : nat) : (((BIT0 n) = 0) = (n = 0)) = ((Peano.le n 0) = (term77 n)).
Proof. exact (MK_COMB (@lem521315 n) (@lem521320 n)). Qed.
Lemma lem521328 : term78 = term79.
Proof. exact (fun_ext (fun n : nat => @lem521323 n)). Qed.
Lemma lem521329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521330 : term80 = term81.
Proof. exact (MK_COMB (@lem521329) (@lem521328)). Qed.
Lemma lem521335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521336 : term82 = term83.
Proof. exact (MK_COMB (@lem521335) (@lem521330)). Qed.
Lemma lem521344 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem521345 (n : nat) : (((BIT1 n) = 0) = False) = (term84 n).
Proof. exact (@lem521344 ((BIT1 n) = 0)). Qed.
Lemma lem521349 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521350 (n : nat) : ((BIT1 n) = 0) = (term85 n).
Proof. exact (@lem521349 0 (BIT1 n)). Qed.
Lemma lem521354 (n : nat) : (term45 n) = False.
Proof. exact (EQ_MP (@lem521186 n) (@lem521185 n)). Qed.
Lemma lem521355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521356 (n : nat) : (term86 n) = (and False).
Proof. exact (MK_COMB (@lem521355) (@lem521354 n)). Qed.
Lemma lem521358 (n : nat) : (term39 n) = True.
Proof. exact (EQ_MP (@lem521178 n) (@lem521177 n)). Qed.
Lemma lem521359 (n : nat) : (term85 n) = (False /\ True).
Proof. exact (MK_COMB (@lem521356 n) (@lem521358 n)). Qed.
Lemma lem521361 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem521362 : (False /\ True) = False.
Proof. exact (@lem521361 True). Qed.
Lemma lem521363 (n : nat) : (term85 n) = False.
Proof. exact (TRANS (@lem521359 n) (@lem521362)). Qed.
Lemma lem521364 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (TRANS (@lem521350 n) (@lem521363 n)). Qed.
Lemma lem521365 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem521366 (n : nat) : (term84 n) = (~ False).
Proof. exact (MK_COMB (@lem521365) (@lem521364 n)). Qed.
Lemma lem521368 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem521369 (n : nat) : (term84 n) = True.
Proof. exact (TRANS (@lem521366 n) (@lem521368)). Qed.
Lemma lem521370 (n : nat) : (((BIT1 n) = 0) = False) = True.
Proof. exact (TRANS (@lem521345 n) (@lem521369 n)). Qed.
Lemma lem521371 : term87 = term62.
Proof. exact (fun_ext (fun n : nat => @lem521370 n)). Qed.
Lemma lem521372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521373 : term88 = term64.
Proof. exact (MK_COMB (@lem521372) (@lem521371)). Qed.
Lemma lem521375 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521376 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521375 nat t). Qed.
Lemma lem521377 : term64 = True.
Proof. exact (@lem521376 True). Qed.
Lemma lem521378 : term88 = True.
Proof. exact (TRANS (@lem521373) (@lem521377)). Qed.
Lemma lem521379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521380 : term89 = (and True).
Proof. exact (MK_COMB (@lem521379) (@lem521378)). Qed.
Lemma lem521394 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521395 (n : nat) : (0 = (BIT0 n)) = (term90 n).
Proof. exact (@lem521394 (BIT0 n) 0). Qed.
Lemma lem521399 (n : nat) : (term42 n) = True.
Proof. exact (EQ_MP (@lem521182 n) (@lem521181 n)). Qed.
Lemma lem521400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521401 (n : nat) : (term91 n) = (and True).
Proof. exact (MK_COMB (@lem521400) (@lem521399 n)). Qed.
Lemma lem521403 (n : nat) : (term48 n) = (Peano.le n 0).
Proof. exact (EQ_MP (@lem521190 n) (@lem521189 n)). Qed.
Lemma lem521404 (n : nat) : (term90 n) = (term92 n).
Proof. exact (MK_COMB (@lem521401 n) (@lem521403 n)). Qed.
Lemma lem521406 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521407 (n : nat) : (term92 n) = (Peano.le n 0).
Proof. exact (@lem521406 (Peano.le n 0)). Qed.
Lemma lem521408 (n : nat) : (term90 n) = (Peano.le n 0).
Proof. exact (TRANS (@lem521404 n) (@lem521407 n)). Qed.
Lemma lem521409 (n : nat) : (0 = (BIT0 n)) = (Peano.le n 0).
Proof. exact (TRANS (@lem521395 n) (@lem521408 n)). Qed.
Lemma lem521410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem521411 (n : nat) : (term93 n) = (term76 n).
Proof. exact (MK_COMB (@lem521410) (@lem521409 n)). Qed.
Lemma lem521415 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521416 (n : nat) : (0 = n) = (term94 n).
Proof. exact (@lem521415 n 0). Qed.
Lemma lem521419 (n : nat) : ((0 = (BIT0 n)) = (0 = n)) = ((Peano.le n 0) = (term94 n)).
Proof. exact (MK_COMB (@lem521411 n) (@lem521416 n)). Qed.
Lemma lem521424 : term95 = term96.
Proof. exact (fun_ext (fun n : nat => @lem521419 n)). Qed.
Lemma lem521425 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521426 : term97 = term98.
Proof. exact (MK_COMB (@lem521425) (@lem521424)). Qed.
Lemma lem521431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521432 : term99 = term100.
Proof. exact (MK_COMB (@lem521431) (@lem521426)). Qed.
Lemma lem521440 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem521441 (n : nat) : ((0 = (BIT1 n)) = False) = (term101 n).
Proof. exact (@lem521440 (0 = (BIT1 n))). Qed.
Lemma lem521445 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521446 (n : nat) : (0 = (BIT1 n)) = (term102 n).
Proof. exact (@lem521445 (BIT1 n) 0). Qed.
Lemma lem521450 (n : nat) : (term39 n) = True.
Proof. exact (EQ_MP (@lem521178 n) (@lem521177 n)). Qed.
Lemma lem521451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521452 (n : nat) : (term103 n) = (and True).
Proof. exact (MK_COMB (@lem521451) (@lem521450 n)). Qed.
Lemma lem521454 (n : nat) : (term45 n) = False.
Proof. exact (EQ_MP (@lem521186 n) (@lem521185 n)). Qed.
Lemma lem521455 (n : nat) : (term102 n) = (True /\ False).
Proof. exact (MK_COMB (@lem521452 n) (@lem521454 n)). Qed.
Lemma lem521457 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521458 : (True /\ False) = False.
Proof. exact (@lem521457 False). Qed.
Lemma lem521459 (n : nat) : (term102 n) = False.
Proof. exact (TRANS (@lem521455 n) (@lem521458)). Qed.
Lemma lem521460 (n : nat) : (0 = (BIT1 n)) = False.
Proof. exact (TRANS (@lem521446 n) (@lem521459 n)). Qed.
Lemma lem521461 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem521462 (n : nat) : (term101 n) = (~ False).
Proof. exact (MK_COMB (@lem521461) (@lem521460 n)). Qed.
Lemma lem521464 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem521465 (n : nat) : (term101 n) = True.
Proof. exact (TRANS (@lem521462 n) (@lem521464)). Qed.
Lemma lem521466 (n : nat) : ((0 = (BIT1 n)) = False) = True.
Proof. exact (TRANS (@lem521441 n) (@lem521465 n)). Qed.
Lemma lem521467 : term104 = term62.
Proof. exact (fun_ext (fun n : nat => @lem521466 n)). Qed.
Lemma lem521468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521469 : term105 = term64.
Proof. exact (MK_COMB (@lem521468) (@lem521467)). Qed.
Lemma lem521471 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521472 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521471 nat t). Qed.
Lemma lem521473 : term64 = True.
Proof. exact (@lem521472 True). Qed.
Lemma lem521474 : term105 = True.
Proof. exact (TRANS (@lem521469) (@lem521473)). Qed.
Lemma lem521475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521476 : term106 = (and True).
Proof. exact (MK_COMB (@lem521475) (@lem521474)). Qed.
Lemma lem521494 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521495 (n : nat) (m : nat) : ((BIT0 m) = (BIT0 n)) = (term107 n m).
Proof. exact (@lem521494 (BIT0 n) (BIT0 m)). Qed.
Lemma lem521499 (m : nat) (n : nat) : (term36 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521174 m n) (@lem521173 m n)). Qed.
Lemma lem521500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521501 (m : nat) (n : nat) : (term108 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem521500) (@lem521499 m n)). Qed.
Lemma lem521503 (m : nat) (n : nat) : (term36 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521174 m n) (@lem521173 m n)). Qed.
Lemma lem521504 (n : nat) (m : nat) : (term36 n m) = (Peano.le n m).
Proof. exact (@lem521503 n m). Qed.
Lemma lem521505 (n : nat) (m : nat) : (term107 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem521501 m n) (@lem521504 n m)). Qed.
Lemma lem521508 (n : nat) (m : nat) : ((BIT0 m) = (BIT0 n)) = (term0 n m).
Proof. exact (TRANS (@lem521495 n m) (@lem521505 n m)). Qed.
Lemma lem521509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem521510 (n : nat) (m : nat) : (term109 m n) = (term60 n m).
Proof. exact (MK_COMB (@lem521509) (@lem521508 n m)). Qed.
Lemma lem521514 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521517 (n : nat) (m : nat) : (((BIT0 m) = (BIT0 n)) = (m = n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem521510 n m) (@lem521514 n m)). Qed.
Lemma lem521519 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem521520 (x : Prop) : (x = x) = True.
Proof. exact (@lem521519 Prop x). Qed.
Lemma lem521521 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem521520 (term0 n m)). Qed.
Lemma lem521522 (m : nat) (n : nat) : (((BIT0 m) = (BIT0 n)) = (m = n)) = True.
Proof. exact (TRANS (@lem521517 n m) (@lem521521 n m)). Qed.
Lemma lem521523 (m : nat) : (term110 m) = term62.
Proof. exact (fun_ext (fun n : nat => @lem521522 m n)). Qed.
Lemma lem521524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521525 (m : nat) : (term111 m) = term64.
Proof. exact (MK_COMB (@lem521524) (@lem521523 m)). Qed.
Lemma lem521527 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521528 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521527 nat t). Qed.
Lemma lem521529 : term64 = True.
Proof. exact (@lem521528 True). Qed.
Lemma lem521530 (m : nat) : (term111 m) = True.
Proof. exact (TRANS (@lem521525 m) (@lem521529)). Qed.
Lemma lem521531 : term112 = term62.
Proof. exact (fun_ext (fun m : nat => @lem521530 m)). Qed.
Lemma lem521532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521533 : term113 = term64.
Proof. exact (MK_COMB (@lem521532) (@lem521531)). Qed.
Lemma lem521535 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521536 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521535 nat t). Qed.
Lemma lem521537 : term64 = True.
Proof. exact (@lem521536 True). Qed.
Lemma lem521538 : term113 = True.
Proof. exact (TRANS (@lem521533) (@lem521537)). Qed.
Lemma lem521539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521540 : term114 = (and True).
Proof. exact (MK_COMB (@lem521539) (@lem521538)). Qed.
Lemma lem521552 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem521553 (m : nat) (n : nat) : (((BIT0 m) = (BIT1 n)) = False) = (term115 m n).
Proof. exact (@lem521552 ((BIT0 m) = (BIT1 n))). Qed.
Lemma lem521557 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521558 (n : nat) (m : nat) : ((BIT0 m) = (BIT1 n)) = (term116 n m).
Proof. exact (@lem521557 (BIT1 n) (BIT0 m)). Qed.
Lemma lem521562 (m : nat) (n : nat) : (term31 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521167 m n) (@lem521166 m n)). Qed.
Lemma lem521563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521564 (m : nat) (n : nat) : (term117 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem521563) (@lem521562 m n)). Qed.
Lemma lem521566 (m : nat) (n : nat) : (term26 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem521160 m n) (@lem521159 m n)). Qed.
Lemma lem521567 (n : nat) (m : nat) : (term26 n m) = (Peano.lt n m).
Proof. exact (@lem521566 n m). Qed.
Lemma lem521568 (n : nat) (m : nat) : (term116 n m) = (term118 n m).
Proof. exact (MK_COMB (@lem521564 m n) (@lem521567 n m)). Qed.
Lemma lem521571 (n : nat) (m : nat) : ((BIT0 m) = (BIT1 n)) = (term118 n m).
Proof. exact (TRANS (@lem521558 n m) (@lem521568 n m)). Qed.
Lemma lem521572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem521573 (n : nat) (m : nat) : (term115 m n) = (term119 n m).
Proof. exact (MK_COMB (@lem521572) (@lem521571 n m)). Qed.
Lemma lem521574 (n : nat) (m : nat) : (((BIT0 m) = (BIT1 n)) = False) = (term119 n m).
Proof. exact (TRANS (@lem521553 m n) (@lem521573 n m)). Qed.
Lemma lem521575 (m : nat) : (term120 m) = (term121 m).
Proof. exact (fun_ext (fun n : nat => @lem521574 n m)). Qed.
Lemma lem521576 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521577 (m : nat) : (term122 m) = (term123 m).
Proof. exact (MK_COMB (@lem521576) (@lem521575 m)). Qed.
Lemma lem521582 : term124 = term125.
Proof. exact (fun_ext (fun m : nat => @lem521577 m)). Qed.
Lemma lem521583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521584 : term126 = term127.
Proof. exact (MK_COMB (@lem521583) (@lem521582)). Qed.
Lemma lem521589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521590 : term128 = term129.
Proof. exact (MK_COMB (@lem521589) (@lem521584)). Qed.
Lemma lem521602 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem521603 (m : nat) (n : nat) : (((BIT1 m) = (BIT0 n)) = False) = (term130 m n).
Proof. exact (@lem521602 ((BIT1 m) = (BIT0 n))). Qed.
Lemma lem521607 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521608 (n : nat) (m : nat) : ((BIT1 m) = (BIT0 n)) = (term131 n m).
Proof. exact (@lem521607 (BIT0 n) (BIT1 m)). Qed.
Lemma lem521612 (m : nat) (n : nat) : (term26 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem521160 m n) (@lem521159 m n)). Qed.
Lemma lem521613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521614 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (MK_COMB (@lem521613) (@lem521612 m n)). Qed.
Lemma lem521616 (m : nat) (n : nat) : (term31 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521167 m n) (@lem521166 m n)). Qed.
Lemma lem521617 (n : nat) (m : nat) : (term31 n m) = (Peano.le n m).
Proof. exact (@lem521616 n m). Qed.
Lemma lem521618 (n : nat) (m : nat) : (term131 n m) = (term134 n m).
Proof. exact (MK_COMB (@lem521614 m n) (@lem521617 n m)). Qed.
Lemma lem521621 (n : nat) (m : nat) : ((BIT1 m) = (BIT0 n)) = (term134 n m).
Proof. exact (TRANS (@lem521608 n m) (@lem521618 n m)). Qed.
Lemma lem521622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem521623 (n : nat) (m : nat) : (term130 m n) = (term135 n m).
Proof. exact (MK_COMB (@lem521622) (@lem521621 n m)). Qed.
Lemma lem521624 (n : nat) (m : nat) : (((BIT1 m) = (BIT0 n)) = False) = (term135 n m).
Proof. exact (TRANS (@lem521603 m n) (@lem521623 n m)). Qed.
Lemma lem521625 (m : nat) : (term136 m) = (term137 m).
Proof. exact (fun_ext (fun n : nat => @lem521624 n m)). Qed.
Lemma lem521626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521627 (m : nat) : (term138 m) = (term139 m).
Proof. exact (MK_COMB (@lem521626) (@lem521625 m)). Qed.
Lemma lem521632 : term140 = term141.
Proof. exact (fun_ext (fun m : nat => @lem521627 m)). Qed.
Lemma lem521633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521634 : term142 = term143.
Proof. exact (MK_COMB (@lem521633) (@lem521632)). Qed.
Lemma lem521639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521640 : term144 = term145.
Proof. exact (MK_COMB (@lem521639) (@lem521634)). Qed.
Lemma lem521656 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521657 (n : nat) (m : nat) : ((BIT1 m) = (BIT1 n)) = (term146 n m).
Proof. exact (@lem521656 (BIT1 n) (BIT1 m)). Qed.
Lemma lem521661 (m : nat) (n : nat) : (term21 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521153 m n) (@lem521152 m n)). Qed.
Lemma lem521662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521663 (m : nat) (n : nat) : (term147 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem521662) (@lem521661 m n)). Qed.
Lemma lem521665 (m : nat) (n : nat) : (term21 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem521153 m n) (@lem521152 m n)). Qed.
Lemma lem521666 (n : nat) (m : nat) : (term21 n m) = (Peano.le n m).
Proof. exact (@lem521665 n m). Qed.
Lemma lem521667 (n : nat) (m : nat) : (term146 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem521663 m n) (@lem521666 n m)). Qed.
Lemma lem521670 (n : nat) (m : nat) : ((BIT1 m) = (BIT1 n)) = (term0 n m).
Proof. exact (TRANS (@lem521657 n m) (@lem521667 n m)). Qed.
Lemma lem521671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem521672 (n : nat) (m : nat) : (term148 m n) = (term60 n m).
Proof. exact (MK_COMB (@lem521671) (@lem521670 n m)). Qed.
Lemma lem521676 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem521204 n m) (@lem521203 m n)). Qed.
Lemma lem521679 (n : nat) (m : nat) : (((BIT1 m) = (BIT1 n)) = (m = n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem521672 n m) (@lem521676 n m)). Qed.
Lemma lem521681 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem521682 (x : Prop) : (x = x) = True.
Proof. exact (@lem521681 Prop x). Qed.
Lemma lem521683 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem521682 (term0 n m)). Qed.
Lemma lem521684 (m : nat) (n : nat) : (((BIT1 m) = (BIT1 n)) = (m = n)) = True.
Proof. exact (TRANS (@lem521679 n m) (@lem521683 n m)). Qed.
Lemma lem521685 (m : nat) : (term149 m) = term62.
Proof. exact (fun_ext (fun n : nat => @lem521684 m n)). Qed.
Lemma lem521686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521687 (m : nat) : (term150 m) = term64.
Proof. exact (MK_COMB (@lem521686) (@lem521685 m)). Qed.
Lemma lem521689 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521690 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521689 nat t). Qed.
Lemma lem521691 : term64 = True.
Proof. exact (@lem521690 True). Qed.
Lemma lem521692 (m : nat) : (term150 m) = True.
Proof. exact (TRANS (@lem521687 m) (@lem521691)). Qed.
Lemma lem521693 : term151 = term62.
Proof. exact (fun_ext (fun m : nat => @lem521692 m)). Qed.
Lemma lem521694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521695 : term152 = term64.
Proof. exact (MK_COMB (@lem521694) (@lem521693)). Qed.
Lemma lem521697 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521698 (t : Prop) : (term66 t) = t.
Proof. exact (@lem521697 nat t). Qed.
Lemma lem521699 : term64 = True.
Proof. exact (@lem521698 True). Qed.
Lemma lem521700 : term152 = True.
Proof. exact (TRANS (@lem521695) (@lem521699)). Qed.
Lemma lem521701 : term153 = term154.
Proof. exact (MK_COMB (@lem521640) (@lem521700)). Qed.
Lemma lem521703 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem521704 : term154 = term143.
Proof. exact (@lem521703 term143). Qed.
Lemma lem521715 : term153 = term143.
Proof. exact (TRANS (@lem521701) (@lem521704)). Qed.
Lemma lem521716 : term155 = term156.
Proof. exact (MK_COMB (@lem521590) (@lem521715)). Qed.
Lemma lem521719 : term157 = term158.
Proof. exact (MK_COMB (@lem521540) (@lem521716)). Qed.
Lemma lem521721 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521722 : term158 = term156.
Proof. exact (@lem521721 term156). Qed.
Lemma lem521745 : term157 = term156.
Proof. exact (TRANS (@lem521719) (@lem521722)). Qed.
Lemma lem521746 : term159 = term158.
Proof. exact (MK_COMB (@lem521476) (@lem521745)). Qed.
Lemma lem521748 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521749 : term158 = term156.
Proof. exact (@lem521748 term156). Qed.
Lemma lem521772 : term159 = term156.
Proof. exact (TRANS (@lem521746) (@lem521749)). Qed.
Lemma lem521773 : term160 = term161.
Proof. exact (MK_COMB (@lem521432) (@lem521772)). Qed.
Lemma lem521776 : term162 = term163.
Proof. exact (MK_COMB (@lem521380) (@lem521773)). Qed.
Lemma lem521778 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521779 : term163 = term161.
Proof. exact (@lem521778 term161). Qed.
Lemma lem521814 : term162 = term161.
Proof. exact (TRANS (@lem521776) (@lem521779)). Qed.
Lemma lem521815 : term164 = term165.
Proof. exact (MK_COMB (@lem521336) (@lem521814)). Qed.
Lemma lem521818 : term166 = term167.
Proof. exact (MK_COMB (@lem521284) (@lem521815)). Qed.
Lemma lem521820 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521821 : term167 = term165.
Proof. exact (@lem521820 term165). Qed.
Lemma lem521868 : term166 = term165.
Proof. exact (TRANS (@lem521818) (@lem521821)). Qed.
Lemma lem521869 : term168 = term167.
Proof. exact (MK_COMB (@lem521272) (@lem521868)). Qed.
Lemma lem521871 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521872 : term167 = term165.
Proof. exact (@lem521871 term165). Qed.
Lemma lem521919 : term168 = term165.
Proof. exact (TRANS (@lem521869) (@lem521872)). Qed.
Lemma lem521920 : term165 = term168.
Proof. exact (SYM (@lem521919)). Qed.
